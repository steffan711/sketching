import logging
import time
from collections import OrderedDict
import concurrent.futures as conc
import threading

import stormpy
import stormpy.utility

import cegis.stats
from family_checkers.familychecker import FamilyChecker
from cegis.verifier import Verifier

from z3 import *

logger = logging.getLogger(__name__)


class OptimalitySetting:
    def __init__(self, criterion, direction, epsilon):
        self._criterion = criterion
        assert direction in ["min","max"]
        self._direction = direction
        self._eps = epsilon

    @property
    def criterion(self):
        return self._criterion

    def is_improvement(self, mc_result, best_so_far):
        if best_so_far is None:
            return True
        if self._direction == "min":
            return mc_result < best_so_far
        if self._direction == "max":
            return mc_result > best_so_far

    def get_violation_property(self, best_so_far, bound_translator):
        vp = stormpy.Property("optimality_violation", self._criterion.raw_formula.clone(),
                         "Optimality criterion with adapted bound")
        if self._direction == "min":
            bound = best_so_far - best_so_far * self._eps
            ct = stormpy.logic.ComparisonType.LESS
        else:
            bound = best_so_far + best_so_far * self._eps
            ct = stormpy.logic.ComparisonType.GREATER
        bound = bound_translator(bound)
        vp.raw_formula.set_bound(ct, bound)
        return vp


class Synthesiser(FamilyChecker):
    """
    Class that constructs new candidates to be verified.
    """
    def __init__(self, check_prerequisites=False, threads=1, add_cuts=True):
        super().__init__(check_prerequisites)
        self.template_metavariables = OrderedDict()
        self.learned_clauses = []
        self.stats = cegis.stats.SynthetiserStats()
        self._label_renaming = None
        self.result = None
        self._add_cuts = add_cuts
        self._verifier = Verifier()
        self._smtlock = threading.Lock()
        self._optimality_setting = None
        self.tasks = threads
        self._executor = conc.ThreadPoolExecutor(max_workers=self.tasks)
        self.stats_keyword = "cegis-stats"
        self._all_conflicts = True

    @property
    def verifier_stats(self):
        return self._verifier.stats

    def load_optimality(self, path):
        logger.debug("Loading optimality info.")
        direction = None
        epsilon = None
        with open(path) as file:
            for line in file:
                if line.startswith("//"):
                    continue
                if line.rstrip() == "min":
                    direction = "min"
                elif line.rstrip() == "max":
                    direction = "max"
                elif line.startswith("relative"):
                    epsilon = float(line.split()[1])
                else:
                    optimality_criterion = self._load_property_for_sketch(line)[0]
        logger.debug("Done parsing optimality file.")
        if not direction:
            raise ValueError("direction not set")
        if not epsilon:
            raise ValueError("epsilon not set")
        if not optimality_criterion:
            raise ValueError("optimality criterion not set")

        self._optimality_setting = OptimalitySetting(optimality_criterion, direction, epsilon)

    def _register_unconstrained_design_space(self, size):
        self.stats.design_space_size = size
        logger.info("Design space (without constraints): {}".format(self.stats.design_space_size))

    def initialise(self):
        self._initialize_solver()
        self._initialise_verifier()

    def run(self):
        """
        Run the main loop of the synthesiser.

        :return:
        """
        synt_time = time.time()
        futures = set()

        def make_callback(assignments, sat_model):
            return lambda fut: self._process_verifier_result(sat_model, assignments, fut.result()[0], fut.result()[1])

        while True:
            self.stats.iterations += 1
            logger.debug("Iteration: {} acquire lock..".format(self.stats.iterations))
            self._smtlock.acquire()
            logger.debug("Iteration: {} sat-solving..".format(self.stats.iterations))
            solver_time = time.time()
            # Is there one more possible assignment?
            solver_result = self.solver.check()
            solver_time = time.time() - solver_time
            self.stats.solver_times.append(solver_time)
            if solver_result != sat:
                self._smtlock.release()
                logger.debug("No further instances to explore.")
                break
            logger.debug("Iteration: {} obtain model..".format(self.stats.iterations))

            # Get the model for the instance that the SAT solver encountered.
            sat_model = self.solver.model()
            self._smtlock.release()

            # If we run several tasks in parallel, ensure that no further model is going to work on this particular instance.
            if self.tasks > 1:
                self._exclude_sat_model(sat_model, [self.holes])

            logger.debug("Iteration: {} instantiating..".format(self.stats.iterations))
            # Create an assignment for the holes ..
            hole_assignments = self._sat_model_to_constants_assignment(sat_model)
            # and construct ..
            instance = self.build_instance(hole_assignments)

            logger.debug("Iteration: {} dispatching ..".format(self.stats.iterations))

            # Execute the verifier in another thread.
            future = self._executor.submit(self._verifier.run, instance, self._all_conflicts)
            future._cb = make_callback(hole_assignments, sat_model)
            futures.add(future)
            logger.debug("Currently running: {}".format(len(futures)))
            if len(futures) >= self.tasks:
                logger.debug("Waiting for one task to finish")
                done, futures = conc.wait(futures, return_when=conc.FIRST_COMPLETED)
                logger.debug("Task finished... postprocessing...")
                for d in done:
                    d._cb(d)
                logger.debug("Done postprocessing")
            else:
                for f in futures:
                    if f.done():
                        f._cb(f)

            if self.result and not self._optimality_setting:
                # We have found a solution and do not look for the optimal.
                break

        self.stats.total_time = time.time() - synt_time
        conc.wait(futures)
        return True if self.result is not None else False, self.result

    def build_instance(self, assignments):
        """
        From the sketch and the assignment for the holes, build a concrete instance

        :param assignments:
        :return:
        """
        logger.info(
            "Consider hole assignment: {}".format(",".join("{}={}".format(k, v) for k, v in assignments.items())))
        constants_map = dict()
        ep = stormpy.storage.ExpressionParser(self.expression_manager)
        ep.set_identifier_mapping(dict())
        for hole_name, expr in assignments.items():
            constants_map[self.holes[hole_name].expression_variable] = expr
        logger.debug("construct instance")
        instance = self.sketch.define_constants(constants_map).substitute_constants()
        logger.debug("constructed instance")
        return instance

    def _compute_dont_care_set(self):
        dont_care_set = stormpy.core.FlatSet()

        if self.is_jani():
            for automaton in self.sketch.automata:
                automaton_index = self.sketch.get_automaton_index(automaton.name)
                for edge_index, e in enumerate(automaton.edges):
                    dont_care = not e.guard.contains_variable(set([c.expression_variable for c in self.holes.values()]))
                    if dont_care:
                        for dest in e.destinations:
                            for assignment in dest.assignments:
                                if assignment.expression.contains_variable(
                                        set([c.expression_variable for c in self.holes.values()])):
                                    dont_care = False
                                    continue

                    if dont_care:
                        automaton_edge_index = stormpy.JaniModel.encode_automaton_and_edge_index(automaton_index,
                                                                                                 edge_index)
                        dont_care_set.insert(automaton_edge_index)


        else:
            logger.warning("Dont care sets for prism are not supported")
        return dont_care_set

    def _initialize_solver(self):
        self.solver = Solver()
        variables = dict()
        for k, v in self.hole_options.items():
            # Create Integer Variable
            var = Int(k)
            # Store the variable.
            self.template_metavariables[var] = k
            variables[k] = var
            # Add constraints for the number of actions.
            self.solver.add(var >= 0)
            self.solver.add(var < len(v))

        for sym in self.symmetries:
            for x, y in zip(sym, sym[1:]):
                self.solver.add(variables[x] < variables[y])

        for sym in self.differents:
            for id, x in enumerate(sym):
                for y in sym[id + 1:]:
                    logger.debug("{} != {}".format(x, y))
                    self.solver.add(variables[x] != variables[y])

    def _initialise_verifier(self):
        dont_care_set = self._compute_dont_care_set()
        self._verifier.initialise(self.sketch, self.properties, self.qualitative_properties, dont_care_set,
                                  self._add_cuts)
        self._verifier.initialise_stats(self.holes)
        self._verifier.initialise_optimality(self._optimality_setting)

    def is_jani(self):
        return type(self.sketch) == stormpy.storage.JaniModel

    def _process_verifier_result(self, sat_model_map, assignments, qualitative, conflicts):
        if qualitative:
            conflicts.add(tuple(self.holes.keys()))
            self.stats.qualitative_iterations += 1
        if len(conflicts) == 0:
            self.result = assignments
        else:
            for conflict in conflicts:
                if len(conflict) < len(self.template_metavariables):
                    self.stats.non_trivial_cex += 1
                print(conflicts)
            logger.info("Found conflicts involving {}".format(conflicts))
            self._exclude_sat_model(sat_model_map, conflicts)

    def _count_remaining_models(self):
        """
        How many more models are there?
        Warning; This operation is expensive as it counts explicitly. For future, consider model counting. 

        :return: 
        """
        self.solver.push()
        i = 0
        print("Counting remaining models....")
        while self.solver.check() == sat:
            sat_model = self.solver.model()
            clause = Not(And([var == sat_model[var] for var, hole in self.template_metavariables.items()]))
            self.solver.add(clause)
            i += 1
            if i % 1000 == 0:
                print(i)
        print("Remaining models: {}".format(i))
        self.solver.pop()

    def _sat_model_to_constants_assignment(self, sat_model):
        hole_assignments = OrderedDict()
        for var, hole in self.template_metavariables.items():
            val = sat_model[var].as_long()
            hole_assignments[hole] = self.hole_options[hole][val]
        return hole_assignments

    def _exclude_sat_model(self, sat_model, conflicts):
        """

        :param sat_model: 
        :param conflicts: 
        :return: 
        """
        for conflict in conflicts:
            clause = Not(
                And([var == sat_model[var] for var, hole in self.template_metavariables.items() if hole in conflict]))
            logger.info("learned clause: {}".format(clause))
            if len(conflict) != len(self.template_metavariables):
                self.learned_clauses.append(clause)
            self._smtlock.acquire()
            clause_add_time = time.time()
            self.solver.add(clause)
            clause_add_time = time.time() - clause_add_time
            self.stats.clause_adding_times.append(clause_add_time)
            self._smtlock.release()
            logger.debug("added clause!")

    def print_stats(self):
        print("Iterations: {} ({} s), Qualitative Iterations {}/{}".format(self.stats.iterations,
                                                                           self.stats.total_time,
                                                                           self.stats.qualitative_iterations,
                                                                           self.stats.iterations))
        print("Non-trivial counterexamples: {}".format(self.stats.non_trivial_cex))
        print("Model Building Calls: {} ({} s)".format(self.verifier_stats.model_building_calls,
                                                       self.verifier_stats.model_building_time))
        print("Synthethiser Analysis: {} = {} + {} s".format(self.stats.total_solver_time,
                                                             self.stats.total_solver_analysis_time,
                                                             self.stats.total_solver_clause_adding_time))
        print("Conflict analyses Calls: {} ({} s)".format(self.verifier_stats.conflict_analysis_calls,
                                                          self.verifier_stats.conflict_analysis_time))
        print("Qualitative Model Checking Calls: {} ({} s)".format(
            self.verifier_stats.qualitative_model_checking_calls,
            self.verifier_stats.qualitative_model_checking_time))
        print("Quantitative Model Checking Calls: {} ({} s)".format(
            self.verifier_stats.quantitative_model_checking_calls,
            self.verifier_stats.quantitative_model_checking_time))

        print("CA/Iterations: {}".format(self.verifier_stats.total_conflict_analysis_iterations))
        print("CA/SMT solving: {} s".format(self.verifier_stats.total_conflict_analysis_solver_time))
        print("CA/Analysis: {} s".format(self.verifier_stats.total_conflict_analysis_analysis_time))
        print("CA/MC: {} s".format(self.verifier_stats.total_conflict_analysis_mc_time))
        print("CA/Setup: {} s".format(self.verifier_stats.total_conflict_analysis_setup_time))
        print("CA/Cuts: {} s".format(self.verifier_stats.total_conflict_analysis_cut_time))

        # print("Learned clauses: {}".format(",".join([str(c) for c in self.stats.learned_clauses])))
        # print(self.sketch)

        self.verifier_stats.print_property_stats()

    def store_in_statistics(self):
        return [self.stats, self.verifier_stats]