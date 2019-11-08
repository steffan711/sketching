from collections import OrderedDict
from collections.abc import Iterable
from enum import Enum
from functools import reduce
import logging
import operator
import math
import time
import functools
import operator

import stormpy
import stormpy.core

import jani
from jani.jani_quotient_builder import *
from jani.quotient_container import ThresholdSynthesisResult, Engine
from smt.model_adapter import *
from annotated_property import AnnotatedProperty

logger = logging.getLogger(__name__)


def prod(iterable):
    return functools.reduce(operator.mul, iterable, 1)


class FamilyCheckMethod(Enum):
    """
    Enum to select the type of algorithm to use.
    """
    Lifting = 0,
    SchedulerIteration = 1,
    DtmcIteration = 2,
    AllInOne = 3,
    SMT = 4,
    CEGIS = 5

    @classmethod
    def from_string(cls, input):
        """
        Construct enum from string. 
        
        :param input: either of [lift, cschedenum, onebyone, allinone, smt, cegis]
        :return: the corresponding enum, or None
        """
        if input == "lift":
            return cls.Lifting
        elif input == "cschedenum":
            return cls.SchedulerIteration
        elif input == "onebyone":
            return cls.DtmcIteration
        elif input == "allinone":
            return cls.AllInOne
        elif input == "smt":
            return cls.SMT
        elif input == "cegis":
            return cls.CEGIS
        else:
            return None

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


def open_constants(model):
    return OrderedDict([(c.name, c) for c in model.constants if not c.defined])


class HoleOptions(OrderedDict):
    def __str__(self):
        return "HoleOptions{" + ",".join(
            ["{}: [{}]".format(k, ",".join(str(x) for x in v)) for k, v in self.items()]) + "}"

    def size(self):
        def prod(iterable):
            return reduce(operator.mul, iterable, 1)

        return prod([len(v) for v in self.values()])

    def index_map(self, sub_options):
        result = OrderedDict()
        for k,values in sub_options.items():
            result[k] = []
            for v in values:
                for index, ref in enumerate(self.get(k)):
                    if ref == v:
                        result[k].append(index)
        return result


class RoundStats:
    def __init__(self, round, queued, above, below, time):
        self.round = round
        self.queued = queued
        self.cumulative_above = above
        self.cumulative_below = below
        self.cumulative_time = time


class FamilyChecker:
    def __init__(self, check_prerequisites=False, engine = Engine.Sparse):
        self._check_prereq = check_prerequisites
        self.expression_manager = None
        self.holes = None
        self.hole_options = None
        self.sketch = None
        self.symmetries = None
        self.differents = None
        self.properties = None

        self.qualitative_properties = None
        self._engine = engine
        # keyword that is written to stats files to help restore stats correctly.
        self.stats_keyword = "genericfamilychecker-stats"

    def _load_properties_from_file(self, program, path, constant_str=""):
        """
        Loads a list with properties from a file. 

        :param path: File path 
        :param constant_str: Constants to substitute
        :return: None. Properties are now loaded.
        """
        logger.debug("Load properties from file.")
        properties = []
        with open(path) as file:
            for line in file:
                line = line.rstrip()
                if not line or line == "":
                    continue
                if line.startswith("//"):
                    continue
                properties.append(line)
        self._load_properties(program, properties, constant_str)

    def _load_properties(self, program, properties, constant_str=""):
        """
        Load properties to be checked via model checking

        :param properties:
        :return:
        """
        logger.debug("Load properties")
        self.properties = []
        self.qualitative_properties = []

        for p in properties:
            # prop = self._load_property_for_sketch(p, constant_str)[0]
            for prop in stormpy.parse_properties_for_prism_program(p, program):
                # prop = prp.property
                assert prop.raw_formula.has_bound
                # print(prop.raw_formula)

                if True:  # prop.raw_formula.is_probability_operator and prop.raw_formula.threshold > 0 and prop.raw_formula.threshold < 1:
                    self.properties.append(prop)
        _constants_map = self._constants_map(constant_str, program)


    def _parse_template_defs(self, location):
        definitions = OrderedDict()
        with open(location) as file:
            for line in file:
                line = line.rstrip()
                if not line or line == "":
                    continue
                if line.startswith("#"):
                    continue

                entries = line.strip().split(";")
                definitions[entries[0]] = entries[1:]
        return definitions

    def _register_unconstrained_design_space(self, size):
        logger.info("Design space (without constraints): {}".format(size))


    def load_template_definitions(self, location):
        """
        Load template definitions containing the possible values for the holes

        :param location:
        :return:
        """
        self.hole_options = HoleOptions()
        definitions = self._parse_template_defs(location)

        constants_map = dict()
        ordered_holes = list(self.holes.keys())
        for k in ordered_holes:

            v = definitions[k]

            ep = stormpy.storage.ExpressionParser(self.expression_manager)
            ep.set_identifier_mapping(dict())
            if len(v) == 1:

                constants_map[self.holes[k].expression_variable] = ep.parse(v[0])

                del self.holes[k]
            else:
                self.hole_options[k] = [ep.parse(x) for x in v]

        # Eliminate holes with just a single option.
        self.sketch = self.sketch.define_constants(constants_map).substitute_constants()
        assert self.hole_options.keys() == self.holes.keys()

        logger.debug("Template variables: {}".format(self.hole_options))
        self._register_unconstrained_design_space(prod([len(v) for v in self.hole_options.values()]))


    def _constants_map(self, constant_str, program):
        logger.debug("Load constants '{}'".format(constant_str))
        if constant_str.rstrip() == "":
            return dict()
        constants_map = dict()
        kvs = constant_str.split(",")
        ep = stormpy.storage.ExpressionParser(self.expression_manager)
        ep.set_identifier_mapping(dict())

        holes = dict()
        for c in program.constants:
            holes[c.name] = c

        for kv in kvs:
            key_value = kv.split("=")
            if len(key_value) != 2:
                raise ValueError("Expected Key-Value pair, got '{}'.".format(kv))

            expr = ep.parse(key_value[1])
            constants_map[holes[key_value[0]].expression_variable] = expr
        return constants_map

    def _find_holes(self):
        """
        Find holes in the sketch.

        :return:
        """
        logger.debug("Search for holes in sketch...")
        self.holes = OrderedDict()
        for c in self.sketch.constants:
            if not c.defined:
                self.holes[c.name] = c

        logger.debug("Holes found: {}".format(list(self.holes.keys())))

    def _annotate_properties(self, constant_str):
        _constants_map = self._constants_map(constant_str, self.sketch)
        self.properties = [AnnotatedProperty(stormpy.Property("property-{}".format(i),
                                                              p.raw_formula.clone().substitute(_constants_map)),
                                             self.sketch,
                                             add_prerequisites=self._check_prereq
                                             ) for i, p in
                           enumerate(self.properties)]


    def _set_constants(self, constant_str):
        constants_map = self._constants_map(constant_str, self.sketch)
        self.sketch = self.sketch.define_constants(constants_map)

    def load_sketch(self, path, property_path, constant_str=""):
        logger.info("Load sketch from {}  with constants {}".format(path, constant_str))

        prism_program = stormpy.parse_prism_program(path)
        self.expression_manager = prism_program.expression_manager
        self._load_properties_from_file(prism_program, property_path, constant_str)
        self.sketch, self.properties = prism_program.to_jani(self.properties)
        self._set_constants(constant_str)
        self._find_holes()
        self._annotate_properties(constant_str)

        assert self.expression_manager == self.sketch.expression_manager

    def load_restrictions(self, location):
        logger.debug("Load restrictions")
        mode = "none"
        symmetries = list()
        differents = list()
        with open(location) as file:
            for line in file:
                line = line.rstrip()
                if not line or line == "":
                    continue
                if line.startswith("#"):
                    continue
                if line.startswith("!symmetries"):
                    mode = "symmetries"
                    continue
                if line.startswith("!different"):
                    mode = "different"
                    continue
                if mode == "symmetries":
                    entries = line.strip().split(";")
                    for e in entries:
                        symmetries.append(e.strip().split(","))
                if mode == "different":
                    entries = line.strip().split(";")
                    for e in entries:
                        if e == "":
                            continue
                        differents.append(e.strip().split(","))
                else:
                    raise RuntimeError("Restriction file does not set appropriate mode")
        for symmetry in symmetries:
            for hole_name in symmetry:
                if hole_name not in self.holes:
                    raise ValueError("Key {} not in template, but in list of symmetries".format(hole_name))
        for different in differents:
            for hole_name in different:
                if hole_name not in self.holes:
                    raise ValueError("Key {} not in template, but in list of differents".format(hole_name))
        self.symmetries = symmetries
        self.differents = differents

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


    def holes_as_string(self):
        return ",".join([name for name in self.holes])

    def initialise(self):
        pass

    def print_stats(self):
        pass

    def store_in_statistics(self):
        return []

class LiftingBasedFamilyChecker(FamilyChecker):
    def __init__(self, *args):
        super().__init__(*args)
        self.mc_formulae = None
        self.mc_formulae_alt = None
        self.jani_quotient_builder = None
        self.thresholds = []

    def initialise(self):
        self.mc_formulae = []
        self.mc_formulae_alt = []
        for p in self.properties:
            formula = p.raw_formula.clone()
            comparison_type = formula.comparison_type
            self.thresholds.append(formula.threshold)
            formula.remove_bound()
            alt_formula = formula.clone()
            if comparison_type in [stormpy.ComparisonType.LESS, stormpy.ComparisonType.LEQ]:
                formula.set_optimality_type(stormpy.OptimizationDirection.Minimize)
                alt_formula.set_optimality_type(stormpy.OptimizationDirection.Maximize)
            else:
                assert comparison_type in [stormpy.ComparisonType.GREATER, stormpy.ComparisonType.GEQ]
                formula.set_optimality_type(stormpy.OptimizationDirection.Maximize)
                alt_formula.set_optimality_type(stormpy.OptimizationDirection.Minimize)
            self.mc_formulae.append(formula)
            self.mc_formulae_alt.append(alt_formula)

    def _analyse_from_scratch(self, _open_constants, holes_options, all_in_one_constants, threshold):
        remember = set()#set(_open_constants)#set()
        jani_abstraction_result = self.jani_quotient_builder.construct(holes_options, remember, all_in_one_constants)
        index = 0 #TODO allow setting another index.
        logger.info("Run analysis of property with index {}".format(index))
        jani_abstraction_result.prepare(self.mc_formulae, self.mc_formulae_alt, self._engine)
        jani_abstraction_result.analyse(threshold, index, self._engine)
        return jani_abstraction_result

    def _analyse_suboptions(self, oracle, suboptions, threshold):
        indexed_suboptions = self.hole_options.index_map(suboptions)
        oracle.consider_subset(suboptions, indexed_suboptions)
        index = 0
        oracle.analyse(threshold, index)
        return oracle

class LiftingChecker(LiftingBasedFamilyChecker):
    """
    
    """

    def run(self):
        """
        
        :return: 
        """
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        threshold_synthesis = True

        self._open_constants = self.holes

        options_above = []
        nr_options_above = 0
        options_below = []
        nr_options_below = 0
        oracle = None
        iterations = 0

        hole_options = [self.hole_options]
        total_nr_options = self.hole_options.size()
        logger.info("Total number of options: {}".format(total_nr_options))
        hole_options_next_round = []
        threshold = float(self.thresholds[0]) if threshold_synthesis else math.inf
        logger.debug("Threshold is {}".format(threshold))
        optimal_hole_options = None
        self.use_oracle = True
        while True:
            iterations += 1
            logger.info("Start with iteration {} (queue length: {} + {}).".format(iterations, len(hole_options),
                                                                                  len(hole_options_next_round)))
            # logger.debug("In queue: {} (elements: {})".format(len(hole_options) + len(hole_options_next_round), sum([o.size() for o in hole_options + hole_options_next_round])))
            # ssert sum([o.size() for o in hole_options + hole_options_next_round]) + nr_options_above + nr_options_below + (1 if optimal_hole_options is not None else 0) == total_nr_options, "{} + {} + {} vs {}".format(sum([o.size() for o in hole_options + hole_options_next_round]), nr_options_above, 1 if optimal_hole_options is not None else 0, total_nr_options)
            if oracle is None:
                oracle = self._analyse_from_scratch(self._open_constants, hole_options[0], set(), threshold)
            else:
                self._analyse_suboptions(oracle, hole_options[0], threshold)
            # TODO select right threshold.
            threshold_synthesis_result = oracle.decided(threshold)
            if threshold_synthesis_result == jani.quotient_container.ThresholdSynthesisResult.UNDECIDED:
                logger.debug("Undecided.")

                if threshold_synthesis:
                    if hole_options[0].size() > 2:
                        oracle.scheduler_color_analysis()
                        hole_options_next_round += self._split_hole_options(hole_options[0], oracle)
                    else:
                        hole_options_next_round += self._split_hole_options(hole_options[0], None)
                else:
                    oracle.scheduler_color_analysis()
                    if oracle.is_lower_bound_tight():
                        logger.debug("Found a tight lower bound.")
                        threshold = oracle.lower_bound()
                        logger.info("current threshold {}".format(threshold))
                        nr_options_above += 1 if optimal_hole_options is not None else 0
                        optimal_hole_options = hole_options[0]
                        nr_options_above += hole_options[0].size() - 1
                        hole_options = hole_options[1:]
                    else:
                        hole_options = self._split_hole_options(hole_options[0], oracle) + hole_options[1:]
            else:
                if threshold_synthesis_result == jani.quotient_container.ThresholdSynthesisResult.ABOVE:
                    logger.debug("All above.")
                    if threshold_synthesis:
                        options_above.append(hole_options[0])
                        nr_options_above += hole_options[0].size()
                    else:
                        options_above.append(hole_options[0])
                        nr_options_above += hole_options[0].size()
                        hole_options = hole_options[1:]

                else:
                    logger.debug("All below.")

                    if threshold_synthesis:
                        options_below.append(hole_options[0])
                        nr_options_below += hole_options[0].size()
                    else:
                        oracle.scheduler_color_analysis()
                        if oracle.is_lower_bound_tight():
                            logger.debug("Found a tight lower bound.")
                            threshold = oracle.lower_bound()
                            nr_options_above += 1 if optimal_hole_options is not None else 0
                            nr_options_above += hole_options[0].size() - 1
                            optimal_hole_options = hole_options[0]
                            hole_options = hole_options[1:]
                        else:
                            nr_options_above += 1 if optimal_hole_options is not None else 0
                            threshold = oracle.upper_bound()
                            optimal_hole_options = None
                            hole_options = self._split_hole_options(hole_options[0], oracle) + hole_options[1:]
                        logger.info("current threshold {}".format(threshold))

            remaining = total_nr_options - nr_options_above - nr_options_below
            logger.info("Number options above {} (in {} regions) and below {} (in {} regions). Remaining: {}".format(
                nr_options_above, len(options_above), nr_options_below, len(options_below), remaining))
            logger.info("Singleton regions {}".format(oracle.dtmcs_checked))
            logger.info("Critical timings so far: {} building, {} checking {} analysis.".format(oracle._build_time,
                                                                                                oracle._mc_time,
                                                                                                oracle._sched_ana_time))
            if threshold_synthesis:
                hole_options = hole_options[1:]
            if len(hole_options) == 0:
                if len(hole_options_next_round) == 0:
                    break
                logger.info("Next round...")
                if len(hole_options_next_round) * 8 > remaining:
                    self.use_oracle = False
                hole_options = hole_options_next_round
                hole_options_next_round = []

            if threshold_synthesis:
                # DO SOMETHING WITH RESULT
                pass
            else:
                logger.info("Optimal value at {} with {}".format(threshold, optimal_hole_options))

                #print("[" + ",".join([str(x) for x in hole_options]) + "]")

    def _split_hole_options(self, hole_options, oracle):

        def split_list(a_list):
            half = len(a_list) // 2
            return a_list[:half], a_list[half:]

        # Where to split.
        splitters = []
        selected_splitter = None
        one_side_list = None
        other_side_list = None

        if oracle is not None and self.use_oracle:
            selected_splitter, one_side_list, other_side_list = oracle.propose_split()
            logger.debug("Oracle proposes a split at {}".format(selected_splitter))


        if not isinstance(one_side_list, Iterable):
            one_side_list = [one_side_list]
        if not isinstance(other_side_list, Iterable):
            other_side_list = [other_side_list]

        logger.debug("Presplit {} vs. {}".format(one_side_list, other_side_list))
        #logger.debug(other_side_list)

        if selected_splitter is None:
            # Split longest.
            maxlength = 0
            for k, v in hole_options.items():
                maxlength = max(maxlength, len(v))
                if len(v) == maxlength:
                    selected_splitter = k

            if maxlength == 1:
                return []
        for k, v in hole_options.items():
            if k == selected_splitter:
                logger.debug("Splitting {}...".format(v))
                assert len(v) > 1, "Cannot split along {}".format(k)

                one_vals = [ self.hole_options[k][one_side] for one_side in one_side_list if one_side is not None]
                other_vals = [ self.hole_options[k][other_side] for other_side in other_side_list if other_side is not None]
                logger.debug("Pre-splitted {} and {}".format(one_vals, other_vals))
                new_v = [x for x in v if x not in one_vals + other_vals]
                logger.debug("Now distribute {}".format(new_v))
                second, first = split_list(new_v)
                #if one_side is not None:
                first = first + one_vals
                #if other_side is not None:
                second = second + other_vals
                splitters.append([k, first, second])

                logger.info("Splitting {} into {} and {}".format(k, "[" + ",".join([str(x) for x in first]) + "]",
                                                                 "[" + ",".join([str(x) for x in second]) + "]"))
                break

        # Split.
        assert len(splitters) == 1
        split_queue = [hole_options]
        for splitter in splitters:
            new_split_queue = []
            for options in split_queue:
                new_split_queue.append(HoleOptions(options))
                new_split_queue[-1][splitter[0]] = splitter[1]
                new_split_queue.append(HoleOptions(options))
                new_split_queue[-1][splitter[0]] = splitter[2]
            split_queue = new_split_queue
        assert len(split_queue) == 2
        return split_queue


class AllInOneChecker(LiftingBasedFamilyChecker):
    """
    
    """

    def run(self):
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes
        logger.info("Total number of options: {}".format(self.hole_options.size()))

        _ = self._analyse_from_scratch(self._open_constants, self.hole_options, self._open_constants.keys(), 0)


class OneByOneChecker(LiftingBasedFamilyChecker):
    """
    
    TODO: strictly, this class is not based on lifting (but the code depends on mc_formulae for historical reasons
    """


    def run(self):
        jani_program = self.sketch
        iteration = 0
        iter_start = time.time()
        model_states_cum = 0
        model_transitions_cum = 0
        total_nr_options = self.hole_options.size()
        for constant_assignment in itertools.product(*self.hole_options.values()):
            iteration += 1
            logger.info("Iteration: {} / {}".format(iteration, total_nr_options))
            constants = [jani_program.get_constant(c).expression_variable for c in self.hole_options.keys()]
            substitution = dict(zip(constants, constant_assignment))
            # print(substitution)
            instance = jani_program.define_constants(substitution)
            mh = ModelHandling()

            mh.build_model(instance, self.mc_formulae, self.mc_formulae_alt)
            model_states_cum += mh.full_mdp.nr_states
            model_transitions_cum += mh.full_mdp.nr_transitions
            index = 0
            mh.mc_model(index)

            logger.info("Ran for {}, expect total: {}".format(time.time() - iter_start, (
                time.time() - iter_start) * total_nr_options / iteration))
            logger.info("Avg model size {} states, {} transition".format(model_states_cum, model_transitions_cum))


class ConsistentSchedChecker(LiftingBasedFamilyChecker):
    """
    Enumerate over all schedulers.
    
    Supports (only) threshold synthesis as of now. 
    """
    def run(self):
        prep_start = time.time()
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes

        iterations = 0

        total_nr_options = self.hole_options.size()
        logger.info("Total number of options: {}".format(total_nr_options))
        oracle = self.jani_quotient_builder.construct(self.hole_options, set(), set())
        oracle.prepare(self.mc_formulae, self.mc_formulae_alt)
        oracle.get_full_colors()
        prep_end = time.time()
        prep_time = prep_end - prep_start

        total_states = 0
        total_transitions = 0

        iter_start = time.time()
        for selected_hole_option_dict in itertools.product(*self.hole_options.values()):
            selected_hole_option = HoleOptions(
                [(x, [y]) for x, y in zip(self.hole_options.keys(), selected_hole_option_dict)])
            iterations += 1
            logger.info("Start with iteration {}.".format(iterations))
            self._analyse_suboptions(oracle, selected_hole_option, 0)
            #TODO The result should be stored somehow.
            logger.info("Ran for {}, expect total: {}".format(prep_time + time.time() - iter_start, prep_time + (
            time.time() - iter_start) * total_nr_options / iterations))
            total_states += oracle._mdp_handling.mdp.nr_states
            total_transitions += oracle._mdp_handling.mdp.nr_transitions
            logger.info("Average states so far {}.  Average transitions so far {}".format(total_states/iterations, total_transitions/iterations))


class SmtChecker(LiftingBasedFamilyChecker):
    def run(self):
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        threshold_synthesis = True

        jani_program = self.sketch

        self._open_constants = self.holes
        properties = self.properties
        oracle = self.jani_quotient_builder.construct(self.hole_options, set(), set())
        oracle.prepare(self.mc_formulae, self.mc_formulae_alt)

        solver = SmtConsistentSchedulerSolver()
        model = oracle._mdp_handling.full_mdp
        formula = self.mc_formulae[0]
        assert type(formula) in [stormpy.logic.ProbabilityOperator, stormpy.RewardOperator]
        path_formula = formula.subformula
        if type(path_formula) == stormpy.logic.EventuallyFormula:
            phi_formula = stormpy.logic.BooleanLiteralFormula(True)
            psi_formula = path_formula.subformula
        elif type(path_formula) == stormpy.logic.UntilFormula:
            phi_formula = path_formula.left_subformula
            psi_formula = path_formula.right_subformula
        else:
            raise ValueError("Property type not supported")
        phi_result = stormpy.model_checking(model, phi_formula)
        phi_states = phi_result.get_truth_values()
        psi_result = stormpy.model_checking(model, psi_formula)
        psi_states = psi_result.get_truth_values()
        solver.initialize(oracle._mdp_handling.full_mdp, oracle.get_full_colors(), self.hole_options,
                          self.mc_formulae[0].reward_name if self.mc_formulae[0].is_reward_operator else None,
                          phi_states, psi_states, self.properties[0].raw_formula.threshold,
                          self.properties[0].raw_formula.comparison_type)
