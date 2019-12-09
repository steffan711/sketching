from collections.abc import Iterable

import stormpy
import stormpy.core

import dynasty.jani
from dynasty.jani.jani_quotient_builder import *
from dynasty.jani.quotient_container import ThresholdSynthesisResult as ThresholdSynthesisResult
from dynasty.jani.quotient_container import Engine as Engine
from dynasty.smt.model_adapter import *
from dynasty.annotated_property import AnnotatedProperty

from dynasty.family_checkers.familychecker import FamilyChecker, HoleOptions

class QuotientBasedFamilyChecker(FamilyChecker):
    def __init__(self, *args):
        super().__init__(*args)
        self.mc_formulae = None
        self.mc_formulae_alt = None
        self.jani_quotient_builder = None
        self.thresholds = []
        self._accept_if_above = []

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
                accept_if_above = False
            else:
                assert comparison_type in [stormpy.ComparisonType.GREATER, stormpy.ComparisonType.GEQ]
                formula.set_optimality_type(stormpy.OptimizationDirection.Maximize)
                alt_formula.set_optimality_type(stormpy.OptimizationDirection.Minimize)
                accept_if_above = True
            self.mc_formulae.append(formula)
            self.mc_formulae_alt.append(alt_formula)
            self._accept_if_above.append(accept_if_above)

    def _analyse_from_scratch(self, _open_constants, holes_options, all_in_one_constants, threshold):
        remember = set()  # set(_open_constants)#set()
        jani_abstraction_result = self.jani_quotient_builder.construct(holes_options, remember, all_in_one_constants)
        index = 0  # TODO allow setting another index.
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





class LiftingChecker(QuotientBasedFamilyChecker):
    """

    """

    def run_feasibility(self):
        if self.input_has_multiple_properties():
            raise RuntimeError("Lifting is only implemented for single properties")

        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        threshold_synthesis = True

        self._open_constants = self.holes

        oracle = None
        iterations = 0

        hole_options = [self.hole_options]
        total_nr_options = self.hole_options.size()
        nr_options_remaining = total_nr_options
        logger.info("Total number of options: {}".format(total_nr_options))
        hole_options_next_round = []
        threshold = float(self.thresholds[0])
        logger.debug("Threshold is {}".format(threshold))
        self.use_oracle = True
        while True:
            iterations += 1
            logger.info("Start with iteration {} (queue length: {} + {}).".format(iterations, len(hole_options),
                                                                                  len(hole_options_next_round)))
            if oracle is None:
                oracle = self._analyse_from_scratch(self._open_constants, hole_options[0], set(), threshold)
            else:
                self._analyse_suboptions(oracle, hole_options[0], threshold)
            # TODO select right threshold.
            threshold_synthesis_result = oracle.decided(threshold)
            print(type(hole_options[0]))
            if threshold_synthesis_result == dynasty.jani.quotient_container.ThresholdSynthesisResult.UNDECIDED:
                logger.debug("Undecided.")
                oracle.scheduler_color_analysis()
                hole_options = self._split_hole_options(hole_options[0], oracle) + hole_options[1:]
            else:
                if threshold_synthesis_result == ThresholdSynthesisResult.ABOVE:
                    logger.debug("All above.")
                    if self._accept_if_above[0]:
                        return True, hole_options[0].pick_one_in_family()
                    else:
                        nr_options_remaining -= hole_options[0].size()
                        hole_options = hole_options[1:]
                else:
                    logger.debug("All below.")
                    if not self._accept_if_above[0]:
                        return True, hole_options[0].pick_one_in_family()
                    else:
                        nr_options_remaining -= hole_options[0].size()
                        hole_options = hole_options[1:]


            logger.info("Number options remaining: {}".format(nr_options_remaining))
            logger.info("Singleton regions {}".format(oracle.dtmcs_checked))
            logger.info("Critical timings so far: {} building, {} checking {} analysis.".format(oracle._build_time,
                                                                                                oracle._mc_time,
                                                                                                oracle._sched_ana_time))

            if len(hole_options) == 0:
                if len(hole_options_next_round) == 0:
                    break
                logger.info("Next round...")
                if len(hole_options_next_round) * 8 > remaining:
                    self.use_oracle = False
                hole_options = hole_options_next_round
                hole_options_next_round = []

        return False, None

                # print("[" + ",".join([str(x) for x in hole_options]) + "]")

    def _run_optimal_feasibility(self):
        """
        TODO debug again after recent refactoring. 
        :return:
        """

        if self.input_has_multiple_properties():
            raise RuntimeError("Lifting is only implemented for single properties")

        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)

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
        threshold = math.inf
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
            if threshold_synthesis_result == dynasty.jani.quotient_container.ThresholdSynthesisResult.UNDECIDED:
                logger.debug("Undecided.")


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
                if threshold_synthesis_result == ThresholdSynthesisResult.ABOVE:
                    logger.debug("All above.")
                    options_above.append(hole_options[0])
                    nr_options_above += hole_options[0].size()
                    hole_options = hole_options[1:]

                else:
                    logger.debug("All below.")
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
            if len(hole_options) == 0:
                if len(hole_options_next_round) == 0:
                    break
                logger.info("Next round...")
                if len(hole_options_next_round) * 8 > remaining:
                    self.use_oracle = False
                hole_options = hole_options_next_round
                hole_options_next_round = []


            logger.info("Optimal value at {} with {}".format(threshold, optimal_hole_options))

                # print("[" + ",".join([str(x) for x in hole_options]) + "]")

    def run_partitioning(self):
        """

        :return: 
        """

        if self.input_has_multiple_properties():
            raise RuntimeError("Lifting is only implemented for single properties")

        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)

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
        threshold = float(self.thresholds[0])
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
            threshold_synthesis_result = oracle.decided(threshold)
            if threshold_synthesis_result == dynasty.jani.quotient_container.ThresholdSynthesisResult.UNDECIDED:
                logger.debug("Undecided.")

                if hole_options[0].size() > 2:
                    oracle.scheduler_color_analysis()
                    hole_options_next_round += self._split_hole_options(hole_options[0], oracle)
                else:
                    hole_options_next_round += self._split_hole_options(hole_options[0], None)

            else:
                if threshold_synthesis_result == ThresholdSynthesisResult.ABOVE:
                    logger.debug("All above.")
                    options_above.append(hole_options[0])
                    nr_options_above += hole_options[0].size()

                else:
                    logger.debug("All below.")

                    options_below.append(hole_options[0])
                    nr_options_below += hole_options[0].size()


            remaining = total_nr_options - nr_options_above - nr_options_below
            logger.info("Number options above {} (in {} regions) and below {} (in {} regions). Remaining: {}".format(
                nr_options_above, len(options_above), nr_options_below, len(options_below), remaining))
            logger.info("Singleton regions {}".format(oracle.dtmcs_checked))
            logger.info("Critical timings so far: {} building, {} checking {} analysis.".format(oracle._build_time,
                                                                                                oracle._mc_time,
                                                                                                oracle._sched_ana_time))
            hole_options = hole_options[1:]
            if len(hole_options) == 0:
                if len(hole_options_next_round) == 0:
                    break
                logger.info("Next round...")
                if len(hole_options_next_round) * 8 > remaining:
                    self.use_oracle = False
                hole_options = hole_options_next_round
                hole_options_next_round = []



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
        # logger.debug(other_side_list)

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

                one_vals = [self.hole_options[k][one_side] for one_side in one_side_list if one_side is not None]
                other_vals = [self.hole_options[k][other_side] for other_side in other_side_list if
                              other_side is not None]
                logger.debug("Pre-splitted {} and {}".format(one_vals, other_vals))
                new_v = [x for x in v if x not in one_vals + other_vals]
                logger.debug("Now distribute {}".format(new_v))
                second, first = split_list(new_v)
                # if one_side is not None:
                first = first + one_vals
                # if other_side is not None:
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


class AllInOneChecker(QuotientBasedFamilyChecker):
    """

    """

    def run_feasibility(self):
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes
        logger.info("Total number of options: {}".format(self.hole_options.size()))

        _ = self._analyse_from_scratch(self._open_constants, self.hole_options, self._open_constants.keys(), 0)


class OneByOneChecker(QuotientBasedFamilyChecker):
    """

    TODO: strictly, this class is not based on lifting (but the code depends on mc_formulae for historical reasons
    """

    def run_feasibility(self):
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
            #TODO something with result

class ConsistentSchedChecker(QuotientBasedFamilyChecker):
    """
    Enumerate over all schedulers.

    Supports (only) threshold synthesis as of now. 
    """
    def run_partitioning(self):
        return self._run(False,False)

    def run_feasibility(self):
        if self.input_has_multiple_properties():
            raise NotImplementedError("Support for multiple properties is not implemented (but straightforward)")
        if self.input_has_optimality_property():
            raise NotImplementedError("Support for optimality is not implemented, but straightforward")
            #self._run(False,True)
        return self._run()

    def _run(self, allow_termination_with_feasible_solution=True, keep_optimal=False):
        if keep_optimal:
            raise NotImplementedError("Keep optimal not yet implemented")
        prep_start = time.time()
        self.jani_quotient_builder = JaniQuotientBuilder(self.sketch, self.holes)
        self._open_constants = self.holes
        threshold = float(self.thresholds[0])
        logger.debug("Threshold is {}".format(threshold))

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
            if allow_termination_with_feasible_solution:
                # Plain feasibility checking.
                threshold_synthesis_result = oracle.decided(threshold)
                if threshold_synthesis_result == dynasty.jani.quotient_container.ThresholdSynthesisResult.ABOVE and self._accept_if_above:
                    return True, selected_hole_option.pick_one_in_family()
                if threshold_synthesis_result == dynasty.jani.quotient_container.ThresholdSynthesisResult.BELOW and not self._accept_if_above:
                    return True, selected_hole_option.pick_one_in_family()

            # TODO For partitioning, the result should be stored somehow.
            logger.info("Ran for {}, expect total up to: {}".format(prep_time + time.time() - iter_start, prep_time + (
                time.time() - iter_start) * total_nr_options / iterations))
            total_states += oracle._mdp_handling.mdp.nr_states
            total_transitions += oracle._mdp_handling.mdp.nr_transitions
            logger.info("Average states so far {}.  Average transitions so far {}".format(total_states / iterations,total_transitions / iterations))

        return False, None


class SmtChecker(QuotientBasedFamilyChecker):
    def run_feasibility(self):
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
