
from dynasty.model_handling.mdp_handling import *
import logging
import math
import time

from collections import OrderedDict, Counter

logger = logging.getLogger(__name__)

from enum import Enum
class ThresholdSynthesisResult(Enum):
     ABOVE = 1
     BELOW = 2
     UNDECIDED = 3


class Engine(Enum):
    Sparse = 0,
    Hybrid = 1,
    Dd = 2


def is_inside_function(threshold):
    return (lambda lower, upper: threshold > lower and threshold < upper)


def _compute_choice_origins_to_colors(jani):
    result = {}
    for automaton in jani.automata:
        automaton_index = jani.get_automaton_index(automaton.name)
        for edge_index, edge in enumerate(automaton.edges):
            if edge.color != 0:
                result[jani.encode_automaton_and_edge_index(automaton_index, edge_index)] = edge.color
    return result

class InconsistencyInfo:
    def __init__(self):
        pass

class JaniQuotientContainer:
    """
    This class contains the result fo applying the jani model adapter,
    together with several utilities to interpret the results and decide on a refinement strategy
    """
    def __init__(self, jani_program, edge_coloring, ordered_holes, color_to_edge_indices):
        self._jani_program = jani_program
        self._edge_coloring = edge_coloring
        self._choice_origins_to_color = _compute_choice_origins_to_colors(jani_program)
        self._color_to_edge_indices = color_to_edge_indices
        self._mdp_handling = ModelHandling()
        self._latest_result = None
        self._latest_no_further_reward = None
        self._inconsistencies = []
        self._differences = []
        self._ordered_holes = ordered_holes
        self._full_colors = None

        self._mc_time = 0
        self._build_time = 0
        self._sched_ana_time = 0

        self.dtmcs_checked = 0

    @property
    def jani_program(self):
        return self._jani_program

    def consider_subset(self, subset, indexed_suboptions):
        logger.debug("Consider sub-set of hole-options: {}".format(subset))
        start_time = time.time()

        subcolors = self._edge_coloring.subcolors(indexed_suboptions)
        #print(subcolors)

        color_0_indices = self._color_to_edge_indices.get(0)
        collected_edge_indices = stormpy.FlatSet(color_0_indices)
        for c in subcolors:
            collected_edge_indices.insert_set(self._color_to_edge_indices.get(c))


        logger.debug("restrict MDP")
        self._mdp_handling.restrict(collected_edge_indices, color_0_indices)
        end_time = time.time()
        self._build_time += end_time - start_time
        #self._mdp_handling.display_model()

        # newcolors = set()
        # for act in range(self._mdp_handling.mdp.nr_choices):
        #     for edge_index in self._mdp_handling.mdp.choice_origins.get_edge_index_set(act):
        #         if edge_index in self._choice_origins_to_color:
        #             newcolors.add(self._choice_origins_to_color[edge_index])
        # assert subcolors == newcolors

    def _color_for_choice_origin(self, e):
        return self._choice_origins_to_color.get(e, 0)

    def _compute_differences(self, scheduler_selection_0, scheduler_selection_1):
        diffs = OrderedDict()
        for h, counts_0 in scheduler_selection_0.items():
            if h not in scheduler_selection_1:
                if len(counts_0) > 1:
                    diffs[h] = sum(counts_0.values())/8
                else:
                    diffs[h] = 0.0
            counts_1 = scheduler_selection_1.get(h, dict())
            diff_count = 0
            total_count = 0
            entries = 0
            for key, count in counts_0.items():
                diff_count += abs(count - counts_1.get(key, 0))
                total_count += count
                entries += 1
            for key, count in counts_1.items():
                total_count += count
                if key in counts_0:
                    continue
                diff_count += count
                entries += 1
            diffs[h] = (10*(1-(1/total_count))) if entries > 1 else 0
            if h in self._inconsistencies[0]:
                diffs[h] += 5*self._inconsistencies[0][h][0]
            if h in self._inconsistencies[1]:
                diffs[h] += 5*self._inconsistencies[1][h][0]
            diffs[h] += (diff_count * (1 - 1/entries)) if entries > 0 else 0
            diffs[h] *= 1.05 if (entries % 2 == 0) else 1

        for h, counts_1 in scheduler_selection_1.items():
            if h not in scheduler_selection_0:
                if len(counts_1) > 1:
                    diffs[h] = sum(counts_1.values())/8 #discount
                else:
                    diffs[h] = 0.0
        logger.debug("Schedulers differ in {}".format(diffs))
        max_count = 0
        max_key = None
        for key, c in diffs.items():
            if c > max_count:
                max_key = key
                max_count = c
        logger.debug("Splitting in {}".format(max_key))

        if max_key is None:
            return None

        if max_key not in scheduler_selection_0:
            logger.warning("Unlikely case; not properly implemented.")
            return max_key, None, None
        if max_key not in scheduler_selection_1:
            logger.warning("Unlikely case; not properly implemented.")
            return max_key, None, None

        counts_0 = scheduler_selection_0.get(max_key, Counter())
        counts_1 = scheduler_selection_1.get(max_key, Counter())
        logger.debug("Splitting Options based on {} and {}".format(counts_0, counts_1))
        counts_0.subtract(counts_1)

        logger.debug("Splitting Options Differences {}".format(counts_0))
        def split_list(a_list):
            half = len(a_list) // 2
            return a_list[:half], a_list[half:]
        first_half, second_half = split_list([x[0] for x in counts_0.most_common()])

        return max_key, first_half, second_half

    def _merge_inconsistencies(self):
        logger.debug("Check inconsistencies for a good split candidate")
        assert len(self._inconsistencies) == 2
        propose_split_score = 0
        propose_split = None
        for h in self._ordered_holes:
            if h in self._inconsistencies[0] and h in self._inconsistencies[1]:
                if True: # self._inconsistencies[0][h][1] != self._inconsistencies[1][h][1]:
                    if self._inconsistencies[0][h][0] + self._inconsistencies[1][h][0] + self._inconsistencies[0][h][2] + self._inconsistencies[1][h][2]  > propose_split_score:
                        propose_split_score = self._inconsistencies[0][h][0] + self._inconsistencies[1][h][0] + self._inconsistencies[0][h][2] + self._inconsistencies[1][h][2]
                        if self._inconsistencies[0][h][1] != self._inconsistencies[1][h][1]:
                            propose_split = (h, self._inconsistencies[0][h][1], self._inconsistencies[1][h][1])
                        else:
                            propose_split = h, self._inconsistencies[0][h][1], None
        return propose_split

    def _apply_scheduler(self, mdp, scheduler, drop_unreachable_states):
        action_selection = scheduler.compute_action_support(mdp.nondeterministic_choice_indices)
        all_states = stormpy.BitVector(mdp.nr_states, True)
        subsystem_construction_options = stormpy.SubsystemBuilderOptions()
        subsystem_construction_options.build_action_mapping = True
        result = stormpy.construct_submodel(mdp, all_states, action_selection, not drop_unreachable_states, subsystem_construction_options)

        return result.model, result.new_to_old_state_mapping, result.new_to_old_action_mapping

    def get_full_colors(self):
        logger.debug("Compute full colors")
        if self._full_colors is None:
            self._full_colors = self._model_color_analysis_acts(self._mdp_handling.full_mdp)
        return self._full_colors

    def scheduler_color_analysis(self):
        if self._mdp_handling.submodel_is_dtmc():
            # NOthing to do
            return
        start_time = time.time()
        store_colors = True
        if not self._latest_result:
            raise RuntimeError("No result stored.")
        # TODO copy is not strictly necessary.

        assert self._mdp_handling.mdp.has_choice_origins()
        if store_colors:
            self.get_full_colors()

        color_maps = []
        self._hole_option_maps = []
        self._inconsistencies = []
        assert self._latest_result.scheduler is not None
        assert self._latest_result.alt_scheduler is not None
        for scheduler in [self._latest_result.scheduler, self._latest_result.alt_scheduler]:
            logger.info("Compute colors in the scheduler...")
            logger.info("Applying scheduler...")
            assert scheduler.memoryless
            assert scheduler.deterministic
            #dtmc = self._mdp_handling.mdp.apply_scheduler(scheduler, drop_unreachable_states=True)
            _, state_map, action_map = self._apply_scheduler(self._mdp_handling.mdp, scheduler, drop_unreachable_states=True)
            #logger.info("Counting colors...")
            #assert dtmc.has_choice_origins()
            # TODO model analysis. (Reuse?)
            #color_map = self._model_color_analysis_aux(dtmc)
            #color_maps.append(color_map)

            logger.debug("Collect hole counts...")
            #hole_option_map = self._selected_hole_counts(color_map, self._latest_result.lower_bound_result,
             #                                            self._latest_result.upper_bound_result)

            hole_option_map = self._selected_hole_counts_incremental(state_map, action_map, self._latest_result.lower_bound_result,
                                                         self._latest_result.upper_bound_result)
            logger.debug("Selected holes in scheduler: {}".format(hole_option_map))
            print(hole_option_map)

            self._inconsistencies.append(self._inconsistent_options(hole_option_map))
            self._hole_option_maps.append(hole_option_map)
        end_time = time.time()
        self._sched_ana_time += end_time - start_time

    def _model_color_analysis_acts(self, mdp):
        act_to_color = OrderedDict()
        for actindex in range(mdp.nr_choices):
                autedgeindices = mdp.choice_origins.get_edge_index_set(actindex)
                act_to_color[actindex] = set([self._color_for_choice_origin(e) for e in autedgeindices])
        color_map = OrderedDict()
        print(act_to_color)
        for act, colors in act_to_color.items():
            assigns = self._edge_coloring.get_hole_assignment_set_colors(colors)
            if len(assigns) > 0:
                color_map[act] = self._edge_coloring.get_hole_assignment_set_colors(colors)
        return color_map

    def _model_color_analysis_aux(self, mdp):
        state_act_to_color = OrderedDict()
        for state in mdp.states:
            state_act_to_color[state.id] = []
            for action in state.actions:
                action_index = state.id if mdp.model_type == stormpy.ModelType.DTMC else (mdp.nondeterministic_choice_indices[state.id] + action.id)
                autedgeindices = mdp.choice_origins.get_edge_index_set(action_index)
                state_act_to_color[state.id].append([self._color_for_choice_origin(e) for e in autedgeindices])
        color_map = OrderedDict()
        for state, act_to_colors in state_act_to_color.items():
            color_map[state] = self._edge_coloring.get_hole_assignments(act_to_colors)
        return color_map

    def model_color_analysis(self):
        return self._model_color_analysis_aux(self._mdp_handling.mdp)

    def _selected_hole_mapping(self, color_map):
        selected_hole_option_map = dict()
        for state, hole_option_map in color_map.items():
            for hole, option_selection_map in hole_option_map.items():
                e = selected_hole_option_map.get(hole, set())
                for o in option_selection_map:
                    e.add(o)
                selected_hole_option_map[hole] = e
        #print(selected_hole_option_map)

    def _selected_hole_counts_incremental(self, state_map, action_map, mc_lower_result, mc_upper_result ):
        selected_hole_option_map = OrderedDict()
        for key in self._ordered_holes:
            selected_hole_option_map[key] = Counter()
        difference = mc_lower_result.at(self._mdp_handling.full_mdp.initial_states[0]) - mc_upper_result.at(self._mdp_handling.full_mdp.initial_states[0])
        if difference < 0.001:
            # avoid numerical issues.
            # TODO Think about handling diff = 0 seperately.
            difference = 0.001
        scale_factor = 1.0/abs(difference)
        for submdp_state, submdp_action in zip(state_map, action_map):
            if abs(mc_lower_result.at(submdp_state) - mc_upper_result.at(submdp_state))*scale_factor < 0.3:
                continue
            orig_action_id = self._mdp_handling.get_original_action(submdp_action)
            for hole, option_selection in self._full_colors.get(orig_action_id, dict()).items():
                selected_hole_option_map[hole].update(option_selection)
        return selected_hole_option_map


    def _selected_hole_counts(self, color_map, mc_lower_result, mc_upper_result):
        selected_hole_option_map = dict()

        for state, hole_option_map in color_map.items():
            for hole, option_selection_map in hole_option_map.items():
                e = selected_hole_option_map.get(hole, dict())
                for o in option_selection_map:
                    former_count = e.get(o, 0)
                    e[o] = former_count + 1
                selected_hole_option_map[hole] = e
        return OrderedDict([(key, selected_hole_option_map[key]) for key in self._ordered_holes if key in selected_hole_option_map])


    def _inconsistent_options(self, hole_option_map):
        logger.debug("Check for inconsistent options...")
        #print(color_map)
        # Compute a map hole -> set[options] first.
        # TODO switch to selected-hole-map (include counts for debugging right now)


        inconsistent = OrderedDict()
        for h, counts in hole_option_map.items():
            if len(counts) > 1:
                inconsistent[h] = (max(counts.values())/100, max(counts.keys(), key=lambda x: counts.get(x)), len(counts))
        print(inconsistent)
        if len(inconsistent) == 0:
            logger.debug("Found consistent scheduler: {}".format(hole_option_map))

        return inconsistent

        # TODO compute the several colors that correspond to one hole.
        # We compute a dict from action to color first.
        # That is inefficient for now as we need it just for this single task, but
        # I guess we will use it multiple times.

    def decided(self, threshold):
        if threshold > self._latest_result.absolute_max:
            logger.debug("Absolute maximum {} is below threshold {}".format(self._latest_result.absolute_max, threshold))
            return ThresholdSynthesisResult.BELOW
        elif threshold < self._latest_result.absolute_min:
            return ThresholdSynthesisResult.ABOVE
        return ThresholdSynthesisResult.UNDECIDED

    def upper_bound(self):
        return self._latest_result.absolute_max

    def lower_bound(self):
        return self._latest_result.absolute_min

    def is_lower_bound_tight(self):
        return len(self._lower_bound_inconsistencies()) == 0

    def _lower_bound_inconsistencies(self):
        return self._inconsistencies[1] if self._latest_result.maximising else self._inconsistencies[0]

    def is_upper_bound_tight(self):
        return len(self._upper_bound_inconsistencies()) == 0

    def _upper_bound_inconsistencies(self):
        return self._inconsistencies[0] if self._latest_result.maximising else self._inconsistencies[1]


    def propose_split(self, directions = None):
        start_time = time.time()
        logger.debug("Propose split...!")

        assert len(self._inconsistencies) == 2
        # is there an inconsistency in both schedulers:
        proposed_split = self._compute_differences(self._hole_option_maps[0], self._hole_option_maps[1])#self._merge_inconsistencies()
        #proposed_split = None
        if proposed_split is not None:
            end_time = time.time()
            self._sched_ana_time += end_time - start_time
            return proposed_split[0], proposed_split[1], proposed_split[2]

        proposed_split = self._merge_inconsistencies()
        if proposed_split is not None:

            end_time = time.time()
            self._sched_ana_time += end_time - start_time
            return proposed_split[0], proposed_split[1], proposed_split[2]
        else:
            proposed_split = self._compute_differences(self._hole_option_maps[0], self._hole_option_maps[1])
            if proposed_split is not None:
                end_time = time.time()
                self._sched_ana_time += end_time - start_time
                return proposed_split[0], proposed_split[1], proposed_split[2]

        end_time = time.time()
        self._sched_ana_time += end_time - start_time
        if len(self._inconsistencies[0]) > 0:
            return list(self._inconsistencies[0])[0], None, None
        if len(self._inconsistencies[1]) > 0:
            return list(self._inconsistencies[1])[0], None, None
        return None, None, None

    def prepare(self, formulae, alt_formulae, engine=Engine.Sparse):
        start_time = time.time()
        if engine in [Engine.Hybrid, Engine.Dd]:
            self._mdp_handling.build_symbolic_model(self._jani_program, formulae, alt_formulae)
        else:
            assert engine == Engine.Sparse
            self._mdp_handling.build_model(self._jani_program, formulae, alt_formulae)
        end_time = time.time()
        self._build_time += end_time - start_time

    def analyse(self, threshold = None, index=0, engine=Engine.Sparse):
        start_time = time.time()
        if self._mdp_handling.submodel_is_dtmc():
            self.dtmcs_checked += 1
        if engine == engine.Dd:
            self._mdp_handling.mc_model_symbolic(index)
        elif engine == engine.Hybrid:
            self._mdp_handling.mc_model_hybrid(index)
        else:
            assert engine == Engine.Sparse
            self._latest_result = self._mdp_handling.mc_model(index, compute_action_values=False, check_dir_2=is_inside_function(threshold) if threshold is not None else always_true)
        end_time = time.time()
        self._mc_time += end_time - start_time
        return self._latest_result

