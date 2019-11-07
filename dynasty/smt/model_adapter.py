import pysmt.shortcuts as smt
import logging
import stormpy

logger = logging.getLogger(__name__)

class SmtConsistentSchedulerSolver:


    def __init__(self):
        self.state_vars = None
        self.option_vars = None

    def _to_smt_relation(self, relation):
        """
        
        :param relation: 
        :return: A tuple with the corresponding relation, and the relation to use for the constraints. 
        """

        if relation == stormpy.ComparisonType.LEQ:
            return smt.LE, smt.GE
        elif relation == stormpy.ComparisonType.LESS:
            return smt.LT, smt.GE
        elif relation == stormpy.ComparisonType.GEQ:
            return smt.GE, smt.LE
        elif relation == stormpy.ComparisonType.GREATER:
            return smt.GT, smt.LE

    def initialize(self, mdp, colors, hole_options, reward_name, okay_states, target_states, threshold, relation):
        logger.warning("This approach has been tested sparsely.")
        prob0E,prob1A = stormpy.compute_prob01min_states(mdp,okay_states,target_states)
        sink_states = ~okay_states

        assert len(mdp.initial_states) == 1
        self.state_vars = [smt.Symbol("p_{}".format(i), smt.REAL) for i in range(mdp.nr_states)]
        self.state_prob1_vars = [smt.Symbol("asure_{}".format(i)) for i in range(mdp.nr_states)]
        self.state_probpos_vars = [smt.Symbol("x_{}".format(i)) for i in range(mdp.nr_states)]
        self.state_order_vars = [smt.Symbol("r_{}".format(i), smt.REAL) for i in range(mdp.nr_states)]
        self.option_vars = dict()
        for h, opts in hole_options.items():
            self.option_vars[h] = {index: smt.Symbol("h_{}_{}".format(h, opt)) for index, opt in enumerate(opts)}
        self.transition_system = []
        logger.debug("Obtain rewards if necessary")

        rewards = mdp.reward_models[reward_name] if reward_name else None
        if rewards:
            assert not rewards.has_transition_rewards
            state_rewards = rewards.has_state_rewards
            action_rewards = rewards.has_state_action_rewards
            logger.debug("Model has state rewards: {}, has state/action rewards {}".format(state_rewards, action_rewards))

            self.transition_system.append(self.state_prob1_vars[mdp.initial_states[0]])

        threshold_inequality, action_constraint_inequality = self._to_smt_relation(relation)  # TODO or GE
        self.transition_system.append(threshold_inequality(self.state_vars[mdp.initial_states[0]], smt.Real(float(threshold))))


        state_order_domain_constraint = smt.And([smt.And(smt.GE(var, smt.Real(0)), smt.LE(var, smt.Real(1))) for var in self.state_order_vars])
        self.transition_system.append(state_order_domain_constraint)
        #TODO how to ensure that prob is zero if there is no path.

        select_parameter_value_constraints = []
        for h, opts in self.option_vars.items():
            select_parameter_value_constraints.append(smt.Or(ov for ov in opts.values()))
            for i, opt1 in enumerate(opts.values()):
                for opt2 in list(opts.values())[i+1:]:
                    select_parameter_value_constraints.append(smt.Not(smt.And(opt1, opt2)))
        #logger.debug("Consistency: {}".format(smt.And(select_parameter_value_constraints)))
        self.transition_system.append(smt.And(select_parameter_value_constraints))


        for state in mdp.states:
            if sink_states.get(state.id):
                assert rewards is None
                self.transition_system.append(smt.Equals(self.state_vars[state.id], smt.REAL(0)))
                #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                self.transition_system.append(smt.Not(self.state_prob1_vars[state.id]))
                #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                self.transition_system.append(smt.Equals(self.state_order_vars[state.id], smt.Real(0)))
                #logger.debug("Constraint: {}".format(self.transition_system[-1]))
            elif target_states.get(state.id):
                self.transition_system.append(smt.Equals(self.state_order_vars[state.id], smt.Real(1)))
                #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                self.transition_system.append(self.state_prob1_vars[state.id])
                #logger.debug("Constraint: {}".format(self.transition_system[-1]))

                if rewards is None:
                    self.transition_system.append(smt.Equals(self.state_vars[state.id], smt.Real(1)))
                    #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                else:
                    self.transition_system.append(self.state_probpos_vars[state.id])
                    #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                    self.transition_system.append(smt.Equals(self.state_vars[state.id], smt.Real(0)))
                    #logger.debug("Constraint: {}".format(self.transition_system[-1]))
            else:
                state_in_prob1A = False
                state_in_prob0E = False
                if prob0E.get(state.id):
                    state_in_prob0E = True
                else:
                    self.transition_system.append(smt.Equals(self.state_order_vars[state.id], smt.Real(1)))
                    #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                    self.transition_system.append(self.state_probpos_vars[state.id])
                    #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                if rewards and not state_in_prob0E:
                    if prob1A.get(state.id):
                        self.transition_system.append(self.state_prob1_vars[state.id])
                        logger.debug("Constraint: {}".format(self.transition_system[-1]))
                        state_in_prob1A = True


                for action in state.actions:
                    action_index = mdp.nondeterministic_choice_indices[state.id] + action.id
                    #logger.debug("Action index: {}".format(action_index))
                    precondition = smt.And([self.option_vars[hole][list(option)[0]] for hole, option in colors.get(action_index, dict()).items()])
                    reward_value = None
                    if rewards:
                        reward_const = (rewards.get_state_reward(state.id) if state_rewards else 0.0) + (rewards.get_state_action_reward(action_index) if action_rewards else 0.0)
                        reward_value = smt.Real(reward_const)
                    act_constraint = action_constraint_inequality(self.state_vars[state.id], smt.Plus([smt.Times(smt.Real(t.value()), self.state_vars[t.column]) for t in action.transitions] + [reward_value] if reward_value else []))
                    full_act_constraint = act_constraint
                    if state_in_prob0E:
                        if not rewards:
                            full_act_constraint = smt.And(smt.Implies(self.state_probpos_vars[state.id], act_constraint), smt.Implies(smt.Not(self.state_probpos_vars), smt.Equals(self.state_vars[state.id], smt.Real(0))))
                        self.transition_system.append(smt.Implies(precondition, smt.Iff(self.state_probpos_vars[state.id], smt.Or([smt.And(self.state_probpos_vars[t.column], smt.LT(self.state_order_vars[state.id], self.state_order_vars[t.column])) for t in action.transitions]))))
                        #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                    if rewards and not state_in_prob1A:
                        # prob_one(state) <-> probpos AND for all succ prob_one(succ)
                        self.transition_system.append(smt.Implies(precondition, smt.Iff(self.state_prob1_vars[state.id], smt.And([self.state_prob1_vars[t.column] for t in action.transitions] + [self.state_probpos_vars[state.id]]))))
                        #logger.debug("Constraint: {}".format(self.transition_system[-1]))
                    self.transition_system.append(smt.Implies(precondition,full_act_constraint))
                    #logger.debug("Constraint: {}".format(self.transition_system[-1]))



        if rewards:
            self.transition_system.append(smt.And([smt.GE(sv, smt.Real(0)) for sv in self.state_vars]))
        else:
            self.transition_system.append(smt.And([smt.And(smt.GE(sv, smt.Real(0)), smt.LE(sv, smt.Real(1))) for sv in self.state_vars]))

        #print(self.transition_system)
        formula = smt.And(self.transition_system)
        logger.info("Start SMT solver")
        model = smt.get_model(formula)

        if model:
            logger.info("SAT: Found {}".format(model))
        else:
            logger.info("UNSAT.")