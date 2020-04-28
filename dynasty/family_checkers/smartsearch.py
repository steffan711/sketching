import random
import time
import threading
import functools
import logging
import re
import itertools
from collections import OrderedDict

from dynasty.family_checkers.familychecker import FamilyChecker
from dynasty.sketch_parser.parser import parse

import stormpy
from stormpy.logic.logic import ComparisonType
from z3 import *

logger = logging.getLogger(__name__)

class SmartSearcher(FamilyChecker):

    def __init__(self, optimize_one):
        super().__init__()
        self.template_metavariables = OrderedDict()
        self._smtlock = threading.Lock()
        self.num_of_options_for_holes = []
        self.num_of_holes = 0
        self.penalization_const = 20.0
        self.num_of_generated_MO = 0  # MO - mutation only solution
        self.num_of_generated_Rand = 0  # count of randomly generated individuals
        self.time_limit_sec = 30
        self.time_clock_start_sec = None
        self.mutation_probability = 0.05
        self.gener_indiv_counter = 0
        self.current_best_indiv = []
        self.offspring_database = set()
        self.max_size_offspring_database = 1000
        self.optimized_property = optimize_one

    def initialize_counters(self):
        self.offspring_database = set()
        self.current_best_indiv = []
        self.num_of_generated_MO = 0
        self.num_of_generated_Rand = 0
        self.gener_indiv_counter = 0

    def initialise(self):
        self._initialize_solver()

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

    def load_sketch(self, path, property_path, optimality_path=None, constant_str=""):
        logger.info("Do the parsing first!!!")
        #sketch_path = os.path.splitext(path)[0] + '.sketch'
        # This will replace the content of path if the file exists
        #self._unwind_sketch_macros(path, sketch_path)

        return super(SmartSearcher, self).load_sketch(path, property_path, optimality_path, constant_str)

    def _unwind_sketch_macros(self, path, sketch_path):
        with open(sketch_path, 'r') as file:
            data = file.read()
        macros = re.findall(r"(?<=#genQIDBeg).*?(?=#genQIDEnd)", data, re.MULTILINE|re.DOTALL)

        constants_str = ""
        allowed_str = "\n"
        symmetries_str = "!symmetries\n"

        for macro in macros:
            macro_data = parse(macro)
            unwound_macro_data = self._macro_unwinder(macro_data)
            data = re.sub(r"#genQIDBeg.*?#genQIDEnd", ''.join(unwound_macro_data[0]), data, 1, re.MULTILINE|re.DOTALL)

            for constants in unwound_macro_data[1]:
                constants_str += '\n'.join(["const " + const_name + ";" for const_name in constants[2]]) + "\n"
                if type(constants[1]) is tuple:
                    if not (type(constants[1][0]) is int and type(constants[1][1])):
                        logger.error("Interval for guard synthesis cannot refer to a variable!")
                        return None
                    possible_vals_str = ';'.join([str(i) for i in range(constants[1][0], constants[1][1] + 1)])
                else:
                    possible_vals_str = ';'.join([ str(const) for const in constants[1]])
                allowed_str += '\n'.join([const_name + ";" + possible_vals_str for const_name in constants[2]]) + "\n"
                if constants[0]:
                    symmetries_str += ','.join(constants[2]) + "\n"

        if macros and not re.search("#genCONST", data):
            logger.error("No macro for space of constants specified!")
            return None

        data = re.sub(r"#genCONST", constants_str, data, 1, re.MULTILINE | re.DOTALL)

        allowed_path = os.path.splitext(path)[0] + '.allowed'
        with open(allowed_path, 'a+') as file:
            file.write(allowed_str)

        restriction_path = os.path.splitext(path)[0] + '.restrictions'
        with open(restriction_path, 'a+') as file:
            file.write(symmetries_str)

        with open(path, 'w+') as file:
            file.write(data)
        return None

    def _comparison_from_frac(self, quan_name, interval, frac, sign):
        space = " "
        if (interval[0] == 0):
            border = ""
            lpar = ""
            rpar = ""
        else:
            border = " - " + (interval[0])
            lpar = "("
            rpar = ")"
        return lpar + quan_name + border + rpar + "*" + str(frac[1]) + space + sign + space + str(frac[0]) + "*" + lpar + str(interval[1]) + border + rpar

    def _macro_unwinder(self, macro_data):
        constants = list()
        intervals = list()
        # Create intervals
        for count, quan in enumerate(macro_data[1]):
            quan_intervals = list()
            quan_constants = list()
            if (type(quan[2]) is list):
                if quan[2]:
                    quan_intervals.append(self._comparison_from_frac(quan[0], quan[1], quan[2][0], "<="))
                    prev_frac = quan[2][0]
                    for frac in quan[2][1:]:
                        left_part_of_interval = self._comparison_from_frac(quan[0], quan[1], prev_frac, ">")
                        quan_intervals.append(left_part_of_interval + " & " + self._comparison_from_frac(quan[0], quan[1], frac, "<="))
                        prev_frac = frac
                    quan_intervals.append(self._comparison_from_frac(quan[0], quan[1], quan[2][-1], ">"))
            elif (type(quan[2]) is int):
                for i in range(quan[2]):
                    quan_constants.append("c_" + "m" + str(count) + "_" + str(i))
                quan_intervals = list()
                if quan_constants:
                    quan_intervals.append(quan[0] + " <= " + quan_constants[0])
                    prev_const = quan_constants[0]
                    for const in quan_constants[1:]:
                        quan_intervals.append(quan[0] + " > " + prev_const + " & " + quan[0] + " <= " + const)
                        prev_const = const
                    quan_intervals.append(quan[0] + " > " + quan_constants[-1])
                    constants.append((True, quan[1], quan_constants))
            else:
                logger.error("Incorrect input for arity or fractions!")
                return None
            if quan_intervals:
                intervals.append(quan_intervals)

        # Prepare guards
        guard_data = list(itertools.product(*intervals))
        # Prepare actions
        index_permutations = list(itertools.product(*[[i for i in range(len(j))] for j in intervals]))
        actions = list()
        dep_constants = [[] for i in range(len(macro_data[2]))]
        for perm in index_permutations:
            suffix = ""
            for num in perm:
                suffix += "_" + str(num)
            action_data = list()
            for count, dep in enumerate(macro_data[2]):
                const = "c_" + dep[0] + suffix
                dep_constants[count].append(const)
                action_data.append("(" + dep[0] + "'" + " = " + const + ")")
            actions.append(action_data)
        # Add dependency constants into general constants
        for count, dep in enumerate(macro_data[2]):
            constants.append((False, dep[1], dep_constants[count]))


        # Create commands
        commands = list()
        space = " "
        for guard, action in zip(guard_data, actions):
            command = "\t[" + macro_data[0] + "]" + space
            command += guard[0]
            for interval in guard[1:]:
                command += " & " + interval
            command += " -> "
            command += action[0]
            for assignment in action[1:]:
                command += " & " + assignment
            command += ";\n\n"
            commands.append(command)

        return (commands, constants)

    def _time_is_over(self):
        return time.time() - self.time_clock_start_sec > self.time_limit_sec

    def _init_individual_MO(self):
        assert 1 <= sum(self.num_of_options_for_holes)

        individual = []
        while True:
            individual.clear()
            for hole_idx in range(self.num_of_holes):
                option_idx = random.randrange(self.num_of_options_for_holes[hole_idx])
                individual.append(option_idx)
            clause = And([var == val for var, val in zip(self.template_metavariables.keys(), individual)])
            self._smtlock.acquire()
            self.solver.push()
            self.solver.add(clause)
            solver_result = self.solver.check()
            self.solver.pop()
            self._smtlock.release()
            if solver_result != sat:
                if self._time_is_over():
                    logger.debug("Run out of time while generating initial individual.")
                    return None
                continue
            else:
                # Remember all the offspring in offspring_database, solver is superfluous for that purpose
                # self.solver.add(Not(clause))
                self.offspring_database.add(tuple(individual))
                self.num_of_generated_MO += 1
                self.gener_indiv_counter += 1
                break
        return individual

    def _generate_offspring_MO(self, individual, offspring_count, offspring, state_space_size):
        if self.num_of_generated_MO > state_space_size - offspring_count:
            # It is not possible to generate the next generation - state space exhausted
            logger.debug("State space exhausted.")
            return False
        if self.current_best_indiv != individual:
            self.current_best_indiv = individual.copy()
            if len(self.offspring_database) > self.max_size_offspring_database:
                self.offspring_database = set()
            # self.offspring_database = set()
        for _ in range(offspring_count):
            while True:
                new_individual = individual.copy()
                genotype_changed = False
                while not genotype_changed:
                    for hole_idx in range(self.num_of_holes):
                        if random.random() < self.mutation_probability:
                            option_idx = random.randrange(self.num_of_options_for_holes[hole_idx])
                            while option_idx == new_individual[hole_idx]:
                                option_idx = random.randrange(self.num_of_options_for_holes[hole_idx])
                            new_individual[hole_idx] = option_idx
                            genotype_changed = True
                if tuple(new_individual) in self.offspring_database:
                    continue
                self.gener_indiv_counter += 1
                clause = And([var == val for var, val in zip(self.template_metavariables.keys(), new_individual)])
                self._smtlock.acquire()
                self.solver.push()
                self.solver.add(clause)
                solver_result = self.solver.check()
                self.solver.pop()
                self._smtlock.release()
                if solver_result != sat:
                    if self._time_is_over():
                        logger.debug("Run out of time while generating offspring.")
                        return False
                    continue
                else:
                    offspring.append(new_individual)
                    self.offspring_database.add(tuple(new_individual))
                    # Remember all the offspring in offspring_database, solver is superfluous for that purpose
                    # self.solver.add(Not(clause))
                    self.num_of_generated_MO += 1
                    break
        return True

    def _indiv_info(self, individual):
        # Create an assignment for the holes
        hole_assignments = self._individual_to_constants_assignment(individual)

        # And construct
        instance = self.build_instance(hole_assignments)
        model = stormpy.build_model(instance, [p.property for p in self.properties])
        model.reduce_to_state_based_rewards()
        for p_qual, p_quan in zip(self.properties, self.quantitative_properties):
            mc_result = stormpy.model_checking(model, p_quan).at(model.initial_states[0])
            threshold = float(p_qual.property.raw_formula.threshold)
            if p_qual.property.raw_formula.is_probability_operator:
                logger.debug("Probability operator: {}".format(p_qual.property.raw_formula.comparison_type))
            elif p_qual.property.raw_formula.is_reward_operator:
                logger.debug("Reward operator: {}".format(p_qual.property.raw_formula.comparison_type))
            else:
                assert False
            logger.debug("Operator's threshold: {}".format(threshold))
            logger.debug("Computed value for the operator: {}".format(mc_result))

    def _fitness_MO(self, individual):
        # Invariant - individual that gets here is always valid with respect to the constrains on options

        # Create an assignment for the holes
        hole_assignments = self._individual_to_constants_assignment(individual)

        # And construct
        instance = self.build_instance(hole_assignments)
        model = stormpy.build_model(instance, [p.property for p in self.properties])
        model.reduce_to_state_based_rewards()
        # model = self._build_model(instance)

        fitness_val = 0.
        penalisation = 0.
        sum = 0
        for p_qual, p_quan in zip(self.properties, self.quantitative_properties):
            # Check the property
            mc_result = stormpy.model_checking(model, p_quan).at(model.initial_states[0])
            # logger.debug("MC Result: {}".format(mc_result))
            # logger.debug("model states: {}, transitions: {}".format(model.nr_states, model.nr_transitions))
            # formula = p_qual.property.raw_formula
            # print(p_quan.raw_formula.threshold)
            threshold = float(p_qual.property.raw_formula.threshold)

            if p_qual.property.raw_formula.is_probability_operator:
                fitness_norm_const = 1.
            elif p_qual.property.raw_formula.is_reward_operator:
                assert (p_qual.property.raw_formula.comparison_type == ComparisonType.LEQ or
                        p_qual.property.raw_formula.comparison_type == ComparisonType.LESS)
                fitness_norm_const = 1. / threshold
            else:
                assert False

            if self.optimized_property:
                is_optimized = int((sum + 1) == self.optimized_property)
            else:
                is_optimized = 1.

            if p_qual.property.raw_formula.comparison_type == ComparisonType.GEQ:
                if mc_result >= threshold:
                    fitness_val += (mc_result - threshold) * is_optimized
                else:
                    fitness_val += (mc_result - threshold) * self.penalization_const
                    penalisation -= 1.
            elif p_qual.property.raw_formula.comparison_type == ComparisonType.GREATER:
                if mc_result > threshold:
                    fitness_val += (mc_result - threshold) * is_optimized
                else:
                    fitness_val += (mc_result - threshold) * self.penalization_const
                    penalisation -= 1.
            elif p_qual.property.raw_formula.comparison_type == ComparisonType.LEQ:
                if mc_result <= threshold:
                    fitness_val += (threshold - mc_result) * fitness_norm_const * is_optimized
                else:
                    fitness_val += (threshold - mc_result) * self.penalization_const * fitness_norm_const
                    penalisation -= 1.
            elif p_qual.property.raw_formula.comparison_type == ComparisonType.LESS:
                if mc_result < threshold:
                    fitness_val += (threshold - mc_result) * fitness_norm_const * is_optimized
                else:
                    fitness_val += (threshold - mc_result) * self.penalization_const * fitness_norm_const
                    penalisation -= 1.
            else:
                assert False

            sum += 1

        assert sum > 0
        fitness_val /= sum
        fitness_val += penalisation
        return fitness_val

    def writeIndivDataByTime(self, file, indiv, fitness):
        file.write("#%s\n%f\t%f\n" % (indiv, time.time() - self.time_clock_start_sec, fitness))

    def writeIndivDataMO(self, file, indiv, fitness):
        file.write("#%s\n%f\t%f\n" % (indiv, self.num_of_generated_MO, fitness))

    def writeIndivDataRand(self, file, indiv, fitness):
        file.write("#%s\n%f\t%f\n" % (indiv, self.num_of_generated_Rand, fitness))

    def run_feasibility(self):
        self.num_of_holes = len(self.hole_options)

        for v in self.hole_options.values():
            self.num_of_options_for_holes.append(len(v))

        return self.run_GA_mutation_only("my_name1")

    def run_GA_mutation_only(self, projname):
        random.seed()
        self.time_clock_start_sec = time.time()
        individual = self._init_individual_MO()
        #individual = [3, 2, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0]
        self.current_best_indiv = individual.copy()
        # individual = [4, 6, 1, 7, 6, 3, 6, 7, 3, 5]
        fitness = self._fitness_MO(individual)
        logger.debug("Initial individual : {} with fitness : {}".format(individual, fitness))
        hole_assignments = self._individual_to_constants_assignment(individual)
        logger.info("Consider hole assignment: {}".format(
            ",".join("{}={}".format(k, v) for k, v in hole_assignments.items())))
        dir_name = "./Graphs and data/" + projname
        name_counter = 0
        while True:
            try:
                os.makedirs(dir_name)
            except OSError:
                if not name_counter:
                    dir_name += "(1)"
                else:
                    dir_name = dir_name[:dir_name.rfind("(")] + "(" + str(name_counter) + ")"
                name_counter += 1
                continue
            break
        f = open(dir_name + "/MutationOnlyFitness.dat", "a+")
        f2 = open(dir_name + "/MutationOnlyImproved.dat", "w+")
        self.writeIndivDataMO(f, individual, fitness)
        self.writeIndivDataMO(f2, individual, fitness)
        updateCount = 1
        updateCountOnlyBetter = 0
        state_space_size = functools.reduce(lambda x, y: x * y, self.num_of_options_for_holes, 1)
        while not (self._time_is_over()):
            offspring = []
            if self._generate_offspring_MO(individual, 10, offspring, state_space_size):
                for new_indiv in offspring:
                    new_fitness = self._fitness_MO(new_indiv)
                    updateCount += 1
                    self.writeIndivDataMO(f, new_indiv, new_fitness)
                    if new_fitness >= fitness:
                        if abs(new_fitness - fitness) >= 1e-8:
                            updateCountOnlyBetter += 1
                            self.writeIndivDataMO(f2, new_indiv, new_fitness)
                        fitness = new_fitness
                        individual = new_indiv
                        # self.writeIndivDataMO(f, individual, fitness)
                        logger.debug("New individual : {} with fitness : {}".format(individual, fitness))
                        hole_assignments = self._individual_to_constants_assignment(individual)
                        logger.info("Consider hole assignment: {}".format(
                            ",".join("{}={}".format(k, v) for k, v in hole_assignments.items())))
                # if fitness > -2.473026:
                # break
            else:
                break
            #if fitness > 0:
             #   break
        f.close()
        f2.close()
        from os import system
        cwd = os.getcwd()
        os.chdir(dir_name)
        system('gnuplot ../plot1.gp')  # Create gnuplot graph as specified in the file plot1.gp
        system('gnuplot ../plot2.gp')  # Create gnuplot graph as specified in the file plot2.gp
        os.chdir(cwd)

        logger.debug("Number of explored individuals : {} best fitness : {} best individual : {}".format(
            self.num_of_generated_MO, fitness, individual))
        logger.debug("Number of fitness updates: {}".format(updateCount))
        logger.debug("Number of fitness improvements: {}".format(updateCountOnlyBetter))
        logger.debug("Num of generated individuals: {}".format(self.gener_indiv_counter))
        logger.debug("Best individual info:")
        self._indiv_info(individual)
        return fitness >= 0., self._individual_to_constants_assignment(individual), None

    def _generate_indiv_Rand(self, state_space_size):
        random.seed()
        if self.num_of_generated_MO >= state_space_size:
            # It is not possible to generate the next generation - state space exhausted
            logger.debug("State space exhausted.")
            return None
        individual = []
        while True:
            individual.clear()
            for hole_idx in range(self.num_of_holes):
                option_idx = random.randrange(self.num_of_options_for_holes[hole_idx])
                individual.append(option_idx)
            clause = And([var == val for var, val in zip(self.template_metavariables.keys(), individual)])
            self._smtlock.acquire()
            self.solver.push()
            self.solver.add(clause)
            solver_result = self.solver.check()
            self.solver.pop()
            self._smtlock.release()
            if solver_result != sat:
                if self._time_is_over():
                    logger.debug("Run out of time while generating offspring.")
                    return None
                continue
            else:
                self.solver.add(Not(clause))
                self.num_of_generated_Rand += 1
                break
        return individual

    def run_Random_search(self, all_conflicts):
        state_space_size = functools.reduce(lambda x, y: x * y, self.num_of_options_for_holes, 1)
        individual = self._generate_indiv_Rand(state_space_size)
        fitness = self._fitness_MO(individual)
        logger.debug("Initial individual : {} with fitness : {}".format(individual, fitness))
        self.time_clock_start_sec = time.time()

        f = open("Graphs and data/RandomGenFitnessUpdate.dat", "a+")
        f2 = open("Graphs and data/RandomGenFitnessStrictlyImproved.dat", "w+")
        # Clock must be set when calling write functions
        self.writeIndivDataRand(f, individual, fitness)
        self.writeIndivDataRand(f2, individual, fitness)
        updateCount = 0
        updateCountOnlyBetter = 0
        while not (self._time_is_over()):
            new_indiv = self._generate_indiv_Rand(state_space_size)
            if new_indiv == None:
                break
            new_fitness = self._fitness_MO(new_indiv)
            updateCount += 1
            self.writeIndivDataRand(f, new_indiv, new_fitness)
            if new_fitness >= fitness:
                # updateCount += 1
                if abs(new_fitness - fitness) >= 1e-8:
                    updateCountOnlyBetter += 1
                    self.writeIndivDataRand(f2, new_indiv, new_fitness)
                fitness = new_fitness
                individual = new_indiv
                # self.writeIndivDataRand(f, individual, fitness)
                logger.debug("New individual : {} with fitness : {}".format(individual, fitness))
        logger.debug("Number of explored individuals : {} best fitness : {} best individual : {}".format(
            self.num_of_generated_Rand, fitness, individual))
        f.close()
        f2.close()
        from os import system
        cwd = os.getcwd()
        os.chdir('./Graphs and data')
        system('gnuplot plot3.gp')  # Create gnuplot graph as specified in the file plot3.gp
        system('gnuplot plot4.gp')  # Create gnuplot graph as specified in the file plot4.gp
        os.chdir(cwd)

        logger.debug("Number of explored individuals : {} best fitness : {} best individual : {}".format(
            self.num_of_generated_Rand, fitness, individual))
        logger.debug("Number of fitness updates: {}".format(updateCount))
        logger.debug("Number of fitness improvements: {}".format(updateCountOnlyBetter))
        return None

    def _individual_to_constants_assignment(self, individual):
        hole_assignments = OrderedDict()
        for option_idx, hole in zip(individual, self.template_metavariables.values()):
            hole_assignments[hole] = self.hole_options[hole][option_idx]
        return hole_assignments

    def build_instance(self, assignments):
        """
        From the sketch and the assignment for the holes, build a concrete instance

        :param assignments:
        :return:
        """
        # logger.info(
        #   "Consider hole assignment: {}".format(",".join("{}={}".format(k, v) for k, v in assignments.items())))
        constants_map = dict()
        ep = stormpy.storage.ExpressionParser(self.sketch.expression_manager)
        ep.set_identifier_mapping(dict())
        for hole_name, expr in assignments.items():
            constants_map[self.holes[hole_name].expression_variable] = expr

        # logger.debug("construct instance")
        instance = self.sketch.define_constants(constants_map).substitute_constants()
        # logger.debug("constructed instance")
        return instance