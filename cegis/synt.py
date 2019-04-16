import logging


import pickle

import stormpy
import stormpy.utility

from synthesiser import Synthesiser

import click

from z3 import *

logger = logging.getLogger(__name__)




def setup_logger(log_path):
    """
    Setup routine for logging. 
    
    :param log_path: 
    :return: 
    """
    root = logging.getLogger()
    root.setLevel(logging.DEBUG)

    formatter = logging.Formatter('%(asctime)s %(threadName)s - %(name)s - %(levelname)s - %(message)s')

    handlers = []
    if log_path:
        fh = logging.FileHandler(log_path)
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(formatter)
        handlers.append(fh)
    ch = logging.StreamHandler(sys.stdout)
    handlers.append(ch)
    ch.setLevel(logging.DEBUG)
    ch.setFormatter(formatter)
    for h in handlers:
        root.addHandler(h)
    return handlers

def reset_handlers(handlers):
    for h in handlers:
        logging.getLogger().removeHandler(h)


def store_stats(path, synt_stats, verif_stats, constants, description=""):
    logger.debug("Storing stats...")
    pickle.dump((synt_stats, verif_stats, constants, description), open(path, "wb"))
    logger.info("Stored stats at {}".format(path))


@click.command()
@click.option('--project', help="root")
@click.option('--sketch', help="the sketch")
@click.option('--allowed', help="for each hole the options")
@click.option('--restrictions', help="restrictions")
@click.option('--optimality', help="optimality criterion")
@click.option('--properties', help="the properties")
@click.option('--check-prerequisites', default=False, help="should prerequisites be checked")
@click.option('--backward-cuts', default=1, type=int, help="switch off backward cuts")
@click.option("--threads", type=int, default=1)
@click.option("--constants", default="")
@click.option("--stats", default="stats.out")
def cli_synthesise(project, sketch, allowed, restrictions, optimality, properties, check_prerequisites, backward_cuts, threads, constants, stats):
    synthethise(project, sketch, allowed, restrictions, optimality, properties, check_prerequisites, backward_cuts, threads, constants, stats)

def synthethise(project, sketch, allowed, restrictions, optimality, properties, check_prerequisites, backward_cuts, threads, constants, stats):
    #stormpy.core._set_loglevel_trace()

    synthesiser = Synthesiser(to_jani=True, threads=threads, check_prerequisites=check_prerequisites, add_cuts=backward_cuts)
    sketch_path = os.path.join(project, sketch)
    allowed_path = os.path.join(project, allowed)
    restriction_path = os.path.join(project, restrictions)
    property_path = os.path.join(project, properties)

    synthesiser.load_sketch(sketch_path, property_path, constants, as_jani=False)
    synthesiser.load_template_definitions(allowed_path)
    synthesiser.load_restrictions(restriction_path)
    if optimality:
        optimality_path = os.path.join(project, optimality)
        synthesiser.load_optimality(optimality_path)


    synthesiser.initialize_synthesis()


    result = synthesiser.run(all_conflicts=True)
    if result is not None:
        print("Satisfiable!")
        #print(synthesiser.build_instance(result))
    else:
        print("Unsatisfiable!")

    print("Iterations: {} ({} s), Qualitative Iterations {}/{}".format(synthesiser.stats.iterations, synthesiser.stats.total_time, synthesiser.stats.qualitative_iterations, synthesiser.stats.iterations))
    print("Non-trivial counterexamples: {}".format(synthesiser.stats.non_trivial_cex))
    print("Model Building Calls: {} ({} s)".format(synthesiser.verifier_stats.model_building_calls, synthesiser.verifier_stats.model_building_time))
    print("Synthethiser Analysis: {} = {} + {} s".format(synthesiser.stats.total_solver_time, synthesiser.stats.total_solver_analysis_time, synthesiser.stats.total_solver_clause_adding_time))
    print("Conflict analyses Calls: {} ({} s)".format(synthesiser.verifier_stats.conflict_analysis_calls, synthesiser.verifier_stats.conflict_analysis_time))
    print("Qualitative Model Checking Calls: {} ({} s)".format(synthesiser.verifier_stats.qualitative_model_checking_calls, synthesiser.verifier_stats.qualitative_model_checking_time))
    print("Quantitative Model Checking Calls: {} ({} s)".format(synthesiser.verifier_stats.quantitative_model_checking_calls, synthesiser.verifier_stats.quantitative_model_checking_time))

    print("CA/Iterations: {}".format(synthesiser.verifier_stats.total_conflict_analysis_iterations))
    print("CA/SMT solving: {} s".format(synthesiser.verifier_stats.total_conflict_analysis_solver_time))
    print("CA/Analysis: {} s".format(synthesiser.verifier_stats.total_conflict_analysis_analysis_time))
    print("CA/MC: {} s".format(synthesiser.verifier_stats.total_conflict_analysis_mc_time))
    print("CA/Setup: {} s".format(synthesiser.verifier_stats.total_conflict_analysis_setup_time))
    print("CA/Cuts: {} s".format(synthesiser.verifier_stats.total_conflict_analysis_cut_time))

    #print("Learned clauses: {}".format(",".join([str(c) for c in synthesiser.stats.learned_clauses])))
    #print(synthesiser.sketch)

    synthesiser.verifier_stats.print_property_stats()
    description = "-".join([str(x) for x in [project,sketch,allowed,restrictions,optimality,properties,check_prerequisites,backward_cuts,"sat" if result is not None else "unsat"]])

    store_stats(stats, synthesiser.stats, synthesiser.verifier_stats, constants, description)





if __name__ == '__main__':
    setup_logger("cegis.log")
    cli_synthesise()