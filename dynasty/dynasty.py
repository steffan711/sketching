import sys
import logging
import pickle
import click
import os
import time

from familychecker import LiftingChecker,AllInOneChecker,OneByOneChecker,ConsistentSchedChecker,SmtChecker,FamilyCheckMethod
from synthesiser import Synthesiser

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

def dump_stats_to_file(path, keyword, constants, description, *args):
    logger.debug("Storing stats...")
    pickle.dump((keyword,constants, description,*args), open(path, "wb"))
    logger.info("Stored stats at {}".format(path))


@click.command()
@click.option('--project', help="root", required=True)
@click.option('--sketch', help="the sketch", required=True)
@click.option('--allowed', help="for each hole the options", required=True)
@click.option('--properties', help="the properties", required=True)
@click.option('--optimality', help="optimality criterion")
@click.option('--restrictions', help="restrictions")
@click.option("--constants", default="")
@click.option("--stats", default="stats.out")
@click.option('--check-prerequisites', default=False, help="should prerequisites be checked")
@click.argument("method",  type=click.Choice(['lift', 'cschedenum', 'allinone', 'onebyone', 'smt', 'cegis']))
def dynasty(project, sketch, allowed, properties, optimality, restrictions, constants, stats, check_prerequisites, method):
    approach = FamilyCheckMethod.from_string(method)
    assert approach is not None
    backward_cuts = 1 # Only used for cegis.

    if approach == FamilyCheckMethod.Lifting:
        algorithm = LiftingChecker()
    elif approach == FamilyCheckMethod.AllInOne:
        algorithm = AllInOneChecker()
    elif approach == FamilyCheckMethod.DtmcIteration:
        algorithm = OneByOneChecker()
    elif approach == FamilyCheckMethod.SchedulerIteration:
        algorithm = ConsistentSchedChecker()
    elif approach == FamilyCheckMethod.SMT:
        algorithm = SmtChecker()
    elif approach == FamilyCheckMethod.CEGIS:
        algorithm = Synthesiser(to_jani=True, threads=1, check_prerequisites=check_prerequisites,
                              add_cuts=backward_cuts)
    else:
        assert None


    sketch_path = os.path.join(project, sketch)
    allowed_path = os.path.join(project, allowed)
    if restrictions:
        restriction_path = os.path.join(project, restrictions)
    property_path = os.path.join(project, properties)

    algorithm.load_sketch(sketch_path, property_path, constants)
    algorithm.load_template_definitions(allowed_path)
    if restrictions:
        algorithm.load_restrictions(restriction_path)
    if optimality:
        optimality_path = os.path.join(project, optimality)
        algorithm.load_optimality(optimality_path)
    algorithm.initialise()

    start_time = time.time()
    result = algorithm.run()
    end_time = time.time()

    if result is not None:
        sat, solution = result
        if sat:
            print("Satisfiable!")
            # print(algorithm.build_instance(solution))
        else:
            print("Unsatisfiable!")
    else:
        print("Solver finished without a result provided.")


    logger.info("Finished after {} seconds.".format(end_time - start_time))

    algorithm.print_stats()

    description = "-".join([str(x) for x in
                            [project, sketch, allowed, restrictions, optimality, properties, check_prerequisites,
                             backward_cuts, "sat" if result is not None else "unsat"]])
    dump_stats_to_file(stats, algorithm.stats_keyword, constants, description, algorithm.store_in_statistics())

if __name__ == "__main__":
    setup_logger("dynasty.log")
    dynasty()