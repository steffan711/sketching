import sys
import logging
import pickle
import click
import os
import time
import click_config_file

from dynasty.family_checkers.familychecker import FamilyCheckMethod
from dynasty.family_checkers.quotientbased import LiftingChecker, AllInOneChecker,OneByOneChecker,ConsistentSchedChecker,SmtChecker
from dynasty.family_checkers.cegis import Synthesiser
from dynasty.family_checkers.smartsearch import SmartSearcher
from dynasty import version

logger = logging.getLogger(__name__)

def setup_logger(log_path, loglevel):
    """
    Setup routine for logging. 

    :param log_path: 
    :return: 
    """
    root = logging.getLogger()
    root.setLevel(loglevel)

    formatter = logging.Formatter('%(asctime)s %(threadName)s - %(name)s - %(levelname)s - %(message)s')

    handlers = []
    if log_path:
        fh = logging.FileHandler(log_path)
        fh.setLevel(loglevel)
        fh.setFormatter(formatter)
        handlers.append(fh)
    ch = logging.StreamHandler(sys.stdout)
    handlers.append(ch)
    ch.setLevel(loglevel)
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
@click.option('--optimize-one', help="number of the optimized property", type=click.IntRange(1))
@click.option('--timeout', help="time limit for evolutionary search in seconds", default=30)
@click.option("--constants", default="")
@click.option("--stats", default="stats.out")
@click.option("--print-stats", is_flag=True)
@click.option('--check-prerequisites', help="should prerequisites be checked", is_flag=True)
@click.option('--partitioning', help="run partitioning instead of feasibility", is_flag=True)
@click.option('-v', '--verbose', count=True)
@click_config_file.configuration_option()
@click.argument("method",  type=click.Choice(['lift', 'cschedenum', 'allinone', 'onebyone', 'smt', 'cegis', 'ea']))
def dynasty(project, sketch, allowed, properties, optimality, optimize_one, timeout, restrictions, constants, stats, print_stats, check_prerequisites, partitioning, verbose, method):
    print("This is Dynasty version {}.".format(version()))
    log(verbose)
    approach = FamilyCheckMethod.from_string(method)
    assert approach is not None
    backward_cuts = 1 # Only used for cegis.

    if optimality:
        if partitioning:
            raise RuntimeError("It does not make sense to combine partitioning and optimality")

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
        algorithm = Synthesiser(threads=1, check_prerequisites=check_prerequisites,
                              add_cuts=backward_cuts)
    elif approach == FamilyCheckMethod.EA:
        algorithm = SmartSearcher(optimize_one, timeout)
    else:
        assert None


    sketch_path = os.path.join(project, sketch)
    allowed_path = os.path.join(project, allowed)
    if restrictions:
        restriction_path = os.path.join(project, restrictions)
    property_path = os.path.join(project, properties)
    if optimality:
        optimality_path = os.path.join(project, optimality)
    else:
        optimality_path = None

    algorithm.load_sketch(sketch_path, property_path, optimality_path=optimality_path, constant_str=constants)
    algorithm.load_template_definitions(allowed_path)
    if restrictions:
        algorithm.load_restrictions(restriction_path)
    algorithm.initialise()

    start_time = time.time()
    if partitioning:
        result = algorithm.run_partitioning()
    else:
        result = algorithm.run_feasibility()
    end_time = time.time()

    if partitioning:
        if result is not None:
            above, below = result
            print("Subfamilies above: ")
            print(above)
        else:
            print("Solver finished without returning a result (probably not implemented).")
    else:
        if result is not None:
            sat, solution, optimal_value = result
            if sat:
                print("Satisfiable!")
                print("using " + ", ".join([str(k) + ": " + str(v) for k,v in solution.items()]))
                if optimal_value is not None:
                    print("and induces a value of {}".format(optimal_value))
                # print(algorithm.build_instance(solution))

            else:
                print("Unsatisfiable!")
        else:
            print("Solver finished without a result provided.")

    logger.info("Finished after {} seconds.".format(end_time - start_time))

    if print_stats:
        algorithm.print_stats()

    description = "-".join([str(x) for x in
                            [project, sketch, allowed, restrictions, optimality, properties, check_prerequisites,
                             backward_cuts, "sat" if result is not None else "unsat"]])
    dump_stats_to_file(stats, algorithm.stats_keyword, constants, description, algorithm.store_in_statistics())

def log(verbosity):
    click.echo('Verbosity: %s' % verbosity)
    base_loglevel = 30
    verbosity = min(verbosity, 2)
    loglevel = base_loglevel - (verbosity * 10)
    setup_logger("dynasty.log", loglevel)

def main():
    dynasty()

if __name__ == "__main__":
    main()
