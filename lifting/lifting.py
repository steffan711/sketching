
import sys
import logging
import click
import os
import time

from familychecker import LiftingChecker,AllInOneChecker,OneByOneChecker,ConsistentSchedChecker,SmtChecker,FamilyCheckMethod

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

@click.command()
@click.option('--project', help="root", required=True)
@click.option('--sketch', help="the sketch", required=True)
@click.option('--allowed', help="for each hole the options", required=True)
@click.option('--property', help="the properties", required=True)
@click.option("--constants", default="")
@click.argument("method",  type=click.Choice(['lift', 'cschedenum', 'allinone', 'onebyone', 'smt']))
def lifting(project, sketch, allowed, property, constants, method):
    approach = FamilyCheckMethod.from_string(method)
    assert approach is not None

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
    else:
        assert None

    sketch_path = os.path.join(project, sketch)
    allowed_path = os.path.join(project, allowed)
    property_path = os.path.join(project, property)

    algorithm.load_sketch(sketch_path,property_path, constants)
    algorithm.load_template_definitions(allowed_path)

    start_time = time.time()
    algorithm.run()
    end_time = time.time()
    logger.info("Finished after {} seconds.".format(end_time - start_time))

if __name__ == "__main__":
    setup_logger(None)
    lifting()