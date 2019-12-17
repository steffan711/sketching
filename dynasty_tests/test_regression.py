import os.path
import pytest
import logging
import click.testing

import dynasty
import dynasty.cli
logger = logging.getLogger(__name__)

benchmarks_feasibility = [
    pytest.param("examples/grid", "4x4grid_sl.templ", "CMAX=11,T_EXP=10.0,T_SLOW=10.0,T_FAST=0.7", "4x4grid_sl.allowed", "single.properties",  "none.restrictions", "lift"),
   # pytest.param("grid", "4x4grid_sl.templ", "", "property1", "prism"),
   # pytest.param("brp", "brp", "N=16,MAX=2", "property1", "stormpy", marks=[require_stormpy()]),
]

@pytest.mark.parametrize("project,sketch,constants,allowed,properties,restrictions,method", benchmarks_feasibility)
def test_feasibility_script(project, sketch, constants, allowed, properties, restrictions, method):
    command = ["--project",
               project,
               "--sketch",
               sketch,
               "--constants",
               constants,
               "--allowed",
               allowed,
               "--properties",
               properties,
               "--restrictions",
               restrictions,
               method
               ]
    dynasty.cli.setup_logger("dynasty_tests.log")
    runner = click.testing.CliRunner()
    logger.debug("dynasty.py " + " ".join(command))
    result = runner.invoke(dynasty.cli.dynasty, command)
    assert result.exit_code == 0, result.output
#    assert os.path.isfile(target_file)
#    os.remove(target_file)
