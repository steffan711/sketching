# Counterexample Guided Inductive Synthesis on MDPs

This project contains a prototypical implementation of graph-parameter synthesis via counterexamples.

It is largely based on:
- Milan Ceska, Christian Hensel, Sebastian Junges, Joost-Pieter Katoen: Counterexample-Driven Synthesis for Probabilistic Program Sketches

The code has been mostly developed by Sebastian Junges. 
Please do not hesitate to contact us in case of questions.

### Requirements

- [Stormpy](https://moves-rwth.github.io/stormpy/): The python bindings for Storm in an up-to-date version. 
- The SMT-solver z3 with its python bindings
- Furthermore, standard python dependencies:  pip install click

### Usage examples

- python cegis/synt.py --project examples/virus/ --sketch virus.templ --constants CMAX=0,T=18.0 --allowed virus.allowed --restrictions virus.restrictions  --properties virus.properties
- python cegis/synt.py--project examples/grid/ --sketch 4x4grid_sl.templ --constants CMAX=11,T_EXP=10.0,T_SLOW=10.0,T_FAST=0.9 --allowed 4x4grid_sl.allowed --restrictions 4x4grid_sl.restrictions  --properties single.properties 
- python cegis/synt.py--project examples/grid/ --sketch 4x4grid_sl.templ --constants CMAX=1,T_EXP=10.0,T_SLOW=10.0,T_FAST=0.9 --allowed 4x4grid_sl.allowed --restrictions 4x4grid_sl.restrictions  --properties reward.properties --check-prerequisites True

Notice: The CMAX generally reflects blowing up the state space. For the grid examples, it should however be choosen larger than the counters in the properties.
One may omit the check prerequisites if the sketch already ensures that all rewards are less than infinity.

### Navigation
- Entry point is synt.py
- The synthesiser is located in synthesiser.py
- The verifier is located in verifier.py
