Dynasty
=================================================

This project contains prototypical implementations of synthesis in probabilistic program sketches.

It contains algorithms based on:
- Milan Ceska, Christian Hensel, Sebastian Junges, Joost-Pieter Katoen: Counterexample-Driven Synthesis for Probabilistic Program Sketches, FM 2019
- Milan Ceska, Nils Jansen, Sebastian Junges, Joost-Pieter Katoen: Shepherding Hordes of Markov chains, TACAS 2019

The code has been developed by Sebastian Junges.
More information can be found in his PhD thesis.

## Dependencies

- Python bindings for [z3](https://github.com/Z3Prover/z3)
- The model checker storm and the python bindings for storm. Please check the [installation hints](https://moves-rwth.github.io/stormpy/installation.html#installation-steps).
- The python packages
  * click
  * pysmt


## Usage examples

We support three types of problems
 - Feasibility Analysis (and its dual, validity analysis)
 - Optimal Feasibility Analysis
 - Partitioning (or Threshold analysis)

### Project folders

TODO description

### Feasibility Analysis

#### CEGIS
```
python dynasty.py --project examples/virus/ --sketch virus.templ --constants CMAX=0,T=18.0 --allowed virus.allowed --restrictions virus.restrictions  --properties virus.properties
```
```
python dynasty.py --project examples/grid/ --sketch 4x4grid_sl.templ --constants CMAX=11,T_EXP=10.0,T_SLOW=10.0,T_FAST=0.9 --allowed 4x4grid_sl.allowed --restrictions 4x4grid_sl.restrictions  --properties single.properties 
```
```
python dynasty.py --project examples/grid/ --sketch 4x4grid_sl.templ --constants CMAX=1,T_EXP=10.0,T_SLOW=10.0,T_FAST=0.9 --allowed 4x4grid_sl.allowed --restrictions 4x4grid_sl.restrictions  --properties reward.properties --check-prerequisites True
```

#### Lifting
```bash
python dynasty.py --project examples/grid/ --sketch 4x4grid_sl.templ --properties reward.properties --constants "CMAX=400,T_EXP=7.7,T_FAST=0.6,T_SLOW=0.995" --allowed 4x4grid_sl.allowed lift
```

#### Scheduler enumeration
```bash
python dynasty.py --project examples/grid/ --sketch 4x4grid_sl.templ --properties reward.properties --constants "CMAX=400,T_EXP=7.7,T_FAST=0.6,T_SLOW=0.995" --allowed 4x4grid_sl.allowed cschedenum
```

Notice: The CMAX generally reflects blowing up the state space. For the grid examples, it should however be choosen larger than the counters in the properties.
One may omit the check prerequisites if the sketch already ensures that all rewards are less than infinity.


#### All other approaches

TODO

### Optimal Feasibility Analysis

#### CEGIS

TODO description
```bash
python dynasty.py --project examples/grid/ --sketch 4x4grid_sl.templ --constants CMAX=11,T_EXP=10.0,T_SLOW=10.0,T_FAST=0.7 --allowed 4x4grid_sl.allowed --restrictions 4x4grid_sl.restrictions  --optimality fast_to_target.optimal --properties none.properties cegis
```

#### Lifting

TODO


### Partitioning 
This problem is also known as threshold synthesis.
It aims to partition the set of instantiations into a set of accepting 
instantiations, i.e., instantiations that satisfy the property at hand,
and rejecting instantiations, i.e., instantiations that do not satisfy the property at hand.

In general, partitioning can be enabled by adding a switch `--partitioning`. Notice that this switch
cannot be combined with `--optimality`.

#### CEGIS

Currently has no working implementation for this type of analysis.

#### Lifting

TODO: Description

```bash
python --project examples/grid/ --sketch 4x4grid_sl.templ --constants CMAX=11,T_EXP=10.0,T_SLOW=10.0,T_FAST=0.9 --allowed 4x4grid_sl.allowed --restrictions 4x4grid_sl.restrictions  --properties single.properties --partitioning lift
```

#### Scheduler enumeration

TODO: Descritption

#### All other approaches

TODO: Description