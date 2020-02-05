Dynasty
=================================================
[![Build Status](https://travis-ci.org/moves-rwth/dynasty.svg?branch=master)](https://travis-ci.org/moves-rwth/dynasty)

This project contains prototypical implementations of synthesis in probabilistic program sketches.

It contains algorithms based on:
- [1] Milan Ceska, Christian Hensel, Sebastian Junges, Joost-Pieter Katoen: Counterexample-Driven Synthesis for Probabilistic Program Sketches, FM 2019
- [2] Milan Ceska, Nils Jansen, Sebastian Junges, Joost-Pieter Katoen: Shepherding Hordes of Markov chains, TACAS 2019

The code has been developed by Sebastian Junges.
More information can be found in his PhD thesis.

## Installation

### Dependencies

- Python bindings for [z3](https://github.com/Z3Prover/z3)
- The model checker storm and the python bindings for storm. Please check the [installation hints](https://moves-rwth.github.io/stormpy/installation.html#installation-steps).
- The python packages
  * click
  * pysmt

### Install

First, run: 

```
python setup.py install
```

This will automatically install dynasty and its python dependencies. Notice that you have to install storm yourself (see above).
If you are planning on making changes to the code, we suggest to use `python setup.py develop`

To run the tests, run:
```
python -m pytest dynasty_tests
```


### Docker container

Coming soon.

## Usage examples

We support three types of problems
 - Feasibility Analysis (and its dual, validity analysis)
 - Optimal Feasibility Analysis
 - Partitioning (or Threshold analysis)
 
We support three methods:
 - CEGIS [1]
 - Lifting [2]
 - (Consistent) Scheduler enumeration [2]
 
and have experimental code support for (rapid) one-by-one, all-in-one, and SMT-based synthesis. 

As input, we take projects. Below, we first explain what a project is, and then discuss the different analysis types and how to invoke the different methods for these problems. For details about the methods, we refer to publications. 

### Input: Project folders

A project is a folder containing the various inputs for the synthesis. 

We require:
- A .templ file, which is a PRISM file with various open integer constants (holes).
- A .allowed file, which lists for each hole the possible values. The instantiations are the Cartesean product of these files.
- A .properties file, which contains a list of PCTL formulae.

Optionally, a project may contain: 
- A .restrictions file, which contains restrictions on the intstantiations. Restrictions are currently only supported by CEGIS.
- A .optimality file, which contains a PCTL formula, a direction, and a relative precision. This file is relevant for optimal feasibility.

Notice that a project may contain more files than necessary, e.g., to allow for slight variations without duplicating everything.

For more information, look at the [examples](examples/)

### Feasibility Analysis

This problem tries to find an instantiation of the holes such that the induced program satisfies the properties.
All methods provided here are complete, e.g., if the there is no feasible instantiation, the algorithms eventually report so.

Notice that one has to be careful about potentially ill-formed sketches. The checks performed are not necessarily sufficient.

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

### Further Options

- `--check-prerequisites`/`--no-check-prerequiites` 
One may omit the check prerequisites if the sketch already ensures that all rewards are less than infinity.

- `--print-stats` 
Print statistics at the end. Helpful to understand the algorithm performance, but clutters output. 

## The sources
