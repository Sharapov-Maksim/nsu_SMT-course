package smt.theory.rdl

import smt.theory.Model

data class ModelRDL(val variableValues: Map<Variable, Double>): Model