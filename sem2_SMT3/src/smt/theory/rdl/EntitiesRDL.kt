package smt.theory.rdl

import smt.theory.TypeRDL

/**
 * Abstract function defined with `declare-fun`.
 */
data class Variable(val name: String, val result: TypeRDL) {
    override fun toString(): String {
        return "Var($name)"
    }
}


/**
 * Application of some function. Used to construct expressions in RDL theory.
 */
interface ExpressionReal

data class Constant(val value: Double): ExpressionReal

data class VariableApply(val variableDefinition: Variable): ExpressionReal

abstract class BinaryApply (
    val name: String,
    open val left: ExpressionReal,
    open val right: ExpressionReal): ExpressionReal

data class LEQ_Apply(override val left: ExpressionReal, override val right: ExpressionReal):
    BinaryApply("<=", left, right)

data class Sub_Apply(override val left: ExpressionReal, override val right: ExpressionReal):
    BinaryApply("-", left, right)