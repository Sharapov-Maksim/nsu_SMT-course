package smt.theory

interface Type

interface TypeRDL: Type
interface TypeUF: Type


/**
 * Used in QF_RDL.
 */
object Real: TypeRDL

/**
 * Technical type.
 */
object Void: TypeRDL

/**
 * Used in QF_UF. As a type for uninterpreted functions.
 */
data class Sort(val name: String, val num: Int): TypeUF {

    override fun toString(): String {
        return "Sort($name)"
    }
}