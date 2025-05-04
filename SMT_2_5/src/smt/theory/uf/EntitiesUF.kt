package smt.theory.uf

import smt.theory.Sort
import smt.theory.Type
import java.util.*


data class UninterpretedFunction(val name: String, val args: List<Type>, val result: Type) {
    override fun toString(): String {
        return "Function (\"$name\" $args -> $result)"
    }
}

open class Term {

    open class FunctionApplication(open val args: List<Term>): Term() {
        override fun equals(other: Any?): Boolean {
            if (other !is FunctionApplication) {
                return false
            }
            return args == other.args
        }

        override fun hashCode(): Int {
            return Objects.hash(args)
        }
    }

    class NamedFunctionApplication(
        val f: UninterpretedFunction,
        override val args: List<Term>): FunctionApplication(args) {

        override fun equals(other: Any?): Boolean {
            if (other !is NamedFunctionApplication) {
                return false
            }
            if (this.f != other.f) {
                return false
            }
            return super.equals(other)
        }

        override fun hashCode(): Int {
            return Objects.hash(f, super.hashCode())
        }

    }

    class EqualityFunctionApplication private constructor(val isEqual: Boolean, override val args: List<Term>): FunctionApplication(args) {

        override fun equals(other: Any?): Boolean {
            if (!(other is EqualityFunctionApplication)) {
                return false
            }
            if (this.isEqual != other.isEqual) {
                return false
            }
            return super.equals(other)
        }

        override fun hashCode(): Int {
            return Objects.hash(isEqual, super.hashCode())
        }

        companion object {
            fun create(isEqual: Boolean, args: List<Term>): EqualityFunctionApplication {
                if (args.size != 2) {
                    throw IllegalArgumentException("Wrong ${ if (isEqual) "equality" else "inequality" } args $args")
                }
                return EqualityFunctionApplication(isEqual, args)
            }
        }
    }


}

