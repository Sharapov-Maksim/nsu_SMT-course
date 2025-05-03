package smt.theory.ufrdl

import smt.rdl
import smt.theory.Model
import smt.theory.Real
import smt.theory.TheorySolver
import smt.theory.rdl.*
import smt.theory.uf.Term
import smt.theory.uf.TheorySolverUF

/**
 * Theory solver for combination of UF and RDL.
 *
 * @see TheorySolverUF
 * @see TheorySolverRDL
 */
class TheorySolverUFRDL(val uf: TheorySolverUF, val rdl: TheorySolverRDL): TheorySolver {

    var solved = false

    override fun solve(): Boolean {
        // 2. solve UF
        val ufSat = uf.solve()
        if (!ufSat) {
            return false
        }

        val varEqualityClasses = uf.variableEqualityClasses()

        // 2. add variable equalities to RDL theory
        for (eqClass in varEqualityClasses) {
            if (eqClass.size >= 2) {
                addEqualities(eqClass.toList())
            }
        }

        // 3. Solve RDL
        val rdlSat = rdl().solve()
        if (!rdlSat) {
            return false
        }


        TODO("Not yet implemented")
    }

    /**
     * Add all pairs of equalities from equality class.
     */
    private fun addEqualities(cls: List<Term>) {
        if (cls.size < 2) {
            return
        }
        val firstVariable = cls.first()
        if (firstVariable !is Term.NamedFunctionApplication) {
            throw IllegalArgumentException("Equality class with non-variable provided")
        }
        assert(firstVariable.args.isEmpty()) // variable
        val tail = cls.drop(1)

        // add all pairs of variables from tail with first variable
        for (otherVariable in tail) {
            if (otherVariable !is Term.NamedFunctionApplication) {
                throw IllegalArgumentException("Equality class with non-variable provided")
            }
            assert(otherVariable.args.isEmpty()) // variable
            otherVariable.f.name
            val left = VariableApply(UFTermVariableToRDLVariable(firstVariable))
            val right = VariableApply(UFTermVariableToRDLVariable(otherVariable))
            rdl.addAssert(LEQ_Apply(Sub_Apply(left, right), Constant(0.0)))
            rdl.addAssert(LEQ_Apply(Sub_Apply(right, left), Constant(0.0)))
        }

        addEqualities(tail) // recursively add all combinations from tail
    }

    /**
     * Transform UF [Term] of variable to RDL [Variable].
     */
    private fun UFTermVariableToRDLVariable(term: Term): Variable {
        if (term !is Term.NamedFunctionApplication) {
            throw IllegalArgumentException("Provided term is not variable, $term")
        }
        if (term.args.isNotEmpty()) {
            throw IllegalArgumentException("Provided term is not variable, $term")
        }
        return Variable(term.f.name, Real)
    }

    override fun getModel(): Model {
        TODO("Not yet implemented")
    }
}