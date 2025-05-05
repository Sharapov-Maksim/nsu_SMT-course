package smt.theory.ufrdl

import smt.rdl
import smt.theory.Model
import smt.theory.Real
import smt.theory.TheorySolver
import smt.theory.rdl.*
import smt.theory.uf.Term
import smt.theory.uf.TheorySolverUF
import smt.theory.uf.UninterpretedFunction
import smt.uf

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
                addEqualitiesRDL(eqClass.toList())
            }
        }

        // 3. Solve RDL, add equalities to UF
        val rdlSat = rdl.solve()
        if (!rdlSat) {
            return false
        }
        val equalVariablesSets = rdl().getEqualVariables()
        for (eqClass in equalVariablesSets) {
            if (eqClass.size >= 2) {
                addEqualitiesUF(eqClass.toList())
            }
        }

        // 4. Solve UF again
        return uf.solve()
    }

    /**
     * Add all pairs of equalities from equality class.
     */
    private fun addEqualitiesRDL(cls: List<Term>) {
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

        addEqualitiesRDL(tail) // recursively add all combinations from tail
    }

    public fun addEqualitiesUF(cls: List<Variable>) {
        if (cls.size < 2) {
            return
        }


        val firstVariable = cls.first()
        val tail = cls.drop(1)

        // add all pairs of variables from tail with first variable
        for (otherVariable in tail) {
            val left = Term.NamedFunctionApplication(term(firstVariable), emptyList())
            val right = Term.NamedFunctionApplication(term(otherVariable), emptyList())
            val eq = Term.EqualityFunctionApplication.create(true, listOf(left, right))
            uf.addAssert(eq)
        }

        addEqualitiesUF(tail) // recursively add all combinations from tail
    }

    fun term(variable: Variable): UninterpretedFunction = uf().getFunction(variable.name)


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