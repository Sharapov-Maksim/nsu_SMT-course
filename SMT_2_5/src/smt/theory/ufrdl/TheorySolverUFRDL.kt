package smt.theory.ufrdl

import smt.theory.Model
import smt.theory.TheorySolver
import smt.theory.rdl.TheorySolverRDL
import smt.theory.uf.Term
import smt.theory.uf.TheorySolverUF

class TheorySolverUFRDL(val uf: TheorySolverUF, rdl: TheorySolverRDL): TheorySolver {
    override fun solve(): Boolean {
        // 2.
        val ufSat = uf.solve()
        if (!ufSat) {
            return false
        }

        val varEqualityClasses = uf.variableEqualityClasses()

        for (eqClass in varEqualityClasses) {
            if (eqClass.size >= 2) {

            }
        }

        TODO("Not yet implemented")
    }

    fun addEqualities(cls: List<Term>) {
        val first = cls.first()
    }

    override fun getModel(): Model {
        TODO("Not yet implemented")
    }
}