package smt

import smt.theory.Sort
import smt.theory.Type
import smt.theory.TypeRDL
import smt.theory.rdl.TheorySolverRDL
import smt.theory.uf.TheorySolverUF
import java.util.Objects


class Environment {

    private var solverRDL: TheorySolverRDL? = null
    private var solverUF: TheorySolverUF? = null

    fun createSolverRDL() {
        if (solverRDL != null) {
            throw IllegalStateException("Solver of RDL theory already exists")
        }
        solverRDL = TheorySolverRDL()
    }

    fun createSolverUF() {
        if (solverUF != null) {
            throw IllegalStateException("Solver of UF theory already exists")
        }
        solverUF = TheorySolverUF()
    }

    fun solverRDL() = solverRDL ?: throw IllegalStateException("Solver of RDL theory does not exist")
    fun solverUF() = solverUF ?: throw IllegalStateException("Solver of UF theory does not exist")

}


