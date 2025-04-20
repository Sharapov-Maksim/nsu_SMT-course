package smt

import smt.theory.Sort
import smt.theory.Type
import smt.theory.TypeRDL
import smt.theory.rdl.TheorySolverRDL
import java.util.Objects


class Environment {

    private var solverRDL: TheorySolverRDL? = null

    fun createSolverRDL() {
        if (solverRDL != null) {
            throw IllegalStateException("Solver of RDL theory already exists")
        }
        solverRDL = TheorySolverRDL()
    }

    fun solverRDL() = solverRDL ?: throw IllegalStateException("Solver of RDL theory does not exist")

}


