package smt

import smt.theory.Sort
import smt.theory.Theory
import smt.theory.Type
import smt.theory.TypeRDL
import smt.theory.rdl.TheorySolverRDL
import smt.theory.uf.TheorySolverUF
import smt.theory.ufrdl.TheorySolverUFRDL
import java.util.Objects


class Environment {

    public var theory: Theory = Theory.NONE
    private var solverRDL: TheorySolverRDL? = null
    private var solverUF: TheorySolverUF? = null
    private var solverUFRDL: TheorySolverUFRDL? = null

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

    fun createSolverUFRDL(uf: TheorySolverUF, rdl: TheorySolverRDL) {
        if (solverUFRDL != null) {
            throw IllegalStateException("Solver of UFRDL theory already exists")
        }
        solverUFRDL = TheorySolverUFRDL(uf, rdl)
    }

    fun solverRDL() = solverRDL ?: throw IllegalStateException("Solver of RDL theory does not exist")
    fun solverUF() = solverUF ?: throw IllegalStateException("Solver of UF theory does not exist")
    fun solverUFRDL() = solverUFRDL ?: throw IllegalStateException("Solver of UFRDL theory does not exist")

}


