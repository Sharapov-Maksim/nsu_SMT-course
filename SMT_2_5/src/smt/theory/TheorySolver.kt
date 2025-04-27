package smt.theory

interface TheorySolver {


    companion object {
        const val EMPTY_LOGIC = ""

    }

    /**
     * Solve the theory.
     *
     * @return true if theory is satisfiable.
     */
    fun solve(): Boolean

    fun getModel(): Model

}