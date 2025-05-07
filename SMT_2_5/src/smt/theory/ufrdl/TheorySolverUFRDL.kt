package smt.theory.ufrdl

import smt.DEBUG_LOG
import smt.rdl
import smt.theory.Model
import smt.theory.Real
import smt.theory.TheorySolver
import smt.theory.rdl.*
import smt.theory.rdl.TheorySolverRDL.ConstraintGraph
import smt.theory.rdl.TheorySolverRDL.ConstraintGraph.Node
import smt.theory.uf.Term
import smt.theory.uf.TheorySolverUF
import smt.theory.uf.UninterpretedFunction
import smt.uf
import kotlin.math.max

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

    override fun getModel(): ModelUFRDL {
        assert(rdl().searchResult != null)
        val delta = rdl().searchResult!!.d
        val rdlG = rdl().graph!!
        assert(rdl().inducedGraph != null)
        val componentsRaw = ConstraintGraph.SCC.search(rdl().inducedGraph!!)
        val components = componentsRaw.keys.groupBy { componentsRaw.getValue(it) }
        val sccGraph = ConstraintGraph.SCCGraph()
        for ((id, comp) in components) {
            sccGraph.addNode(comp.toSet(), id)
        }
        val sccMap: MutableMap<Node, ConstraintGraph.SCCGraph.SCCNode> = mutableMapOf()
        for (node in rdlG.nodes().values) {
            val sccFiltered =
                sccGraph.nodes.values.filter { sccNode: ConstraintGraph.SCCGraph.SCCNode ->
                    sccNode.component.contains(node)
                }
            assert(sccFiltered.size == 1)
            val scc = sccFiltered.first()
            sccMap[node] = scc
        }
        for (edge in rdlG.edges()) {
            sccGraph.addEdge(sccMap.getValue(edge.from), sccMap.getValue(edge.to))
        }
        if (DEBUG_LOG) {
            println("SCC Graph: $sccGraph")
        }
        val sccSorted = sccGraph.topsort()
        if (DEBUG_LOG) {
            println("   Topsort: $sccSorted")
        }

        // build "not-equivalent" relation on SCC-graph
        val neqRelation: MutableMap<ConstraintGraph.SCCGraph.SCCNode, MutableSet<ConstraintGraph.SCCGraph.SCCNode>> =
            mutableMapOf()
        uf().assertsCongruenceClosure()

        sccSorted.forEach{ neqRelation.putIfAbsent(it, mutableSetOf()) }

        for ((x, y) in uf().variableInequalityPairs()) {
            val xvar = rdl().variables().getValue(x.name)
            val yvar = rdl().variables().getValue(y.name)
            val xnode = rdl().graph!!.nodes().getValue(xvar)
            val ynode = rdl().graph!!.nodes().getValue(yvar)
            val xSCC = sccMap.getValue(xnode)
            val ySCC = sccMap.getValue(ynode)
            neqRelation.getValue(xSCC) += ySCC
            neqRelation.getValue(ySCC) += xSCC
        }
        if (DEBUG_LOG) {
            println("   Neq relation: $neqRelation")
        }

        // model generation algorithm
        var deltaPatched = delta
        var epsilon = findEpsilon(rdlG) // (i)
        /*if (DEBUG_LOG) {
            println("   epsilon: $epsilon")
        }*/
        if (epsilon != Double.MAX_VALUE) {
            val gamma = sccGraph.nodes.values.associateWith { 0.0 }.toMutableMap() // (ii)
            for (S in sccSorted) { // (iii)
                // (a)
                if (sccSorted.any { (neqRelation.getValue(it).contains(S)) && (gamma.getValue(S) == gamma.getValue(it)) }) {
                    gamma[S] = gamma[S]!! + epsilon/2
                    epsilon /= 2
                }
                // (b)
                sccGraph.edges.forEach { sccEdge: ConstraintGraph.SCCGraph.SCCEdge ->
                    val S = sccEdge.from
                    val U = sccEdge.to
                    gamma[U] = max(gamma[U]!!, gamma[S]!!)
                }
            }

            // (iv) new values for variables according to UF and RDL constraints
            deltaPatched = delta.mapValues { (node, d) -> d - gamma.getValue(sccMap.getValue(node)) }
        } else {
            assert(uf().variableInequalityPairs().isEmpty())
        }

        val d = deltaPatched.mapKeys { (node, _) -> node.variable }
        val assignmentRDL: MutableMap<Variable, Double> = mutableMapOf()

        rdl.variables().values.forEach { variable: Variable ->
            val variableValue: Double
            if (d.getValue(variable) == 0.0) {
                variableValue = 0.0
            } else {
                variableValue = -1 * d.getValue(variable)
            }
            assignmentRDL[variable] = variableValue
        }

        val model = uf().getModel(assignmentRDL)
        if (DEBUG_LOG) {
            println("Model: $model")
        }
        return model
    }

    /**
     * TODO discuss a problem if x != y, x-y<=0, d(x)==0, d(y)==0
     */
    private fun findEpsilon(rdlG: ConstraintGraph): Double {
        var min = Double.MAX_VALUE
        val delta = rdl.searchResult?.d!!
        for (x in delta.keys) {
            for (y in delta.keys) {
                val dx = delta.getValue(x)
                val dy = delta.getValue(y)
                if (dx != dy) {
                    val a = Math.abs(dx - dy)
                    if (a < min) {
                        min = a
                    }
                }
            }
        }
        for (e in rdlG.edges()) {
            if (rdl.sl(e) != 0.0 && rdl.sl(e) < min) {
                min = rdl.sl(e)
            }
        }
        return min
    }
}