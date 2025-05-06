package smt.theory.uf

class GraphColoring {

    companion object {
        val COLOR_FIRST = ColorUnique(0)
    }

    interface Color

    data object ColorUnknown: Color
    data class ColorUnique(val id: Int): Color
    data class ColorPredefined(val value: Double): Color

    class Graph {

        /**
         * The graph itself represented as map from node id to node.
         */
        private val nodes: MutableMap<Int, Node> = mutableMapOf()

        data class Node(val id: Int, val edges: MutableSet<Node>) {
            var color: Color = ColorUnknown
        }

        fun addNode(id: Int) {
            assert(!nodes.containsKey(id)) // check that no node with given id exists in graph
            nodes[id] = Node(id, mutableSetOf())
        }

        fun addEdge(id0: Int, id1: Int) {
            assert(nodes.containsKey(id0))
            assert(nodes.containsKey(id1))
            nodes.getValue(id0).edges.add(nodes.getValue(id1))
            nodes.getValue(id1).edges.add(nodes.getValue(id0))
        }

        /**
         * Colors graph and returns coloring in map(id -> color)
         */
        fun color(): Map<Int, Color> {
            for (colorsCount in 1..nodes.values.filter { it.color !is ColorPredefined }.size) {
                if (colorSubgraph(0, colorsCount-1)) {
                    // graph is successfully colored
                    return nodes.mapValues { (id, node) -> node.color }.toMap()
                }
            }
            throw IllegalStateException("Could not find a coloring for graph $nodes")
        }

        private fun colorSubgraph(currentId: Int, maximalColor: Int): Boolean {
            if (currentId >= nodes.size) {
                return true
            }

            val predefinedColors = nodes.values.map { it.color }.filterIsInstance<ColorPredefined>().toSet()
            val node = nodes.getValue(currentId)

            if (node.color is ColorPredefined) {
                if (colorSubgraph(currentId + 1, maximalColor)) {
                    return true
                }
            } else {
                // try to use predefined colors first
                for (c in predefinedColors) {
                    if (isSafeToColor(node, c)) {
                        node.color = c
                        if (colorSubgraph(currentId + 1, maximalColor)) {
                            return true
                        }
                        node.color = ColorUnknown // backtrack
                    }
                }
                // make new colors if needed
                for (c in COLOR_FIRST.id..maximalColor) {
                     if (isSafeToColor(node, ColorUnique(c))) {
                        node.color = ColorUnique(c)
                        if (colorSubgraph(currentId + 1, maximalColor)) {
                            return true
                        }
                        node.color = ColorUnknown // backtrack
                    }
                }
            }

            return false
        }

        private fun isSafeToColor(node: Node, color: Color): Boolean {
            assert(node.color !is ColorPredefined)
            return !node.edges.map { n -> n.color }.toSet().contains(color)
        }

    }



}