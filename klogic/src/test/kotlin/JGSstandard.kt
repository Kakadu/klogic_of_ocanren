@file:Suppress("SpellCheckingInspection")

import org.jgrapht.Graph
import org.jgrapht.graph.DefaultEdge
import org.jgrapht.graph.DirectedAcyclicGraph
import org.jgrapht.traverse.TopologicalOrderIterator
import org.jgs.classtable.ClassesTable
import org.jgs.classtable.EmptyClassTable
import org.jgs.classtable.extractClassesTable
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.reified
import utils.JGS.*
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import kotlin.system.measureTimeMillis

class JGSstandard {

    fun checkClassTable(ct: ClassesTable) {
        val nameToId = mutableMapOf<Int,String>()
        for ( (typ,id) in ct.classNames) {
            if (nameToId.containsKey(id))
                TODO("FUCK")
            else
                nameToId.put(id, typ.simpleName)
        }
    }

    @Test
    @DisplayName("asasdf")
    fun test0() {
        var ct: ClassesTable =  extractClassesTable()
//        for ((k,v) in ct.table.toSortedMap())
//            println("$k -> $v")
        println("${ct.table[1]} ")
        println("${ct.table[2]} ")
        println("${ct.table[3]} ")
        checkClassTable(ct)
    }
    @Test
    @DisplayName("111")
    fun test1() {
        var ct : ClassesTable
        println (measureTimeMillis {
            ct = extractClassesTable()
        })

        val directedGraph: Graph<Int, DefaultEdge> =
            DirectedAcyclicGraph(DefaultEdge::class.java)

        fun addEdge(from: Int, to: Class_<LogicInt>) {
            if (from == to.id.asReified().n)
                return
            directedGraph.addVertex(to.id.asReified().n)
            println("Add edge $from  -> ${to.id.asReified()} (${to.humanName})")
            directedGraph.addEdge(from, to.id.asReified().n)
        }
        fun addEdge(from: Int, to: Interface<LogicInt>) {
            if (from == to.id.asReified().n)
                return
            directedGraph.addVertex(to.id.asReified().n)
            println("Add edge $from  -> ${to.id.asReified()} (${to.humanName})")
            directedGraph.addEdge(from, to.id.asReified().n)
        }
        for ( (id, decl) in ct.table) {
            println("WIP: $id    with `$decl`");
            directedGraph.addVertex(id)
            when (decl) {
                is C -> when (decl.superClass) {
                    is Class_ -> addEdge(id, decl.superClass)
                    is Array_ -> println("TODO ${Thread.currentThread().stackTrace[2].lineNumber}")
                    else -> {}
                }
                is I ->
                    for (i in decl.supers.asReified().toList()) {
                        when (i) {
                            is Interface -> addEdge(id, i)
                            else -> {}
                        }
                    }
            }
        }
        with(directedGraph) {
            val moreDependencyFirstIterator = TopologicalOrderIterator(directedGraph)
            // Some class are generated withoout information. Possible Bug
            val toRemove : MutableSet<Int> = mutableSetOf()
            moreDependencyFirstIterator.forEachRemaining { id: Int ->
                if (ct.table[id] == null)
                    toRemove.add(id)
            }
            toRemove.forEach { directedGraph.removeVertex(it!!) }
        }
        val moreDependencyFirstIterator = TopologicalOrderIterator(directedGraph)
        moreDependencyFirstIterator.forEachRemaining { id: Int ->
            assert(ct.table.containsKey(id))
            val dest = ct.table[id]
            println("$id -> $dest")
        }

    }
}
