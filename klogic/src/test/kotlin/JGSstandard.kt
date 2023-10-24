@file:Suppress("SpellCheckingInspection")

import org.jgrapht.Graph
import org.jgrapht.graph.DefaultEdge
import org.jgrapht.graph.DirectedAcyclicGraph
import org.jgrapht.traverse.TopologicalOrderIterator
import org.jgs.classtable.ClassesTable
import org.jgs.classtable.EmptyClassTable
import org.jgs.classtable.extractClassesTable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.core.Var
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.toPeanoLogicNumber
import utils.JGS.*
import utils.JGS.Closure.Closure
import utils.JGS.Wildcard
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.LogicOption
import utils.Some
import utils.freshTypedVars
import kotlin.system.measureTimeMillis
import JGSBackward.ClosureType

class JGSstandard {
    fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    fun checkClassTable(ct: ClassesTable) {
        val nameToId = mutableMapOf<Int, String>()
        for ((typ, id) in ct.classNames) {
            if (nameToId.containsKey(id))
                TODO("FUCK")
            else
                nameToId.put(id, typ.simpleName)
        }
    }

    @Test
    @DisplayName("asasdf")
    fun test0() {
        val ct: ClassesTable = data.first
//        for ((k,v) in ct.table.toSortedMap())
//            println("$k -> $v")
        println("${ct.table[1]} ")
        println("${ct.table[2]} ")
        println("${ct.table[3]} ")
        checkClassTable(ct)
    }

    private val data = prepareGraph(verbose=true)
    private fun prepareGraph(verbose: Boolean = false): Pair<ClassesTable, DirectedAcyclicGraph<Int, DefaultEdge>> {
        var ct: ClassesTable = extractClassesTable()
        val directedGraph: DirectedAcyclicGraph<Int, DefaultEdge> =
            DirectedAcyclicGraph(DefaultEdge::class.java)

        fun addEdge(from: Int, to: Class_<LogicInt>) {
            if (from == to.id.asReified().n)
                return
            directedGraph.addVertex(to.id.asReified().n)
            if (verbose)
                println("Add edge $from  -> ${to.id.asReified()} (${to.humanName})")
            directedGraph.addEdge(from, to.id.asReified().n)
        }

        fun addEdge(from: Int, to: Interface<LogicInt>) {
            if (from == to.id.asReified().n)
                return
            directedGraph.addVertex(to.id.asReified().n)
            if (verbose)
                println("Add edge $from  -> ${to.id.asReified()} (${to.humanName})")
            directedGraph.addEdge(from, to.id.asReified().n)
        }
        for ((id, decl) in ct.table) {
            if (verbose)
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
            val toRemove: MutableSet<Int> = mutableSetOf()
            moreDependencyFirstIterator.forEachRemaining { id: Int ->
                if (ct.table[id] == null)
                    toRemove.add(id)
            }
            toRemove.forEach { directedGraph.removeVertex(it) }
        }
        println("Graph prepareted")
        println(" Total ${ct.table.size} classes")
        println("Id of 'java.lang.Object' =  ${ct.idOfName["java.lang.Object"]}")
        println(" Object with id=1 is ${ct.table[1]}")
        return (ct to directedGraph)
    }

    fun testSingleConstraint(
        expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>>,
        count: Int = 10,
        boundKind: JGSBackward.ClosureType = JGSBackward.ClosureType.Subtyping,
        bound: (CLASSTABLE) -> Term<Jtype<ID>>,
        verbose: Boolean = false
    ) {
        val classTable = BigCT(data.second, data.first)
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)
        withEmptyContext {
            val g = { q: Term<Jtype<ID>> ->
                and(
                    only_classes_interfaces_and_arrays(q), (when (boundKind) {
                        JGSBackward.ClosureType.Subtyping -> JGSBackward.MakeClosure2(closureBuilder)
                            .closure({ a, b, c, d ->
                            v.minus_less_minus(
                                a,
                                b,
                                c,
                                d
                            )
                        }, q, bound(classTable))

                        JGSBackward.ClosureType.SuperTyping -> TODO()
                    })
                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            Assertions.assertEquals(count, answers.count())
            val expectedTerm = expectedResult(classTable).toCountMap()
            Assertions.assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    @Test
    @DisplayName("111")
    fun test1() {
        val ct = data.first
        val moreDependencyFirstIterator = TopologicalOrderIterator(data.second)
        moreDependencyFirstIterator.forEachRemaining { id: Int ->
            assert(ct.table.containsKey(id))
            val dest = ct.table[id]
            println("$id -> $dest")
        }
    }

    @Test
    @DisplayName("Simple use of the class table")
    fun test2() {
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
//                ct.object_t, Array_(ct.object_t), Array_(Array_(ct.object_t)), Array_(Null) as Jtype<ID>
            )
        }
        testSingleConstraint(expectedResult, count = 4, ClosureType.Subtyping, { it.object_t }, verbose = false)
    }


    class BigCT : CLASSTABLE {
        private var lastId: Int = 0
        fun newId(): Int {
            lastId++;
            return lastId;
        }

        private val graph: DirectedAcyclicGraph<Int, DefaultEdge>
        private val data: ClassesTable
        private val objectId: Int
        private val cloneableId: Int
        private val serializableId: Int
//        private val top: Term<Jtype<ID>>?
//
        override val object_t: Term<Jtype<LogicInt>>
        override val cloneable_t: Term<Jtype<LogicInt>>
        override val serializable_t: Term<Jtype<LogicInt>>

        constructor(g: DirectedAcyclicGraph<Int, DefaultEdge>, ct: ClassesTable) {
            assert(ct.table.isNotEmpty())
            assert(ct.idOfName.isNotEmpty())
            graph = g
            data = ct
//            top = Class_<ID>(0.toLogic(), LogicList.logicListOf());
//            addClass(LogicList.logicListOf(), top, LogicList.logicListOf())
//            lastId = 0;

            // TODO: add assertions that hardcoded classes correspond to class table
            objectId = 1
            assert(objectId == 1)
            object_t = Class_(objectId.toLogic(), LogicList.logicListOf())
            assert(ct.table.containsKey(objectId))

            cloneableId = 2
            assert(cloneableId == 2)
            cloneable_t = Interface(cloneableId.toLogic(), LogicList.logicListOf())
            assert(ct.table.containsKey(cloneableId))

            serializableId = 3
            assert(serializableId == 3)
            serializable_t = Interface(serializableId.toLogic(), LogicList.logicListOf())
            assert(ct.table.containsKey(serializableId))
        }
//        override fun addClass(c: C<ID>): Int {
//            data[newId()] = c
//            return lastId
//        }
//
//        override fun addClass(
//            params: Term<LogicList<Jtype<ID>>>,
//            superClass: Term<Jtype<ID>>,
//            supers: Term<LogicList<Jtype<ID>>>,
//        ): Int {
//            data[newId()] = C(params, superClass, supers)
//            return lastId
//        }
//
//        override fun addInterface(c: I<ID>): Int {
//            data[newId()] = c
//            return lastId
//        }
//
//        override fun addInterface(
//            params: Term<LogicList<Jtype<ID>>>,
//            supers: Term<LogicList<Jtype<ID>>>
//        ): Int {
//            data[newId()] = I(params, supers)
//            return lastId
//
//        }

//        override fun makeTVar(index: Int, upb: Term<Jtype<ID>>): Jtype<ID> {
//            val id = newId()
//            return utils.JGS.Var(id.toLogic(), index.toPeanoLogicNumber(), upb, None())
//        }

        context(RelationalContext) override fun new_var(): Term<LogicInt> {
            return newId().toLogic()
        }

        context(RelationalContext)
        override fun decl_by_id(v1: Term<LogicInt>, rez: Term<Decl<LogicInt>>): Goal {
//        println("decl_by_id: $v1, $rez")
            return debugVar(v1, { id -> id.reified() }) { it ->
                val v = it.term
                when (v) {
                    is Var<*> -> TODO("not implemented. Got a var")
                    is LogicInt ->
                        if (data.table.containsKey(v.n))
                            rez `===` data.table.get(v.n)!!
                        else
                            TODO("Not implemented. Asked integer ${v.n} which is not in the table")
                    else -> TODO("?")
                }

            }
        }

        context(RelationalContext)
        fun getSuperclassByIdFreeFree(
            subId: Term<LogicInt>, superId: Term<LogicInt>,
            rez: Term<Jtype<LogicInt>>
        ): Goal {
            val parents: (Decl<ID>) -> List<Jtype<ID>> = { it ->
                when (it) {
                    is I -> when (it.supers) {
                        is LogicList<Jtype<ID>> -> it.supers.toList().map { it -> it as Jtype<ID> }

                        is org.klogic.core.Var -> TODO("")
                        is Wildcard<*> -> TODO("Should not be reachable")
                        else -> TODO("Should not be reachable 100%")
                    }
//                is I -> when (it.supers) {
//                    is CustomTerm<LogicList<Jtype<ID>>> -> it.supers.asReified().toList().map { it -> it as Jtype<ID> }
//                    is org.klogic.core.UnboundedValue<*> -> TODO("")
//
//                }
                    is C -> when (it.supers) {
                        is LogicList<Jtype<ID>> -> it.supers.toList().map { it as Jtype<ID> }

                        is Var -> TODO("")
                        is Wildcard<*> -> TODO("Should not be reachable")
                        else -> TODO("Should not be reachable 100%")
                    } + when (it.superClass) {
                        is Jtype<ID> -> listOf(it.superClass)

                        is Var -> TODO("")
                        is Wildcard<*> -> TODO("Should not be reachable")
                        else -> TODO("Should not be reachable 100%")
                    }
                }
            }
            return data.table.entries.fold(failure) { acc, entry ->
                val curId = entry.key
                if (curId == objectId) acc
                else {
                    val d: Term<Decl<ID>> = entry.value
                    val parentsList = parents(d as Decl<ID>)


                    parentsList.fold(acc) { acc, jtyp ->
                        when (jtyp) {
                            is Interface -> acc `|||` and(
                                jtyp.id `===` superId,
                                curId.toLogic() `===` subId, rez `===` jtyp
                            )

                            is Class_ -> acc `|||` and(
                                jtyp.id `===` superId,
                                curId.toLogic() `===` subId, rez `===` jtyp
                            )

                            else -> TODO("ancestor of the interface should be an interface")
                        }
                    }
                }
            }
        }

        context(RelationalContext) override fun get_superclass_by_id(
            subId: Term<LogicInt>,
            superId: Term<LogicInt>,
            rez: Term<LogicOption<Jtype<LogicInt>>>
        ): Goal {
            println("get_superclass_by_id $subId $superId ~~> $rez\n")
            return freshTypedVars { answerJtyp: Term<Jtype<LogicInt>> ->
                and(rez `===` Some(answerJtyp), getSuperclassByIdFreeFree(subId, superId, answerJtyp))
            }
        }
    }


}
