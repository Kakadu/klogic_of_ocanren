@file:Suppress("SpellCheckingInspection")

import JGSBackward.ClosureType
import org.jgrapht.graph.DefaultEdge
import org.jgrapht.graph.DirectedAcyclicGraph
import org.jgrapht.traverse.TopologicalOrderIterator
import org.jgs.classtable.ClassesTable
import org.jgs.classtable.extractClassesTable
import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.klogic.core.*
import org.klogic.core.Var
import org.klogic.utils.terms.LogicBool
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.logicTo
import org.klogic.utils.terms.toPeanoLogicNumber
import utils.JGS.*
import utils.JGS.Closure.Closure
import utils.JGS.Wildcard
import utils.JtypePretty
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.LogicOption
import utils.Some
import utils.freshTypedVars

class JGSstandard {
    companion object {
        private var data: Pair<ClassesTable, DirectedAcyclicGraph<Int, DefaultEdge>> =
            ClassesTable(mutableMapOf()) to DirectedAcyclicGraph(
                DefaultEdge::class.java
            )

        @JvmStatic
        @BeforeAll
        fun initClasses() {
            val ct: ClassesTable = extractClassesTable()
            println(" Classes are loaded")
            println("java.util.AbstractList's ID = ${ct.idOfName["java.util.AbstractList"]}")

            data = prepareGraph(ct, verbose = false)
        }

        private fun prepareGraph(
            ct: ClassesTable,
            verbose: Boolean = false
        ): Pair<ClassesTable, DirectedAcyclicGraph<Int, DefaultEdge>> {

            val directedGraph: DirectedAcyclicGraph<Int, DefaultEdge> = DirectedAcyclicGraph(
                DefaultEdge::class.java
            )

            fun addEdge(from: Int, to: Class_<LogicInt>) {
                val destID = to.id.asReified().n
                if (from == destID)
                    return
                directedGraph.addVertex(destID)
                if (verbose) {
                    val destName = ct.nameOfId[destID]!!
                    println("Add edge $from  -> ${to.id.asReified()} ($destName)")
                }
                directedGraph.addEdge(from, destID)
            }

            fun addEdge(from: Int, to: Interface<LogicInt>) {
                val destID = to.id.asReified().n
                if (from == destID)
                    return
                directedGraph.addVertex(destID)
                if (verbose) {
                    val destName = ct.nameOfId[destID]!!
                    println("Add edge $from  -> ${to.id.asReified()} ($destName)")
                }
                directedGraph.addEdge(from, to.id.asReified().n)
            }
            for ((id, decl) in ct.table) {
                if (verbose) println("WIP: $id    with `$decl`")
                directedGraph.addVertex(id)
                when (decl) {
                    is C -> when (decl.superClass) {
                        is Class_ -> addEdge(id, decl.superClass)
                        is Array_ -> println(
                            "TODO ${Thread.currentThread().stackTrace[2].lineNumber}"
                        )

                        else -> {}
                    }

                    is I -> for (i in decl.supers.asReified().toList()) {
                        when (i) {
                            is Interface -> addEdge(id, i)
                            else -> {}
                        }
                    }
                }
            }
            with(directedGraph) {
                val moreDependencyFirstIterator = TopologicalOrderIterator(
                    directedGraph
                ) // Some class are generated withoout information. Possible Bug
                val toRemove: MutableSet<Int> = mutableSetOf()
                moreDependencyFirstIterator.forEachRemaining { id: Int ->
                    if (ct.table[id] == null) toRemove.add(id)
                }
                toRemove.forEach { directedGraph.removeVertex(it) }
            }
            println("Graph prepareted")
            println(" Total ${ct.table.size} classes")
            println(" Orphaned types: ${ct.missingTypes} ")
            //        println(" nameOfId size =  ${ct.da} ")

            println("Id of 'java.lang.Object' =  ${ct.idOfName["java.lang.Object"]}")
            println("Id of 'java.lang.Iterable' =  ${ct.idOfName["java.lang.Iterable"]}")
            println("Id of 'java.util.List' =  ${ct.idOfName["java.util.List"]}")
            println(" Object with id=1 is ${ct.table[1]}")
            //        println(" Object with id=7671 is ${ct.table[7671]}")
            return (ct to directedGraph)
        }
    }


    private fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    private fun checkClassTable(ct: ClassesTable) {
        val nameToId = mutableMapOf<Int, String>()
        for ((typ, id) in ct.classNames) {
            if (nameToId.containsKey(id)) TODO("FUCK")
            else nameToId[id] = typ.simpleName
        }
    }

    @Test
    @DisplayName("Class table is well founded")
    fun test0() {
        val ct: ClassesTable = data.first //        for ((k,v) in ct.table.toSortedMap())
        //            println("$k -> $v")
        println("${ct.table[1]} ")
        println("${ct.table[2]} ")
        println("${ct.table[3]} ")
        checkClassTable(ct)
    }


    private fun testSingleConstraint(
        expectedResult: (CLASSTABLE) -> Collection<String>, count: Int = 10,
        boundKind: ClosureType = ClosureType.Subtyping,
        bound: (RelationalContext, ConvenientCT) -> Term<Jtype<ID>>, verbose: Boolean = false
    ) {
        val classTable = BigCT(data.second, data.first)
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)
        withEmptyContext {
            val g = { q: Term<Jtype<ID>> ->
                and(
                    only_classes_interfaces_and_arrays(q), (when (boundKind) {
                        ClosureType.Subtyping -> JGSBackward.MakeClosure2(closureBuilder)
                            .closure({ a, b, c, d ->
                                v.minus_less_minus(a, b, c, d)
                            }, q, bound(this, classTable))

                        ClosureType.SuperTyping -> JGSBackward.MakeClosure2(closureBuilder)
                            .closure({ a, b, c, d ->
                                v.minus_less_minus(a, b, c, d)
                            }, bound(this, classTable), q)
                    })
                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            val expectedTerm = expectedResult(classTable).toCountMap()
            val pp = JtypePretty { classTable.nameOfId(it) }
            val answers2 = answers.map { pp.ppJtype(it) }
            answers2.run {
                forEachIndexed { i, x -> println("//$i\n\"$x\",") }
            }
            assertEquals(count, answers.count())
            assertEquals(expectedTerm, answers2.toCountMap())
        }
    }


    private fun testManyConstraints(
        expectedResult: (CLASSTABLE) -> Collection<String>,
        count: Int = 10,
        verbose: Boolean,
        bounds:
            (RelationalContext, ConvenientCT) -> Collection<Pair<ClosureType, Term<Jtype<ID>>>>
    ) {
        val classTable = BigCT(data.second, data.first)
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)

        withEmptyContext {
            val (subs, supers) = bounds(this, classTable).partition {
                when (it.first) {
                    ClosureType.Subtyping -> true
                    ClosureType.SuperTyping -> false
                }
            }
            val g = { q: Term<Jtype<ID>> ->
                val direct: (v29: (Term<Jtype<LogicInt>>, Term<Jtype<LogicInt>>, Term<LogicBool>) -> Goal, v30: Term<Jtype<LogicInt>>, v31: Term<Jtype<LogicInt>>, v32: Term<LogicBool>) -> (State) -> RecursiveStream<State> =
                    { a, b, c, d ->
                        v.minus_less_minus(a, b, c, d)
                    }
                and(
                    only_classes_interfaces_and_arrays(q),
                    supers.fold(success) { acc, (_, bound) ->
                        acc and
                                JGSBackward.MakeClosure2(closureBuilder)
                                    .closure(direct, bound, q)
                    },
                    subs.fold(success) { acc, (_, bound) ->
                        acc and
                                JGSBackward.MakeClosure2(closureBuilder)
                                    .closure(direct, q, bound)
                    },
                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            val expectedTerm = expectedResult(classTable).toCountMap()
            val pp = JtypePretty { classTable.nameOfId(it) }
            val answers2 = answers.map { pp.ppJtype(it) }
            answers2.run {
                forEachIndexed { i, x -> println("//$i\n\"$x\",") }
            }
            assertEquals(count, answers.count())
            assertEquals(expectedTerm, answers2.toCountMap())
        }
    }

    @Test
    @DisplayName("111")
    fun test1() {
        val ct = data.first
        val moreDependencyFirstIterator = TopologicalOrderIterator(data.second)
        moreDependencyFirstIterator.forEachRemaining { id: Int ->
            check(ct.table.containsKey(id))
            val dest = ct.table[id]
            println("$id -> $dest")
        }
    }

    @Test
    @DisplayName("Subclasses of Object")
    fun test2() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                "Class java.lang.Object",
//1
                "Array<Class java.lang.Object>",
//2
                "Class sun.util.resources.provider.NonBaseLocaleDataMetaInfo",
//3
                "Array<Array<Class java.lang.Object>>",
//4
                "Array<Class sun.util.resources.provider.NonBaseLocaleDataMetaInfo/*TODO*/>",
            )
        }
        testSingleConstraint(
            expectedResult,
            count = 5,
            ClosureType.Subtyping, { _, ct -> ct.object_t },
            verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of Iterable<Object>")
    fun test3() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                "Interface java.lang.Iterable<Class java.lang.Object>",
//1
                "Interface javax.xml.crypto.NodeSetData<Class java.lang.Object>",
//2
                "Class java.util.stream.SpinedBuffer\$OfPrimitive<Class java.lang.Object, _.?, _.?>",
//3
                "Class java.util.stream.SpinedBuffer<Class java.lang.Object>",
//4
                "Class java.util.ServiceLoader<Class java.lang.Object>",

            )
        }

        testSingleConstraint(
            expectedResult, count = 5,
            ClosureType.Subtyping, { _, ct ->
                val humanName = "java.lang.Iterable"
                val listID = ct.idOfName(humanName)!!
                ct.makeInterface(listID, logicListOf(Type(ct.object_t)))
            },
            verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of java.util.AbstractList<Object>")
    fun test4() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                "Class java.util.AbstractList<Class java.lang.Object>",
//1
                "Class sun.awt.util.IdentityArrayList<Class java.lang.Object>",
//2
                "Class java.util.Vector<Class java.lang.Object>",
//3
                "Class java.util.Collections\$SingletonList<Class java.lang.Object>",
//4
                "Class java.util.Collections\$EmptyList<Class java.lang.Object>",
//5
                "Class java.util.Collections\$CopiesList<Class java.lang.Object>",
//6
                "Class java.util.Arrays\$ArrayList<Class java.lang.Object>",
//7
                "Class java.util.ArrayList\$SubList<Class java.lang.Object>",
//8
                "Class java.util.ArrayList<Class java.lang.Object>",
//9
                "Class java.util.AbstractSequentialList<Class java.lang.Object>",
//10
                "Class java.util.AbstractList\$SubList<Class java.lang.Object>",
//11
                "Class java.lang.invoke.AbstractConstantGroup\$AsList",
//12
                "Class com.sun.org.apache.xerces.internal.impl.xs.util.ObjectListImpl",
//13
                "Class com.sun.org.apache.xerces.internal.impl.dv.xs.XSSimpleTypeDecl\$AbstractObjectList",
//14
                "Class com.sun.org.apache.xerces.internal.impl.dv.xs.ListDV\$ListData",
//15
                "Class com.sun.jmx.remote.internal.ArrayQueue<Class java.lang.Object>",
//16
                "Class java.util.Stack<Class java.lang.Object>",
//17
                "Class sun.swing.BakedArrayList<Class java.lang.Object>",
//18
                "Class jdk.internal.org.objectweb.asm.tree.MethodNode$1",
//19
                "Class javax.management.relation.RoleUnresolvedList",
//20
                "Class javax.management.relation.RoleList",
//21
                "Class javax.management.AttributeList",
//22
                "Class sun.awt.util.IdentityLinkedList<Class java.lang.Object>",
//23
                "Class java.util.LinkedList<Class java.lang.Object>",
//24
                "Class java.util.AbstractList\$RandomAccessSubList<Class java.lang.Object>",
//25
                "Class com.sun.org.apache.xerces.internal.impl.dv.xs.XSSimpleTypeDecl$3",
//26
                "Class com.sun.org.apache.xerces.internal.impl.dv.xs.XSSimpleTypeDecl$2",
            )
        }
        // In principle, we can find AbstractSequentialList, ArrayList, Vector
        // but this classes seem not to be in the class table

        val lookup = { ct: BigCT, clas: String ->
            println("\nLooking for $clas in the idOfName")
            ct.data.idOfName.forEach {
                if (it.key.contains(clas)) {
                    println("\t${it.key} ~~> ${it.value}")
                    println("\t\t${ct.data.table[it.value]}")
                }
            }
        }
        testSingleConstraint(
            expectedResult, count = 27,
            ClosureType.Subtyping, { _, ct ->
                val ct2 = ct as BigCT

                val humanName = "java.util.AbstractList"
                val listID = ct.idOfName(humanName)!!
                ct.makeClass(listID, logicListOf(Type(ct.object_t)))
            },
            verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of Collection<V1>")
    fun test5() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
                "Interface java.util.Collection</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
                "Class java.util.concurrent.ConcurrentHashMap\$ValuesView</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None), _.?>"
            )
        }

        testSingleConstraint(
            expectedResult, count = 2,
            ClosureType.Subtyping, { _, ct ->
                val humanName = "java.util.Collection"
                val iterableID = ct.idOfName(humanName)!!

                ct.makeInterface(iterableID, logicListOf(Type(ct.makeTVar(0, ct.object_t))))
            },
            verbose = false
        )
    }

    @Test
    @DisplayName("Super classes of javax.management.AttributeList")
    fun test6() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                "Class javax.management.AttributeList",
//1
                "Class java.util.ArrayList<Class java.lang.Object>",
//2
                "Interface java.io.Serializable",
//3
                "Interface java.lang.Cloneable",
//4
                "Interface java.util.RandomAccess",
//5
                "Class java.util.AbstractList<Class java.lang.Object>",
//6
                "Interface java.util.List<Class java.lang.Object>",
//7
                "Interface java.util.List<Class java.lang.Object>",
//8
                "Class java.util.AbstractCollection<Class java.lang.Object>",
//9
                "Interface java.util.Collection<Class java.lang.Object>",
//10
                "Interface java.lang.Iterable<Class java.lang.Object>",
//11
                "Interface java.util.Collection<Class java.lang.Object>",
//12
                "Class java.lang.Object",
//13
                "Interface java.util.Collection<Class java.lang.Object>",
//14
                "Interface java.lang.Iterable<Class java.lang.Object>",
//15
                "Interface java.lang.Iterable<Class java.lang.Object>",
            )
        }

        testSingleConstraint(
            expectedResult, count = 16,
            ClosureType.SuperTyping, { _, ct ->
                val humanName = "javax.management.AttributeList"
                val ID = ct.idOfName(humanName)!!
                ct.makeClass(ID, logicListOf())
            },
            verbose = false
        )
    }

    @Test
    @DisplayName("Conj of constraints ")
    fun test7() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
                //0
                "Interface java.util.Collection</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//1
                "Class java.util.concurrent.ConcurrentHashMap\$ValuesView</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None), _.?>",
//2
                "Class java.util.concurrent.ConcurrentHashMap\$CollectionView</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None), _.?, _.?>",
//3
                "Interface java.util.Set</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//4
                "Interface java.util.Queue</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//5
                "Interface java.util.List</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//6
                "Class java.util.Collections\$UnmodifiableCollection</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//7
                "Class java.util.Collections\$SynchronizedCollection</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//8
                "Class java.util.Collections\$CheckedCollection</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//9
                "Class java.util.AbstractCollection</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//10
                "Class java.util.concurrent.ConcurrentHashMap\$EntrySetView</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None), _.?>",
//11
                "Class javax.security.auth.Subject\$SecureSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//12
                "Class java.util.concurrent.ConcurrentHashMap\$KeySetView</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None), _.?>",
//13
                "Interface java.util.SortedSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//14
                "Class java.util.ImmutableCollections\$AbstractImmutableSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//15
                "Class java.util.LinkedHashSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//16
                "Class java.util.ImmutableCollections\$AbstractImmutableSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//17
                "Class java.util.LinkedHashSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//18
                "Class java.util.LinkedHashSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
//19
                "Class java.util.LinkedHashSet</*TODO 2 */Var(id=1, index=0, upb=Class_(id=1, args=()), lwb=None)>",
            )
        }

        testManyConstraints(
            expectedResult, count = 20,
            verbose = false
        ) { _, ct ->
            val iterableID = ct.idOfName("java.lang.Iterable")!!
            val collectionID = ct.idOfName("java.util.Collection")!!
            val v1 = Type(ct.makeTVar(0, ct.object_t))
            listOf(
                ClosureType.Subtyping to ct.makeInterface(iterableID, logicListOf(v1)),
                ClosureType.Subtyping to ct.makeInterface(collectionID, logicListOf(v1)),
            )
        }
    }

    @Test
    @DisplayName("Conj of upper and lower bound")
    fun test8() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                "Class javax.management.AttributeList",
//1
                "Class java.util.ArrayList<Class java.lang.Object>",
//2
                "Interface java.util.RandomAccess",
            )
        }

        testManyConstraints(
            expectedResult, count = 3,
            verbose = false
        ) { _, ct ->
            val attrListID = ct.idOfName("javax.management.AttributeList")!!
            val randAccID = ct.idOfName("java.util.RandomAccess")!!
            listOf(
                ClosureType.SuperTyping to ct.makeClass(attrListID, logicListOf()),
                ClosureType.Subtyping to ct.makeInterface(randAccID, logicListOf()),
            )
        }
    }

    interface ConvenientCT : CLASSTABLE {
        fun idOfName(name: String): Int?
        fun nameOfId(id: Int): String?
        fun makeTVar(index: Int, upb: Term<Jtype<ID>>): Jtype<ID>
        fun makeClass(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>>
        fun makeInterface(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>>
    }

    class BigCT//            top = Class_<ID>(0.toLogic(), LogicList.logicListOf());
    //            addClass(LogicList.logicListOf(), top, LogicList.logicListOf())
    //            lastId = 0;

    // TODO: add assertions that hardcoded classes correspond to class table

    //            File("/tmp/out.txt").printWriter().use { out ->
    //                out.println("Big Table\n");
    //                out.println("ct.table.size = ${ct.table.size}")
    //                out.println("ct.nameOfId.size = ${ct.nameOfId.size}")
    //                val lookup = { clas: String ->
    //                    out.println("\nLooking for $clas in the nameOfID")
    //                    ct.nameOfId.forEach {
    //                        if (it.value.contains(clas)) {
    //                            check(ct.idOfName[it.value] == it.key)
    //                            out.println("${it.key} ~~> ${it.value}")
    //                            out.println("    --- ${ct.table[it.key]}")
    //                        }
    //                    }
    //                }
    //
    //                lookup("java.lang.Iterable")
    //            }
        (g: DirectedAcyclicGraph<Int, DefaultEdge>, ct: ClassesTable) : ConvenientCT {
        private var lastId: Int = 0
        private fun newId(): Int {
            lastId++
            return lastId
        }

        private val graph: DirectedAcyclicGraph<Int, DefaultEdge> = g
        val data: ClassesTable = ct
        private val topId: Int = 0
        private val objectId: Int
        private val cloneableId: Int
        private val serializableId: Int

        override fun makeTVar(index: Int, upb: Term<Jtype<ID>>): Jtype<ID> {
            val id = newId()
            return utils.JGS.Var(id.toLogic(), index.toPeanoLogicNumber(), upb, None())
        }

        override fun makeClass(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>> {
            assert(data.table.containsKey(id))
            assert(data.table[id] is C)
            return Class_(id.toLogic(), args)
        }
        override fun makeInterface(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>> {
            assert(data.table.containsKey(id))
            assert(data.table[id] is I)
            return Interface(id.toLogic(), args)
        }

        override fun idOfName(name: String): Int? {
//            println(
//                "idOfName? `$name` = ${data.idOfName[name]} when there are ${data.idOfName.size}")
//            data.idOfName.forEach {
//                if (it.key.contains("ArrayList"))
//                    println("\t${it.key} ~~> ${it.value}")
//            }
            return when (val d = data.idOfName[name]) {
                null -> null
                else -> d
            }
        }

        override fun nameOfId(id: Int): String? {
            return data.nameOfId[id]
        }

        private val topT: Term<Jtype<ID>>
        override val object_t: Term<Jtype<ID>>
        override val cloneable_t: Term<Jtype<ID>>
        override val serializable_t: Term<Jtype<ID>>

        init {
            check(ct.table.isNotEmpty())
            check(ct.idOfName.isNotEmpty())
            topT = Class_(topId.toLogic(), logicListOf())
            objectId = 1
            check(objectId == 1)
            object_t = Class_(objectId.toLogic(), logicListOf())
            check(ct.table.containsKey(objectId))
            cloneableId = 2
            check(cloneableId == 2)
            cloneable_t = Interface(cloneableId.toLogic(), logicListOf())
            check(ct.table.containsKey(cloneableId))
            serializableId = 3
            check(serializableId == 3)
            serializable_t = Interface(serializableId.toLogic(), logicListOf())
            check(ct.table.containsKey(serializableId))
        }

        context(RelationalContext) override fun new_var(): Term<LogicInt> {
            return newId().toLogic()
        }


        context(RelationalContext)
        override fun decl_by_id(
            v1: Term<LogicInt>,
            rez: Term<Decl<LogicInt>>
        ): Goal {
            //        println("decl_by_id: $v1, $rez")
            return debugVar(v1, { id -> id.reified() }) {
                when (val v = it.term) {
                    is Var<*> -> TODO("not implemented. Got a var")
                    is LogicInt -> if (data.table.containsKey(v.n)) rez `===` data.table[v.n]!!
                    else {
                        println("Asking for ${data.table[v.n]}")
                        println("Asking for ${data.table[v.n]}")
                        //TODO("Not implemented. Asked integer ${v.n} which is not in the table")
                        val kind = data.kindOfId[v.n]!!
                        when (kind) {
                            is Class_kind -> rez `===` C(logicListOf(), topT, logicListOf())
                            is Interface_kind ->
                                rez `===` I(logicListOf(), logicListOf())
                            //                            failure
                        }

                    }

                    else -> TODO("?")
                }

            }
        }

        context(RelationalContext)
        private fun getSuperclassByIdFreeFree(
            subId: Term<LogicInt>,
            subKind: Term<Jtype_kind>,
            superId: Term<LogicInt>,
            superKind: Term<Jtype_kind>,
            rez: Term<Jtype<LogicInt>>
        ): Goal {
            val parents: (Decl<ID>) -> List<Jtype<ID>> = { it ->
                when (it) {
                    is I -> when (it.supers) {
                        is LogicList<Jtype<ID>> -> it.supers.toList().map { it as Jtype<ID> }

                        is UnboundedValue -> TODO("Should not be reachable")
                        else -> TODO("Should not be reachable 100%")
                    }

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
                    val entryKind = entry.value.getKind()
                    val parentsList = parents(d as Decl<ID>)

                    parentsList.fold(acc) { acc, jtyp ->
                        when (jtyp) {
                            is Interface -> acc `|||` and(
                                jtyp.id `===` superId,
                                superKind `===` Interface_kind,
                                subKind `===` entryKind,
                                curId.toLogic() `===` subId, rez `===` jtyp
                            )

                            is Class_ -> acc `|||` and(
                                jtyp.id `===` superId,
                                superKind `===` Class_kind,
                                subKind `===` entryKind,
                                curId.toLogic() `===` subId, rez `===` jtyp
                            )

                            else -> TODO("ancestor of the interface should be an interface")
                        }
                    }
                }
            }
        }

        context(RelationalContext) @Suppress("PARAMETER_NAME_CHANGED_ON_OVERRIDE")
        override fun get_superclass_by_id(
            subId: Term<LogicInt>,
            subKind: Term<Jtype_kind>,
            superId: Term<LogicInt>,
            superKind: Term<Jtype_kind>,
            rez: Term<LogicOption<Jtype<LogicInt>>>
        ): Goal {

            return debugVar(subId logicTo superId, reifier = { it.reified() }) {
                //                println("get_superclass_by_id ${it.term} ~~> $rez\n")
                freshTypedVars { answerJtyp: Term<Jtype<LogicInt>> ->
                    and(
                        rez `===` Some(answerJtyp),
                        getSuperclassByIdFreeFree(subId, subKind, superId, superKind, answerJtyp)
                    )
                }
            }
        }
    }
}
