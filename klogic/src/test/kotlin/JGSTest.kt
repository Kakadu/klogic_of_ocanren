import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.core.Var
import org.klogic.utils.terms.LogicBool
import org.klogic.utils.terms.LogicBool.Companion.toLogicBool
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import utils.*
import utils.JGS.*
import utils.LogicInt.Companion.toLogic

typealias ID = LogicInt

interface MutableClassTable : CLASSTABLE {
    fun addClass(c: C<ID>): Int
    fun addClass(
        params: Term<LogicList<Jtype<ID>>>,
        superClass: Term<Jtype<ID>>,
        supers: Term<LogicList<Jtype<ID>>>,
    ): Int

    fun addInterface(c: I<ID>): Int
    fun addInterface(
        params: Term<LogicList<Jtype<ID>>>,
        supers: Term<LogicList<Jtype<ID>>>
    ): Int
}

class DefaultCT : MutableClassTable {
    private var lastId: Int = 0
    fun newId(): Int {
        lastId++;
        return lastId;
    }

    private val data: MutableMap<Int, Decl<ID>> = mutableMapOf()
    private val objectId: Int
    private val cloneableId: Int
    private val serializableId: Int
    private val top: Term<Jtype<ID>>?

    override val object_t: Term<Jtype<LogicInt>>
    override val cloneable_t: Term<Jtype<LogicInt>>
    override val serializable_t: Term<Jtype<LogicInt>>

    override fun addClass(c: C<ID>): Int {
        data[newId()] = c
        return lastId
    }

    override fun addClass(
        params: Term<LogicList<Jtype<ID>>>,
        superClass: Term<Jtype<ID>>,
        supers: Term<LogicList<Jtype<ID>>>,
    ): Int {
        data[newId()] = C(params, superClass, supers)
        return lastId
    }

    override fun addInterface(c: I<ID>): Int {
        data[newId()] = c
        return lastId
    }

    override fun addInterface(
        params: Term<LogicList<Jtype<ID>>>,
        supers: Term<LogicList<Jtype<ID>>>
    ): Int {
        data[newId()] = I(params, supers)
        return lastId

    }

    constructor() {
        top = Class_<ID>(0.toLogic(), logicListOf());
        addClass(logicListOf(), top, logicListOf())
        lastId = 0;
        objectId = addClass(C(logicListOf(), top, logicListOf()))
        assert(objectId == 1)
        object_t = TypeClass_(objectId.toLogic(), logicListOf())
        cloneableId = addInterface(logicListOf(), logicListOf())
        assert(cloneableId == 2)
        cloneable_t = Interface(cloneableId.toLogic(), logicListOf())
        serializableId = addInterface(logicListOf(), logicListOf())
        assert(serializableId == 3)
        serializable_t = Interface(serializableId.toLogic(), logicListOf())
    }

    context(RelationalContext) override fun new_var(): Term<LogicInt> {
        return newId().toLogic()
    }

    context(RelationalContext)
    override fun decl_by_id(v1: Term<LogicInt>, rez: Term<Decl<LogicInt>>): Goal {
        println("$v1, $rez")
        return debugVar(v1, { id -> id.reified() }) { it ->
            val v = it.term
            when (v) {
                is Var<*> -> TODO("not implemented")
                is LogicInt -> rez `===` (data[v.n] as Term<Decl<LogicInt>>)
                else -> TODO("?")
            }

        }
    }

    context(RelationalContext)
    fun getSuperclassByIdFreeFree(subId: Term<LogicInt>,
                                  v4: Term<LogicInt>,
                                  rez: Term<Jtype<LogicInt>>) : Goal {
        TODO("")

//        return
//            data.entries.fold(failure) { acc, entry ->
//                val d = entry.value
//                when (d) {
//                    is I -> acc
//                    is C -> acc `|||` and(entry.key.toLogic() `===` subId, v4 `===` d.id)
//                }
//
//            }
    }
    context(RelationalContext) override fun get_superclass_by_id(
        v3: Term<LogicInt>,
        v4: Term<LogicInt>,
        v5: Term<LogicOption<Jtype<LogicInt>>>
    ): Goal {
        TODO("Not yet implemented")
    }
}


//
//interface IFOO {
//    context(RelationalContext)
//    fun foo(): Goal
//}
//
//@Test
//fun testIFOO(i: IFOO): Goal {
//    withEmptyContext {
//        val g = i.foo()
//        return g
//    }
//}

data class NotComplete(val v: VERIFIER) {
    context(RelationalContext)
    fun smallFish(ta: Term<Jtype<LogicInt>>, tb: Term<Jtype<LogicInt>>, rez: Term<LogicBool>): Goal =
        this.check(ta, tb, rez)

    context(RelationalContext)
    fun check(ta: Term<Jtype<LogicInt>>, tb: Term<Jtype<LogicInt>>, rez: Term<LogicBool>): Goal {
        return v.minus_less_minus(
            { a, b, c -> smallFish(a, b, c) }, ta, tb, rez
        )
    }
}

class JGSTest {
    @AfterEach
    fun clear() {
//        UnificationsController.onFinish()
    }

    private val unificationsTracer = UnificationListener { firstTerm, secondTerm, stateBefore, stateAfter ->
        //if (System.getenv("SILENT_UNIFICATIONS") == null)
        val rez =
            if (stateAfter == null)
                " ~~> _|_"
            else ""
        println("${firstTerm.walk(stateBefore.substitution)} `===` ${secondTerm.walk(stateBefore.substitution)}$rez")
    }

    fun testForward(
        a: (MutableClassTable) -> Term<Jtype<ID>>,
        b: (MutableClassTable) -> Term<Jtype<ID>>,
        init: (MutableClassTable) -> Unit = { },
        rez: Boolean,
        verbose: Boolean = false
    ) {
        val classtable = DefaultCT()
        init(classtable)
        val v = Verifier(classtable)

        withEmptyContext {
            if (verbose)
                addUnificationListener(unificationsTracer)
            val g: (Term<LogicBool>) -> Goal = { NotComplete(v).check(a(classtable), b(classtable), it) }

            val answers = run(2, g).map { it.term }.toList()
            if (verbose)
                answers.forEachIndexed { i, x -> println("$i: $x") }

            assertEquals(answers.count(), 1)
            val expectedTerm = rez.toLogicBool()
            assertEquals(expectedTerm, answers[0])
        }
    }

    @Test
    @DisplayName("Object[] <: Object")
    fun test1() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.object_t }
        testForward(a, b, rez = true)
    }

    @Test
    @DisplayName("Object[] <: Clonable")
    fun test2() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.cloneable_t }
        testForward(a, b, rez = true)
    }

    @Test
    @DisplayName("Object[] <: Serializable")
    fun test3() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.serializable_t }
        testForward(a, b, rez = true)
    }

    @Test
    @DisplayName("Object[] :> Object is FALSE")
    fun test4() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.object_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, rez = false)
    }

    @Test
    @DisplayName("Object[] :> Clonable is FALSE")
    fun test5() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.cloneable_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, rez = false)
    }

    @Test
    @DisplayName("Object[] :> Serializable is FALSE")
    fun test6() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.serializable_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, rez = false)
    }

    @Test
    @DisplayName("Object[][] <: Serializable[]")
    fun test7() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(Array_(classtable.object_t)) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.serializable_t) }
        testForward(a, b, rez = true, verbose = false)
    }

    @Test
    @DisplayName("A <: B")
    fun test8() {
        var a: Term<Jtype<ID>>? = null
        var b: Term<Jtype<ID>>? = null
        // TODO(Kakadu): this null-related stuff is bad. rewrite.
        val init :  (MutableClassTable) -> Unit = { ct: MutableClassTable ->
            val aId = ct.addClass(logicListOf() , ct.object_t, logicListOf())
            a = Class_(aId.toLogic(), logicListOf())
            val bId = ct.addClass(logicListOf() , a!!, logicListOf())
            b = Class_(bId.toLogic(), logicListOf())
        }
        testForward({ a!! }, { b!! }, init, rez = true, verbose = false)
    }
}
