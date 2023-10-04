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
import org.klogic.utils.terms.LogicTruᴼ
import utils.*
import utils.JGS.*
import utils.LogicInt.Companion.toLogic

class DefaultCT : CLASSTABLE {
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

    private fun addClass(c: C<ID>): Int {
        data[newId()] = c
        return lastId
    }

    private fun addInterface(c: I<ID>): Int {
        data[newId()] = c
        return lastId
    }

    private fun addInterface(
        params: Term<LogicList<Jtype<ID>>>,
        supers: Term<LogicList<Jtype<ID>>>
    ): Int {
        data[newId()] = I(params, supers)
        return lastId

    }

    constructor() {
        top = Class_<ID>(0.toLogic(), logicListOf());
        addClass(C(logicListOf(), top, logicListOf()))
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

    context(RelationalContext) override fun get_superclass_by_id(
        v3: Term<LogicInt>,
        v4: Term<LogicInt>,
        v5: Term<LogicOption<Jtype<LogicInt>>>
    ): Goal {
        TODO("Not yet implemented")
    }
}

typealias ID = LogicInt

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

    fun testForward(a: (CLASSTABLE) -> Term<Jtype<ID>>, b: (CLASSTABLE) -> Term<Jtype<ID>>, rez: Boolean, verbose: Boolean = false) {
        val classtable = DefaultCT()
        val v = Verifier(classtable)

        withEmptyContext {
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
        testForward(a, b, true)
    }
    @Test
    @DisplayName("Object[] <: Clonable")
    fun test2() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.cloneable_t }
        testForward(a, b, true)
    }
    @Test
    @DisplayName("Object[] <: Serializable")
    fun test3() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.serializable_t }
        testForward(a, b, true)
    }

    @Test
    @DisplayName("Object[] :> Object is FALSE")
    fun test4() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.object_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, false)
    }
    @Test
    @DisplayName("Object[] :> Clonable is FALSE")
    fun test5() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.cloneable_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, false)
    }
    @Test
    @DisplayName("Object[] :> Serializable is FALSE")
    fun test6() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.serializable_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, false)
    }

    @Test
    @DisplayName("Object[][] <: Serializable[]")
    fun test7() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(Array_(classtable.object_t)) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.serializable_t) }
        testForward(a, b, true, true)
    }

}
