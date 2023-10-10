import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.ZeroNaturalNumber
import utils.JGS.*
import utils.JGS.Closure.CLOSURE
import utils.JGS.Closure.Closure
import utils.JGS.Var
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.LogicOption


class JGSBackward {
    @AfterEach
    fun clear() {
        //        UnificationsController.onFinish()
    }

    private val unificationsTracer = UnificationListener { firstTerm, secondTerm, stateBefore, stateAfter ->
        //if (System.getenv("SILENT_UNIFICATIONS") == null)
        val rez = if (stateAfter == null) " ~~> _|_"
        else ""
        println(
            "${firstTerm.walk(stateBefore.substitution)} `===` ${
                secondTerm.walk(stateBefore.substitution)
            }$rez"
        )
    }

    internal fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    @Test
    @DisplayName("Wanna specify a domain and cut type variables.")
    fun test0wildcards() {
        withEmptyContext {
            val dom: (Term<Jtype<ID>>) -> Goal = { it ->
                conde(it `===` Class_(1.toLogic(), logicListOf()),
                    it `===` Interface(2.toLogic(), logicListOf()),
                    freshTypedVars { c: Term<Jtype<ID>>, d: Term<LogicOption<Jtype<ID>>> ->
                        it `===` Var(4.toLogic(), ZeroNaturalNumber, c, d)
                    }
                )
            }
            val goal: (Term<Jtype<ID>>) -> Goal = { it ->
                and(
                    // I expect that next lines removes all Type Variables, but it doesn't
                    it `!==` Var(wildcard(), wildcard(), wildcard(), wildcard()),
                    dom(it)
                )
            }
            val answers = run(10, goal).map { it.term }.toList()
            val expectedTerm = listOf(
                Class_(1.toLogic(), logicListOf()),
                Interface(2.toLogic(), logicListOf())
            ).toCountMap()
            assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    enum class ClosureType {
        Subtyping, SuperTyping
    }

    class MakeClosure(
        private val closureBuilder: CLOSURE,
        val ct: CLASSTABLE,
        private val closureType: ClosureType,
        private val verifier: VERIFIER,
        private val ctx: RelationalContext
    ) {

        fun direct(ta: Term<Jtype<ID>>, tb: Term<Jtype<ID>>): Goal {
            with(ctx) {
                return closureBuilder.minus_less_minus( // ERROR. No required context receiver found:
                    // this function is passed as parameter in OCaml, but here we are trying to inline it
                    // see run_json2.ml line 230
                    { a, b, c, d -> verifier.minus_less_minus(a, b, c, d) },
                    { a, b -> closure(a, b) },
                    { success },
                    ta,
                    tb
                )
            }
        }

        fun isCorrect(t: Term<Jtype<ID>>): Goal {
            with(ctx) {
                return closureBuilder.is_correct_type({ a, b -> closure(a, b) }, t)
            }
        }


        fun closure(ta: Term<Jtype<ID>>, tb: Term<Jtype<ID>>): Goal {
            with(ctx) {
                return when (closureType) {
                    ClosureType.Subtyping ->
                        closureBuilder.less_minus_less({ a, b -> direct(a, b) }, success, ta, tb)

                    ClosureType.SuperTyping ->
                        TODO("Not implemented")
                }
            }
        }
    }

    fun testSingleConstraint(
        expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>>,
        count: Int = 10,
        boundKind: ClosureType = ClosureType.Subtyping,
        bound: (CLASSTABLE) -> Term<Jtype<ID>>,
        verbose: Boolean = false
    ) {
        val classTable = DefaultCT()
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)
        withEmptyContext {
            val g = { q: Term<Jtype<ID>> ->
                and(
                    only_classes_interfaces_and_arrays(q),
                    (when (boundKind) {
                        ClosureType.Subtyping ->
                            MakeClosure(closureBuilder, classTable, ClosureType.Subtyping, v, this)
                                .closure(q, bound(classTable))

                        ClosureType.SuperTyping -> TODO()
                    })

                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            assertEquals(count, answers.count())
            val expectedTerm = expectedResult(classTable).toCountMap()
            assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    @Test
    @DisplayName("? <: Object")
    fun test1() {
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
                ct.object_t,
                Array_(ct.object_t),
                Array_(Array_(ct.object_t)),
                Array_(Null) as Jtype<ID>
            )
        }
        testSingleConstraint(expectedResult, count = 4, ClosureType.Subtyping, { it.object_t }, verbose = false)
    }

    @Test
    @DisplayName("? <: Cloneable")
    fun test2() {
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
                ct.object_t
            )
        }
        testSingleConstraint(expectedResult, count = 1, ClosureType.Subtyping, { it.cloneable_t }, verbose = false)
    }

    @Test
    @DisplayName("? <: Cloneable[][]")
    fun test3() {
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
                Array_(Null) as Jtype<ID>
            )
        }
        testSingleConstraint(expectedResult, count = 1, ClosureType.Subtyping, { Array_(Array_(it.cloneable_t)) }, verbose = false)
    }
}
