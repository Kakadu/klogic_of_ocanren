import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Test
import org.klogic.core.RelationalContext
import org.klogic.core.Term
import org.klogic.core.useWith
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import utils.LogicInt
import utils.UnificationsController
import utils.appendo
import utils.LogicInt.Companion.toLogic
 

inline fun <R> withEmptyContext(
        block: RelationalContext.() -> R): R = RelationalContext().useWith { block() }

class AppendoTest {
    @AfterEach
    fun clear() {
        UnificationsController.onFinish()
    }

    // May be run manually using './gradlew :test --tests "AppendoTest.testAppendo1"'
    @Test
    fun testAppendo1() {
        withEmptyContext {
            val a = logicListOf(0.toLogic())
            val b = logicListOf(1.toLogic())

            val goal = { q: Term<LogicList<LogicInt>> -> appendo(a, b, q) }
            val answers = run(1, goal)
            println(answers[0])

            UnificationsController.onFinish()
        }
    }

    // May be run manually using './gradlew :test --tests "AppendoTest.testAppendo2"'
    @Test
    fun testAppendo2() {
        withEmptyContext {
            val a = logicListOf(0.toLogic(), 1.toLogic())
            val b = logicListOf(2.toLogic(), 3.toLogic())

            val goal = { q: Term<LogicList<LogicInt>> -> appendo(a, b, q) }
            val answers = run(1, goal)
            assert(answers.size == 1)
            println(answers[0])

            UnificationsController.onFinish()
        }
    }
}
