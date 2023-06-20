import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Test
import org.klogic.core.Term
import org.klogic.core.run
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.Symbol
import org.klogic.utils.terms.Symbol.Companion.toSymbol
import utils.UnificationsController
import utils.appendo

class AppendoTest {
    @AfterEach
    fun clear() {
        UnificationsController.onFinish()
    }

    // May be run manually using './gradlew :test --tests "AppendoTest.testAppendo1"'
    @Test
    fun testAppendo1() {
        val a = logicListOf("0".toSymbol())
        val b = logicListOf("1".toSymbol())

        val goal = { q: Term<LogicList<Symbol>> -> appendo(a, b, q) }
        val answers = run(1, goal)
        println(answers[0])

        UnificationsController.onFinish()
    }

    // May be run manually using './gradlew :test --tests "AppendoTest.testAppendo2"'
    @Test
    fun testAppendo2() {
        val a = logicListOf("0".toSymbol(), "1".toSymbol())
        val b = logicListOf("2".toSymbol(), "3".toSymbol())

        val goal = { q: Term<LogicList<Symbol>> -> appendo(a, b, q) }
        val answers = run(1, goal)
        println(answers[0])

        UnificationsController.onFinish()
    }
}
