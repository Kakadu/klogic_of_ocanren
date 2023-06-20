import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.klogic.core.Term
import org.klogic.core.Var.Companion.createTypedVar
import org.klogic.core.run
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.PeanoLogicNumber
import org.klogic.utils.terms.Symbol
import org.klogic.utils.terms.Symbol.Companion.toSymbol
import org.klogic.utils.terms.toLogicList
import utils.UnificationsController
import utils.reverso
import utils.sortᴼ
import utils.toPeanoLogicNumber
import kotlin.time.ExperimentalTime
import kotlin.time.measureTimedValue

class PermutationsTest {
    @AfterEach
    fun clear() {
        UnificationsController.onFinish()
    }

    // May be run manually using './gradlew :test --tests "PermutationsTest.testPermutations"'
    @OptIn(ExperimentalTime::class)
    @Test
    fun testReverso() {
        val size = 4

        val unsortedList = (-1).createTypedVar<LogicList<PeanoLogicNumber>>()

        val sortedList = (1..size).map { it.toPeanoLogicNumber() }.toLogicList()

        val goal = sortᴼ(unsortedList, sortedList)

        val count = (1..size).reduce(Int::times)
        val run = measureTimedValue { run(count + 1, unsortedList, goal) }

        assertEquals(count, run.value.size)

        UnificationsController.onFinish()
    }
}