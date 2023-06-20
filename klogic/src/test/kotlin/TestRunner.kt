import kotlin.reflect.KFunction0

private val tasks: Map<String, KFunction0<Unit>> = mapOf(
//    "appendo1" to AppendoTest()::testAppendo1,
//    "appendo2" to AppendoTest()::testAppendo2,
//    "reverso" to ReversoTest()::testReverso,
//    "reverso2" to ReversoTest()::testReverso2,
    "add2x3" to OlegNumbersTest()::testAdd2x3,
//    "mul2x3" to OlegNumbersTest()::testMul2x3,
//    "mul3x3" to OlegNumbersTest()::testMul3x3,
//    "mul5x5" to OlegNumbersTest()::testMul5x5,
//    "mul5x5-all" to OlegNumbersTest()::testMul5x5all,
//    "mul127x127" to OlegNumbersTest()::testMul127x127,
//    "mul255x255" to OlegNumbersTest()::testMul255x255,
//    "exp1x2" to OlegNumbersTest()::testExpo1x2,
//    "exp2x1" to OlegNumbersTest()::testExpo2x1,
//    "exp2x2" to OlegNumbersTest()::testExpo2x2,
//    "exp2x3" to OlegNumbersTest()::testExpo2x3,
//    "exp2x5" to OlegNumbersTest()::testExpo2x5,
//    "exp3x2" to OlegNumbersTest()::testExpo3x2,
//    "exp3x5" to OlegNumbersTest()::testExpo3x5,
//    "exp7x2" to OlegNumbersTest()::testExpo7x2,
//    "logo8base2" to OlegNumbersTest()::testLogo8base2,
//    "logo243base3" to OlegNumbersTest()::testLogo243base3,
//    "expo3" to OlegNumbersTest()::testExpo3,
//    "expo4" to OlegNumbersTest()::testExpo4,
//    "expo5" to OlegNumbersTest()::testExpo5,
//    "mul1" to OlegNumbersTest()::testMul1,
//    "repeatedMul1" to OlegNumbersTest()::testRepeatedMul1,
//    "odd_mul1" to OlegNumbersTest()::testOddMul1,

)

fun main(args: Array<String>) {
    args.singleOrNull()?.let {
        tasks[it]?.invoke()
    } ?: System.err.println(
        """
"Unknown command ${args.contentToString()}, available commands
${tasks.keys.joinToString(System.lineSeparator())}
        """.trimIndent()
    )
}
