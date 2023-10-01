import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Test
import org.klogic.core.Term
import utils.*


class OlegNumbersTest {
    @AfterEach
    fun clear() {
        UnificationsController.onFinish()
    }

    @Test
    fun testAdd0x0() {
        withEmptyContext {
            val a = 0u.toOlegLogicNumber()
            val b = 0u.toOlegLogicNumber()

            println("$a + $b")
            run(1, { r: Term<OlegLogicNumber> -> pluso(a, b, r) }).forEachIndexed { i, x ->
                println("$i: $x")
            }
            UnificationsController.onFinish()
        }
    }

    @Test
    fun testPoso0() {
        withEmptyContext {
            val b = 0u.toOlegLogicNumber()

            println("poso? $b")
            val lst = run(1, { _: Term<OlegLogicNumber> -> poso(b) })
//        println("lst = $lst" )
            assert(lst.size == 0);
        }
    }

    @Test
    fun testPoso1() {
        withEmptyContext {
            val b = 1u.toOlegLogicNumber()

            println("poso? $b")
            val lst = run(1, { _: Term<OlegLogicNumber> -> poso(b) })
//        println("lst = $lst" )
            assert(lst.size == 1);
        }
    }

    @Test
    fun testAdd0x1() {
        withEmptyContext {
            val a = 0u.toOlegLogicNumber()
            val b = 1u.toOlegLogicNumber()

            println("$a + $b")
            run(1, { r: Term<OlegLogicNumber> -> pluso(a, b, r) }).forEachIndexed { i, x ->
                println("==== $i: $x")
            }
        }
    }

    @Test
    fun testAdd1x1() {
        withEmptyContext {
            val a = 1u.toOlegLogicNumber()

            val b = 1u.toOlegLogicNumber()

            println("$a + $b")
            run(1, { r: Term<OlegLogicNumber> -> pluso(a, b, r) }).forEachIndexed { i, x ->
                println("$i: $x")
            }
            UnificationsController.onFinish()
        }
    }

    @Test
    fun testAdd2x3() {
        withEmptyContext {
            val a = 2u.toOlegLogicNumber()
            val b = 3u.toOlegLogicNumber()

            println("$a + $b")
            run(1, { r: Term<OlegLogicNumber> -> pluso(a, b, r) }).forEachIndexed { i, x ->
                println("$i: $x")
            }
            UnificationsController.onFinish()
        }
    }

    @Test
    fun testMul2x3() {
        withEmptyContext {
            val a = 2u.toOlegLogicNumber()
            val b = 3u.toOlegLogicNumber()

            println("$a * $b")
            run(1, { r: Term<OlegLogicNumber> -> multo(a, b, r) })
                    .forEachIndexed { i, x ->
                        println("$i: $x")
                    }
            UnificationsController.onFinish()
        }
    }

    @Test
    fun testMul3x3() {
        withEmptyContext {
            val a = 3u.toOlegLogicNumber()
            val b = 3u.toOlegLogicNumber()

            println("$a * $b")
            run(1, { r: Term<OlegLogicNumber> -> multo(a, b, r) })
                    .forEachIndexed { i, x ->
                        println("$i: $x")
                    }
            UnificationsController.onFinish()
        }
    }

    /*
    @Test
    fun testMul5x5() {
        val a = 5u.toOlegLogicNumber()
        val b = 5u.toOlegLogicNumber()
    
        println("$a * $b")
        run(1, { r: Term<OlegLogicNumber> -> mulᴼ(a, b, r) })
        UnificationsController.onFinish()
    }
    @Test
    fun testMul5x5all() {
        val a = 5u.toOlegLogicNumber()
        val b = 5u.toOlegLogicNumber()
    
        println("$a * $b")
        run(5, { r: Term<OlegLogicNumber> -> mulᴼ(a, b, r) })
        UnificationsController.onFinish()
    }
    @Test
    fun testMul127x127() {
        val a = 127u.toOlegLogicNumber()
        val b = 127u.toOlegLogicNumber()
    
        println("$a * $b")
        run(5, { r: Term<OlegLogicNumber> -> mulᴼ(a, b, r) })
        UnificationsController.onFinish()
    }
    
    @Test
    fun testMul255x255() {
        val a = 255u.toOlegLogicNumber()
        val b = 255u.toOlegLogicNumber()
    
        println("$a * $b")
        run(5, { r: Term<OlegLogicNumber> -> mulᴼ(a, b, r) })
        UnificationsController.onFinish()
    }
    
    @Test
    fun testExpo1x2() {
        val base = 1u.toOlegLogicNumber()
        val power = 2u.toOlegLogicNumber()
    
        println("$base^$power")
        run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
        UnificationsController.onFinish()
    }
    
    @Test
    fun testExpo2x1() {
        val base = 2u.toOlegLogicNumber()
        val power = 1u.toOlegLogicNumber()
    
        println("$base^$power")
        run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
        UnificationsController.onFinish()
    }
    
    @Test
    fun testExpo2x2() {
        val base = 2u.toOlegLogicNumber()
        val power = 2u.toOlegLogicNumber()
    
        println("$base^$power")
        run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
        UnificationsController.onFinish()
    }
    */
    @Test
    fun testExpo2x3() {
        withEmptyContext {
            val base = 2u.toOlegLogicNumber()
            val power = 3u.toOlegLogicNumber()

            println("$base^$power")
            run(1, { r: Term<OlegLogicNumber> -> expo(base, power, r) })
                    .forEachIndexed { i, x ->
                        println("$i: $x")
                    }
            UnificationsController.onFinish()
        }
    }
    /*
        @Test
        fun testExpo2x5() {
            val base = 2u.toOlegLogicNumber()
            val power = 5u.toOlegLogicNumber()
    
            println("$base^$power")
            run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
            UnificationsController.onFinish()
        }
    
        @Test
        fun testExpo3x2() {
            val base = 3u.toOlegLogicNumber()
            val power = 2u.toOlegLogicNumber()
    
            println("$base^$power")
            val answers = run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
            println(answers[0].term)
            UnificationsController.onFinish()
        }
    
        @Test
        fun testExpo3x5() {
            val base = 3u.toOlegLogicNumber()
            val power = 5u.toOlegLogicNumber()
    
            println("$base^$power")
            val answers = run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
            println(answers[0].term)
            UnificationsController.onFinish()
        }
    
        @Test
        fun testExpo7x2() {
            val base = 7u.toOlegLogicNumber()
            val power = 2u.toOlegLogicNumber()
    
            println("$base^$power")
            val answers = run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
            println(answers[0].term)
            UnificationsController.onFinish()
        }
    
        @Test
        fun testLogo8base2() {
            val n = 8u.toOlegLogicNumber()
            val b = 2u.toOlegLogicNumber()
            val r = 0u.toOlegLogicNumber()
    
            println("log $n base $b with reminder $r")
            run(1, { q: Term<OlegLogicNumber> -> logᴼ(n, b, q, r) })
    
            UnificationsController.onFinish()
        }
        @Test
        fun testLogo243base3() {
            val n = 243u.toOlegLogicNumber()
            val b = 3u.toOlegLogicNumber()
            val r = 0u.toOlegLogicNumber()
    
            println("log $n base $b with reminder $r")
            run(1, { q: Term<OlegLogicNumber> -> logᴼ(n, b, q, r) })
    
            UnificationsController.onFinish()
        }
        @Test
        fun testExpo3() {
            val base = 2u.toOlegLogicNumber()
            val power = 2u.toOlegLogicNumber()
    
            println("$base^$power")
            run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
            UnificationsController.onFinish()
        }
    
        @Test
        fun testExpo4() {
            val base = 2u.toOlegLogicNumber()
            val power = 1u.toOlegLogicNumber()
    
            println("$base^$power")
            run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
            UnificationsController.onFinish()
        }
    
        @Test
        fun testExpo5() {
            val base = 3u.toOlegLogicNumber()
            val power = 2u.toOlegLogicNumber()
    
            println("$base^$power")
            val answers = run(1, { r: Term<OlegLogicNumber> -> expᴼ(base, power, r) })
            println(answers[0].term)
            UnificationsController.onFinish()
        }
        @Test
        fun testMul1() {
            val a = 3u.toOlegLogicNumber()
            val b = 3u.toOlegLogicNumber()
    
            println("$a * $b")
            run(1, { r: Term<OlegLogicNumber> -> mulᴼ(a, b, r) })
            UnificationsController.onFinish()
        }
    
        @Test
        fun testRepeatedMul1() {
            val a = 3u.toOlegLogicNumber()
            val b = 2u.toOlegLogicNumber()
    
            println("repeatedMul($a, $b, ?)")
            run(1, { r: Term<OlegLogicNumber> -> repeatedMulᴼ(a, b, r) })
            UnificationsController.onFinish()
        }
    
        @Test
        fun testOddMul1() {
            val q = 1u.toOlegLogicNumber()
            val a = 3u.toOlegLogicNumber()
            val b = 3u.toOlegLogicNumber()
    
            println("oddMulo($1, $a, $b)")
            run(1, { r: Term<OlegLogicNumber> -> oddMulᴼ(q, a, b, r) })
            UnificationsController.onFinish()
        }
    */


}
