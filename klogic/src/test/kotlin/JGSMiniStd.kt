import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.ZeroNaturalNumber
import org.klogic.utils.terms.toPeanoLogicNumber
import utils.JGS.*
import utils.JGS.Closure.CLOSURE
import utils.JGS.Closure.Closure
import utils.JGS.Var
import utils.JtypePretty
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.LogicOption

@Suppress("NAME_SHADOWING")
class JGSMiniStd {
    @AfterEach
    fun clear() {

    }

    fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    @Test
    @DisplayName("Wanna specify a domain and cut type variables.")
    fun test0wildcards() {
        withEmptyContext {
            val dom: (Term<Jtype<ID>>) -> Goal = { it ->
                conde(it `===` Class_(1.toLogic(), logicListOf()),
                    it `===` Interface(2.toLogic(), logicListOf()),
                    freshTypedVars { c: Term<Jtype<ID>>, d: Term<LogicOption<Jtype<ID>>> ->
                        it `===` Var(4.toLogic(), ZeroNaturalNumber, c, d)
                    })
            }
            val goal: (Term<Jtype<ID>>) -> Goal = { it ->
                and( // I expect that next lines removes all Type Variables, but it doesn't
                    it `!==` Var(wildcard(), wildcard(), wildcard(), wildcard()), dom(it))
            }
            val answers = run(10, goal).map { it.term }.toList()
            val expectedTerm = listOf(Class_(1.toLogic(), logicListOf()),
                Interface(2.toLogic(), logicListOf())).toCountMap()
            Assertions.assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    enum class ClosureType {
        Subtyping, SuperTyping
    }


    // new revised by Peter
    // specifies upper bound
    fun prepareTest(expectedResult: (MutableClassTable) -> Collection<String>, count: Int = 10,
                    init: (MutableClassTable) -> Unit = { },
                    boundKind: ClosureType = ClosureType.Subtyping, verbose: Boolean = false,
                    bound: (RelationalContext, MutableClassTable) -> Term<Jtype<ID>>) {
        val classTable = DefaultCT()
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)
        init(classTable)
        withEmptyContext {
            val g = { q: Term<Jtype<ID>> ->
                and(only_classes_interfaces_and_arrays(q), (when (boundKind) {
                    ClosureType.Subtyping -> JGSBackward.MakeClosure2(closureBuilder)
                        .closure({ a, b, c, d ->
                            v.minus_less_minus(a, b, c, d)
                        }, q, bound(this, classTable))

                    ClosureType.SuperTyping -> JGSBackward.MakeClosure2(closureBuilder)
                        .closure({ a, b, c, d ->
                            v.minus_less_minus(a, b, c, d)
                        }, bound(this, classTable), q)
                }))
            }
            val pPrinter = JtypePretty { n -> classTable.nameOfId(n) }
            val answers = run(count, g).map { it.term }.toList().map { pPrinter.ppJtype(it) }
            answers.forEachIndexed { i, x ->
                println("$i: $x") //                println("-   ${pPrinter.ppJtype(x)}")
            }

            assertEquals(count, answers.count())
            assertEquals(expectedResult(classTable).toCountMap(), answers.toCountMap())
        }
    }

    @Test
    @DisplayName("Super Interfaces of AbstractCollection")
    fun test8() {
        var abstractCollectionTyp: Term<Jtype<ID>>? = null

        val init: (MutableClassTable) -> Unit = { ct: MutableClassTable ->
            val iIterableID = ct.addInterface(params = logicListOf(), logicListOf())
            println("iterableID = $iIterableID")
            ct.addName(iIterableID, "Iterable")

            val iCollectionID = ct.addInterface(params = logicListOf(),
                logicListOf(Interface(iIterableID.toLogic(), logicListOf())))
            ct.addName(iCollectionID, "Collection")
            val iAbsCollectionID = ct.addInterface(params = logicListOf(),
                logicListOf(Interface(iCollectionID.toLogic(), logicListOf())))
            ct.addName(iAbsCollectionID, "AbstractCollection")
            println("iAbsCollectionID = $iAbsCollectionID")
            abstractCollectionTyp = Interface(iAbsCollectionID.toLogic(), logicListOf())
        }
        val expectedResult: (MutableClassTable) -> Collection<String> = { ct ->
            val pprinter = JtypePretty { ct.nameOfId(it) }
            listOf(
                Interface(id = ct.idOfName("AbstractCollection")!!.toLogic(), logicListOf()),
                Interface(id = ct.idOfName("Collection")!!.toLogic(), logicListOf()),
                Interface(id = ct.idOfName("Iterable")!!.toLogic(), logicListOf()),
            ).map { pprinter.ppJtype(it) }
        }
        prepareTest(expectedResult = expectedResult, count = 3, init = init,
            boundKind = ClosureType.SuperTyping,
            verbose = false) { ctx: RelationalContext, ct: MutableClassTable ->
            abstractCollectionTyp!!
        }
    }

    @Test
    @DisplayName("Sub Interfaces of Iterable")
    fun test9() {
        var iterableTyp: Term<Jtype<ID>>? = null

        val init: (MutableClassTable) -> Unit = { ct: MutableClassTable ->
            val iIterableID = ct.addInterface(params = logicListOf(), logicListOf())
            ct.addName(iIterableID, "Iterable")
            println("iterableID = $iIterableID")

            iterableTyp = Interface(iIterableID.toLogic(), logicListOf())
            val iCollectionID = ct.addInterface(params = logicListOf(),
                logicListOf(Interface(iIterableID.toLogic(), logicListOf())))
            ct.addName(iCollectionID, "Collection")
            val iAbsCollectionID = ct.addInterface(params = logicListOf(),
                logicListOf(Interface(iCollectionID.toLogic(), logicListOf())))
            ct.addName(iAbsCollectionID, "AbstractCollection")
            println("iAbsCollectionID = $iAbsCollectionID")

        }
        val expectedResult: (MutableClassTable) -> Collection<String> = { ct ->
            val pprinter = JtypePretty { ct.nameOfId(it) }
            listOf(
                Interface(id = ct.idOfName("AbstractCollection")!!.toLogic(), logicListOf()),
                Interface(id = ct.idOfName("Collection")!!.toLogic(), logicListOf()),
                Interface(id = ct.idOfName("Iterable")!!.toLogic(), logicListOf()),
            ).map { pprinter.ppJtype(it) }
        }
        prepareTest(expectedResult = expectedResult, count = 3, init = init,
            boundKind = ClosureType.Subtyping,
            verbose = false) { _: RelationalContext, _: MutableClassTable ->
            iterableTyp!!
        }
    }


    @Test
    @DisplayName("Sub Interfaces of Iterable<T>")
    fun test10() {
        var iIterableID: Int? = null
        var intType: Term<Jtype<ID>>? = null
        var iterableObjectTyp: Term<Jtype<ID>>? = null

        val init: (MutableClassTable) -> Unit = { ct: MutableClassTable ->
            iIterableID = ct.addInterface(params = logicListOf(
                Var(100.toLogic(), 0.toPeanoLogicNumber(), ct.object_t, lwb = None())),
                supers = logicListOf())
            ct.addName(iIterableID!!, "Iterable")

            val StringID = ct.addClass(params = logicListOf(), superClass = ct.object_t,
                supers = logicListOf())
            ct.addName(StringID, "String")

            val IntID = ct.addClass(params = logicListOf(), superClass = ct.object_t,
                supers = logicListOf())
            ct.addName(IntID, "Int")
            intType = Class_(IntID.toLogic(), logicListOf())

            val stringType = Class_(StringID.toLogic(), logicListOf())
            iterableObjectTyp = Interface(iIterableID!!.toLogic(),
                logicListOf(Type(ct.object_t)))

            val SpecIterableIntID = ct.addClass(params = logicListOf(),
                superClass = ct.object_t,
                supers = logicListOf(
                    Interface(iIterableID!!.toLogic(), args = logicListOf(Type(intType!!)))))

            ct.addName(SpecIterableIntID, "SpecializedIterableInt")
            println("SpecIterableIntID = $SpecIterableIntID")
            val specIterableIntType = Class_(SpecIterableIntID.toLogic(), logicListOf())
        }
        val expectedResult: (MutableClassTable) -> Collection<String> = { ct ->
            val pprinter = JtypePretty { ct.nameOfId(it) }
            listOf(
                Interface(ct.idOfName("Iterable")!!.toLogic(),
                    args = logicListOf(Type(ct.object_t))
                )
            ).map { pprinter.ppJtype(it) }
        }

        // TODO: Why only single answer
        prepareTest(
            expectedResult = expectedResult,
            count = 1,
            init = init,
            boundKind = ClosureType.Subtyping,
            verbose = false
        ) { _: RelationalContext, _: MutableClassTable ->
            iterableObjectTyp!!
        }

        val expectedResult2: (MutableClassTable) -> Collection<String> = { ct ->
            val pprinter = JtypePretty { ct.nameOfId(it) }
            listOf(
                Interface(ct.idOfName("Iterable")!!.toLogic(),
                    args = logicListOf(
                        Type(Class_(ct.idOfName("Int")!!.toLogic(), logicListOf())))
                ),
                Class_(ct.idOfName("SpecializedIterableInt")!!.toLogic(), logicListOf())
            ).map { pprinter.ppJtype(it) }
        }
        prepareTest(expectedResult = expectedResult2, count = 2, init = init,
            boundKind = ClosureType.Subtyping,
            verbose = false) { _: RelationalContext, _: MutableClassTable ->
            Interface(iIterableID!!.toLogic(), args = logicListOf(Type(intType!!)))
        }
    }
}
