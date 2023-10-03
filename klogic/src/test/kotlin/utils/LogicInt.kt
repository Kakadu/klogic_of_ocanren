package utils

import org.klogic.core.*

@JvmInline
value class LogicInt(val n: Int) : CustomTerm<LogicInt> {
    override val subtreesToUnify: Array<*>
        get() = arrayOf(n)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<LogicInt> =
        // A performance optimization - an integer never changes, so we can omit arguments
        this

    override fun toString(): String = n.toString()
    fun prjExn() = n

    companion object {
        fun Int.toLogic(): LogicInt = LogicInt(this)
    }
}
