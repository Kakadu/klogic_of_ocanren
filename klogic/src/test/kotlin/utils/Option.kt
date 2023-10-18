package utils

import org.klogic.core.CustomTerm
import org.klogic.core.Term
import org.klogic.core.Var

/**
 * Represents logic list with elements of the specified logic type that can contain in the same time
 * elements of this type, or variables of this type.
 */
sealed class LogicOption<T : Term<T>> : CustomTerm<LogicOption<T>> {
    abstract val size: Int

    abstract fun isEmpty(): Boolean
    abstract operator fun get(index: Int): Term<T>
    //    abstract fun toList(): List<Term<T>>

    //    companion object {
    //        fun <T : Term<T>> logicOptionOf(vararg terms: Term<T>): LogicOption<T> {
    //            if (terms.isEmpty()) {
    //                return noneLogic()
    //            }
    //
    //            return Some(terms.first(), LogicOptionOf(*terms.drop(1).toTypedArray()))
    //        }
    //    }
}


object None : LogicOption<Nothing>() {
    @Suppress("UNCHECKED_CAST")
    fun <T : Term<T>> noneLogic(): LogicOption<T> = this as LogicOption<T>

    override val size: Int = 0

    override fun isEmpty(): Boolean = true

    override val subtreesToUnify: Array<Term<*>>
        get() = emptyArray()

    override fun constructFromSubtrees(
        subtrees: Iterable<*>): CustomTerm<LogicOption<Nothing>> = this

    override fun get(index: Int): Nothing = throw IndexOutOfBoundsException("This list is empty")

    //    override fun toList(): List<Term<Nothing>> = emptyList()

    override fun toString(): String = "None"
}

data class Some<T : Term<T>>(val head: Term<T>) : LogicOption<T>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(head)

    override val size: Int
        get() = 1

    override fun isEmpty(): Boolean = false

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<LogicOption<T>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return Some(head as Term<T>)
    }

    override fun toString(): String = "Some (${head.toString()})"

    override fun get(index: Int): Term<T> {
        require(index == 0) {
            "The $index should be 0, we always have a single element"
        }
        return head
    }

    //    override fun toList(): List<Term<T>> {
    //        val begin = listOf(head)
    //
    //        return begin + if (tail is LogicOption<T>) {
    //            tail.toList()
    //        } else {
    //            // Tail is Var
    //            tail as Var<LogicOption<T>>
    //            listOf(tail.cast())
    //        }
    //    }

}

fun <T : Term<T>> T?.toOption(): LogicOption<T> = if (this == null) None.noneLogic() else Some(this)
