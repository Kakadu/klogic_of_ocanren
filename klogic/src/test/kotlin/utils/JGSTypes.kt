package utils.JGS

import org.klogic.core.CustomTerm
import org.klogic.core.Term
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicPair
import org.klogic.utils.terms.PeanoLogicNumber
import utils.LogicOption
import utils.Some

//import utils.JGS.Extends

sealed class Polarity : CustomTerm<Polarity> {
//    val size: Int = 0
}

object Extends : Polarity() {
    override val subtreesToUnify: Array<*> = emptyArray<Any?>()
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Polarity> = this
    override fun toString(): String = "Extends"
}

object Super : Polarity() {
    override val subtreesToUnify: Array<*> = emptyArray<Any?>()
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Polarity> = this
    override fun toString(): String = "Extends"
}


sealed class Jarg<T : Term<T>, T2 : Term<T2>> : CustomTerm<Jarg<T, T2>> {
//    val size: Int = 0
}

data class ArgTypeProto<T : Term<T>, T2 : Term<T2>>(val typ: Term<T>) : Jarg<T, T2>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jarg<T, T2>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return ArgTypeProto(head as Term<T>)
    }
}

data class ArgWildcardProto<T2 : Term<T2>, T : Term<T>>(val typ: Term<T>) :
    Jarg<T2, LogicOption<LogicPair<Polarity, T>>>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>)
            : CustomTerm<Jarg<T2, LogicOption<LogicPair<Polarity, T>>>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return ArgWildcardProto(head as Term<T>)
    }
}

typealias Targ<T> = Jarg<T, LogicOption<LogicPair<Polarity, T>>>

sealed class JtypeProto<ID : Term<ID>>
    : CustomTerm<JtypeProto<ID>> {
}

object Null : JtypeProto<Nothing>() {
    override val subtreesToUnify: Array<*> = emptyArray<Any?>()
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<JtypeProto<Nothing>> = this
    override fun toString(): String = "Extends"
}

data class TypeArrayProto<ID : Term<ID>>(val typ: Term<JtypeProto<ID>>) : JtypeProto<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<JtypeProto<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return TypeArrayProto(head as Term<JtypeProto<ID>>)
    }
}

data class TypeIntersect<ID : Term<ID>>(val left: Term<JtypeProto<ID>>, val right: Term<JtypeProto<ID>>) :
    JtypeProto<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(left, right)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<JtypeProto<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val left = iterator.next()
        val right = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return TypeIntersect(left as Term<JtypeProto<ID>>, right as Term<JtypeProto<ID>>)
    }
}

data class TypeClass_<ID : Term<ID>>(val id: Term<ID>, val args: Term<LogicList<Targ<JtypeProto<ID>>>>) :
    JtypeProto<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, args)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<JtypeProto<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()
        val args = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return TypeClass_(head as Term<ID>, args as Term<LogicList<Targ<JtypeProto<ID>>>>)
    }
}

// Interface is the same as Class but Interface. Maybe we should join this two concepts
data class TypeInterface<ID : Term<ID>>(val id: Term<ID>, val args: Term<LogicList<Targ<JtypeProto<ID>>>>) :
    JtypeProto<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, args)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<JtypeProto<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()
        val args = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return TypeClass_(head as Term<ID>, args as Term<LogicList<Targ<JtypeProto<ID>>>>)
    }
}

data class Var<ID : Term<ID>>(
    val id: Term<ID>,
    val args: Term<PeanoLogicNumber>,
    val upb: Term<JtypeProto<ID>>,
    val lwb: Term<LogicOption<JtypeProto<ID>>>
) :
    JtypeProto<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, args)

    @Suppress("UNCHECKED_CAST")
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<JtypeProto<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()
        val args = iterator.next() as Term<PeanoLogicNumber>
        val upb = iterator.next() as Term<JtypeProto<ID>>
        val lwb = iterator.next() as Term<LogicOption<JtypeProto<ID>>>

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }
        return Var(head as Term<ID>, args, upb, lwb)
    }
}

typealias Intersect<ID> = TypeIntersect<ID>
typealias Array_<ID> = TypeArrayProto<ID>
typealias Class_<ID> = TypeClass_<ID>
typealias Interface<ID> = TypeInterface<ID>
typealias Jtype<ID> = JtypeProto<ID>
