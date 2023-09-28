package utils.JGS

import org.klogic.core.CustomTerm
import org.klogic.core.Term
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicPair
import org.klogic.utils.terms.PeanoLogicNumber
import utils.LogicOption

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


sealed class Jarg<ID : Term<ID>> : CustomTerm<Jarg<ID>> {
//    val size: Int = 0
}

data class Type<ID : Term<ID>>(val typ: Term<ID>) : Jarg<ID >() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jarg<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return Type(head as Term<ID>)
    }
}

data class ArgWildcardProto<JTYP : Term<JTYP> >(val typ: Term<LogicOption<LogicPair<Polarity, JTYP>>>) :
    Jarg<JTYP >() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>)
            : CustomTerm<Jarg<JTYP >> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return ArgWildcardProto(head as  Term<LogicOption<LogicPair<Polarity, JTYP>>>)
    }
}

//typealias Targ<T> = ArgTypeProto<T >
typealias Wildcard<T> = ArgWildcardProto<T>

sealed class Jtype<ID : Term<ID>>
    : CustomTerm<Jtype<ID>> {
}

object Null : Jtype<Nothing>() {
    override val subtreesToUnify: Array<*> = emptyArray<Any?>()
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<Nothing>> = this
    override fun toString(): String = "Null_"

    @Suppress("UNCHECKED_CAST")
    operator fun <ID : Term<ID>> invoke(): Jtype<ID> = this as Jtype<ID>
}
//fun <ID : Term<ID>> Null() = Null_()

data class TypeArrayProto<ID : Term<ID>>(val typ: Term<Jtype<ID>>) : Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return TypeArrayProto(head as Term<Jtype<ID>>)
    }
}

data class Intersect<ID : Term<ID>>(val args: Term<LogicList<Jtype<ID>>>) :
    Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(args)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val args = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return Intersect(args as Term<LogicList<Jtype<ID>>>)
    }
}

data class TypeClass_<ID : Term<ID>>(val id: Term<ID>,
                                     val args: Term<LogicList<Jarg<Jtype<ID>>>>
) :
    Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, args)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()
        val args = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return TypeClass_(head as Term<ID>, args as Term<LogicList<Jarg<Jtype<ID>>>>)
    }
}

// Interface is the same as Class but Interface. Maybe we should join this two concepts
data class TypeInterface<ID : Term<ID>>(val id: Term<ID>,
                                        val args: Term<LogicList<Jarg<Jtype<ID>>>>) :
    Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, args)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()
        val args = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST")
        return TypeClass_(head as Term<ID>, args as Term<LogicList<Jarg<Jtype<ID>>>>)
    }
}

data class Var<ID : Term<ID>>(
    val id: Term<ID>,
    val args: Term<PeanoLogicNumber>,
    val upb: Term<Jtype<ID>>,
    val lwb: Term<LogicOption<Jtype<ID>>>
) :
    Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, args)

    @Suppress("UNCHECKED_CAST")
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()
        val args = iterator.next() as Term<PeanoLogicNumber>
        val upb = iterator.next() as Term<Jtype<ID>>
        val lwb = iterator.next() as Term<LogicOption<Jtype<ID>>>

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }
        return Var(head as Term<ID>, args, upb, lwb)
    }
}


typealias Array_<ID> = TypeArrayProto<ID>
typealias Class_<ID> = TypeClass_<ID>
typealias Interface<ID> = TypeInterface<ID>
