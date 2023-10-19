@file:Suppress("ClassName", "PropertyName")

package utils.JGS

import org.klogic.core.CustomTerm
import org.klogic.core.Term
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicPair
import org.klogic.utils.terms.PeanoLogicNumber
import utils.LogicOption

sealed class Polarity : CustomTerm<Polarity>

object Extends : Polarity() {
    override val subtreesToUnify: Array<*> = emptyArray<Any?>()
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Polarity> = this
    override fun toString(): String = "Extends"

    @Suppress("UNCHECKED_CAST")
    operator fun invoke(): Polarity = this as Polarity
}

object Super : Polarity() {
    override val subtreesToUnify: Array<*> = emptyArray<Any?>()
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Polarity> = this
    override fun toString(): String = "Super"

    @Suppress("UNCHECKED_CAST")
    operator fun invoke(): Polarity = this as Polarity
}


sealed class Jarg<ID : Term<ID>> : CustomTerm<Jarg<ID>>

data class Type<ID : Term<ID>>(val typ: Term<ID>) : Jarg<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jarg<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return Type(head as Term<ID>)
    }
}

data class ArgWildcardProto<JTYP : Term<JTYP>>(
        val typ: Term<LogicOption<LogicPair<Polarity, JTYP>>>) : Jarg<JTYP>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jarg<JTYP>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return ArgWildcardProto(
                head as Term<LogicOption<LogicPair<Polarity, JTYP>>>)
    }
}

//typealias Targ<T> = ArgTypeProto<T >
typealias Wildcard<T> = ArgWildcardProto<T>

sealed class Jtype<ID : Term<ID>> : CustomTerm<Jtype<ID>>

sealed class PrimitiveType<ID : Term<ID>>(val jvmName: String) : Jtype<ID>() {
    object PrimitiveByte : PrimitiveType<Nothing>("byte")
    object PrimitiveShort : PrimitiveType<Nothing>("short")
    object PrimitiveInt : PrimitiveType<Nothing>("int")
    object PrimitiveLong : PrimitiveType<Nothing>("long")
    object PrimitiveFloat : PrimitiveType<Nothing>("float")
    object PrimitiveDouble : PrimitiveType<Nothing>("double")
    object PrimitiveBoolean : PrimitiveType<Nothing>("boolean")
    object PrimitiveChar : PrimitiveType<Nothing>("int")
    object PrimitiveVoid : PrimitiveType<Nothing>("void")

    override val subtreesToUnify: Array<*>
        get() = arrayOf<Any>()

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> = this
}

object Null : Jtype<Nothing>() {
    override val subtreesToUnify: Array<*> = emptyArray<Any?>()
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<Nothing>> = this
    override fun toString(): String = "Null_"

    @Suppress("UNCHECKED_CAST")
    operator fun <ID : Term<ID>> invoke(): Jtype<ID> = this as Jtype<ID>
}
//fun <ID : Term<ID>> Null() = Null_()

data class Array_<ID : Term<ID>>(val typ: Term<Jtype<ID>>) : Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(typ)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return Array_(head as Term<Jtype<ID>>)
    }
}

data class Intersect<ID : Term<ID>>(val args: Term<LogicList<Jtype<ID>>>) : Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(args)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val args = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only head and tail for constructing Cons but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return Intersect(args as Term<LogicList<Jtype<ID>>>)
    }
}

data class Class_<ID : Term<ID>>(val id: Term<ID>,
                                 val args: Term<LogicList<Jarg<Jtype<ID>>>>,
                                 val humanName_: String = "") :
        Jtype<ID>() {
    val  humanName: String = humanName_

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

        @Suppress("UNCHECKED_CAST") return Class_(head as Term<ID>,
                args as Term<LogicList<Jarg<Jtype<ID>>>>)
    }
}

// Interface is the same as Class but Interface. Maybe we should join this two concepts
data class TypeInterface<ID : Term<ID>>(val id: Term<ID>,
                                        val args: Term<LogicList<Jarg<Jtype<ID>>>>,
        val hname:String = ""
) : Jtype<ID>() {
    val humanName : String = hname
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

        @Suppress("UNCHECKED_CAST") return TypeInterface(head as Term<ID>,
                args as Term<LogicList<Jarg<Jtype<ID>>>>)
    }
}

data class Var<ID : Term<ID>>(val id: Term<ID>, val index: Term<PeanoLogicNumber>,
                              val upb: Term<Jtype<ID>>, val lwb: Term<LogicOption<Jtype<ID>>>) :
        Jtype<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, index, upb, lwb)

    @Suppress("UNCHECKED_CAST")
    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Jtype<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val head = iterator.next()
        val index = iterator.next() as Term<PeanoLogicNumber>
        val upb = iterator.next() as Term<Jtype<ID>>
        val lwb = iterator.next() as Term<LogicOption<Jtype<ID>>>

        require(!iterator.hasNext()) {
            "Expected only four arguments for constructing Java Variable, but got more elements"
        }
        return Var(head as Term<ID>, index, upb, lwb)
    }
}

typealias Interface<ID> = TypeInterface<ID>

sealed class Decl<ID : Term<ID>>() : CustomTerm<Decl<ID>> {
//    val humanName : String = ""
    abstract fun humanName() : String
}

data class C<ID : Term<ID>>(
        val params: Term<LogicList<Jtype<ID>>>,
        val superClass: Term<Jtype<ID>>,
        val supers: Term<LogicList<Jtype<ID>>>,
        val humanName: String = ""
) : Decl<ID>() {
    override fun humanName(): String  = humanName

    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(params, superClass, supers)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Decl<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val params = iterator.next()
        val superClass = iterator.next()
        val supers = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only params, super class and super interfaces for constructing C but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return C(params as Term<LogicList<Jtype<ID>>>,
                superClass as Term<Jtype<ID>>, supers as Term<LogicList<Jtype<ID>>>)
    }
}

data class I<ID : Term<ID>>(
        val params: Term<LogicList<Jtype<ID>>>,
        val supers: Term<LogicList<Jtype<ID>>>,
        val humanName: String = ""
) : Decl<ID>() {
    override fun humanName(): String  = humanName
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(params, supers)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<Decl<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val params = iterator.next()
        val supers = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only params and super interfaces for constructing I but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return I(params as Term<LogicList<Jtype<ID>>>,
                supers as Term<LogicList<Jtype<ID>>>)
    }
}

sealed class ClosureConversion<ID : Term<ID>> : CustomTerm<ClosureConversion<ID>> {}

data class CC_inter<ID : Term<ID>>(
        val one: Term<Jtype<ID>>,
        val another: Term<Jtype<ID>>,
) : ClosureConversion<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(one, another)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<ClosureConversion<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val one = iterator.next()
        val another = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only two types for constructing ClosureConversion intersection but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return CC_inter(one as Term<Jtype<ID>>,
                another as Term<Jtype<ID>>)
    }
}

data class CC_subst<ID : Term<ID>>(val one: Term<Jtype<ID>>) : ClosureConversion<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(one)

    override fun constructFromSubtrees(subtrees: Iterable<*>): CustomTerm<ClosureConversion<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val one = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only a types for constructing ClosureConversion substitution but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return CC_subst(one as Term<Jtype<ID>>)
    }

    companion object {
        fun <ID : Term<ID>> cc_inter(one: Term<Jtype<ID>>, another: Term<Jtype<ID>>):
                CC_inter<ID> = CC_inter(one, another)
    }
}

sealed class ClosureConversionType<ID : Term<ID>> : CustomTerm<ClosureConversionType<ID>>
data class CC_type<ID : Term<ID>>(val one: Term<Jtype<ID>>) : ClosureConversionType<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(one)

    override fun constructFromSubtrees(
            subtrees: Iterable<*>): CustomTerm<ClosureConversionType<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val one = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only a types for constructing ClosureConversion substitution but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return CC_type(one as Term<Jtype<ID>>)
    }
}

data class CC_var<ID : Term<ID>>(val id: Term<ID>, val index: Term<PeanoLogicNumber>,
                                 val subst: Term<ClosureConversion<ID>>,
                                 val bound: Term<LogicOption<Jtype<ID>>>) :
        ClosureConversionType<ID>() {
    override val subtreesToUnify: Array<Term<*>>
        get() = arrayOf(id, index, subst, bound)

    override fun constructFromSubtrees(
            subtrees: Iterable<*>): CustomTerm<ClosureConversionType<ID>> {
        // We use by-hand iteration here to avoid losing performance.
        val iterator = subtrees.iterator()
        val id = iterator.next()
        val index = iterator.next()
        val subst = iterator.next()
        val bound = iterator.next()

        require(!iterator.hasNext()) {
            "Expected only a types for constructing ClosureConversion substitution but got more elements"
        }

        @Suppress("UNCHECKED_CAST") return CC_var(id as Term<ID>, index as Term<PeanoLogicNumber>,
                subst as Term<ClosureConversion<ID>>, bound as Term<LogicOption<Jtype<ID>>>)
    }
}
