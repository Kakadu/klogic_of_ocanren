@file:Suppress("SpellCheckingInspection")

package utils

import ID
import org.klogic.core.CustomTerm
import org.klogic.core.Term
import org.klogic.core.UnboundedValue
import org.klogic.utils.terms.LogicList
import utils.JGS.*

class JtypePretty(val getName: (Int) -> Decl<LogicInt>?) {
    fun ppJarg(jarg: Term<Jarg<Jtype<ID>>>, b: StringBuilder) {
        when (jarg) {
            is Type -> {
                val jtyp : Term<Jtype<ID>> = jarg.typ as Term<Jtype<ID>>
                ppJtype(jtyp, b)
            }
            is ArgWildcardProto<*> -> {
                when (val info = jarg.typ.asReified()) {
                    utils.None -> b.append("*")
                    is Some -> {
                        b.append("*")
                        val p = info.head.asReified()
                        when (p.first) {
                            is Extends -> b.append(" extends ")
                            is Super -> b.append(" super ")
                            else -> TODO()
                        }
                        b.append(p.second)
                    }
                }
            }

            is CustomTerm<*> -> TODO()
            is UnboundedValue<*> -> b.append("_.?")
        }
    }

    fun ppJtype(jt: Term<Jtype<ID>>, b: StringBuilder) {
        when (jt) {
            //is Null -> b.append("Null")
            is CustomTerm<*> -> {
                when (val t = jt.asReified()) {
                    is Intersect -> b.append("`intersect`")
                    is Class_ -> {
                        val name =
                            when (t.id) {
                                is CustomTerm -> {
                                    val id: Int = t.id.asReified().n
                                    val decl: Decl<LogicInt> = getName(id)!!
                                    decl.humanName()
                                }
                                else -> "FUCK"
                            }

                        b.append("Class $name")
                        when (t.args) {
                            is LogicList -> {
                                if (t.args.toList().isNotEmpty()) {
                                    b.append("<")
                                    t.args.toList().forEach { this.ppJarg(it, b); b.append(", ") }
                                    b.append(">")
                                }
                            }

                            else -> b.append("/*TODO*/")
                        }
                    }

                    is Interface -> {
                        val name =
                            when (t.id) {
                                is CustomTerm -> {
                                    val id: Int = t.id.asReified().n
                                    val decl: Decl<LogicInt> = getName(id)!!
                                    decl.humanName()
                                }
                                else -> "FUCK"
                            }

                        b.append("Interface ${name}")
                        when (t.args) {
                            is LogicList -> {
                                if (t.args.toList().isNotEmpty()) {
                                    b.append("<")
                                    t.args.toList().forEach { this.ppJarg(it, b); b.append(", ") }
                                    b.append(">")
                                }
                            }

                            else -> b.append("/*TODO*/")
                        }
                    }

                    is Array_ -> {
                        b.append("Array<")
                        b.append(ppJtype(t.typ, b))
                        b.append(">")
                    }

                    else -> b.append("/*TODO*/", t, t.javaClass)
                }
            }

            else -> {}
        }
    }

    fun ppJtype(jt: Term<Jtype<ID>>): String {
        val b = StringBuilder()
        ppJtype(jt, b);
        return b.toString()
    }
}
