@file:Suppress("SpellCheckingInspection")

package utils

import ID
import org.klogic.core.CustomTerm
import org.klogic.core.Term
import org.klogic.core.UnboundedValue
import org.klogic.utils.terms.LogicList
import utils.JGS.*

class JtypePretty(val getName: (Int) -> String?) {
    private fun ppJarg(jarg: Term<Jarg<Jtype<ID>>>, b: StringBuilder) {
        when (jarg) {
            is Type -> ppJtype(jarg.typ, b)
            is ArgWildcardProto<*> -> {
                when (val info = jarg.typ.asReified()) {
                    None -> b.append("*")
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

    private fun ppJtype(jt: Term<Jtype<ID>>, b: StringBuilder) : Unit =
        when (jt) {
            //is Null -> b.append("Null")
            is CustomTerm<*> -> {
                when (val t = jt.asReified()) {
                    is Intersect -> {
                        b.append("`intersect`")
                        Unit
                    }
                    is Class_ -> {
                        val name : String =
                            when (t.id) {
                                is CustomTerm -> {
                                    val id: Int = t.id.asReified().n
                                    getName(id)!!
                                }
                                else -> "FUCK"
                            }

                        b.append("Class $name")

                        when (t.args) {
                            is LogicList -> {
                                if (t.args.toList().isNotEmpty()) {
                                    b.append("<")
                                    t.args.toList().forEachIndexed { i, it ->
                                        if (i!=0) b.append(", ")
                                        this.ppJarg(it, b)
                                    }
                                    b.append(">")
                                }
                            }
                            else -> {
                                b.append("/*TODO*/")

                            }
                        }
                        Unit
                    }

                    is Interface -> {
                        val name : String =
                            when (t.id) {
                                is CustomTerm -> {
                                    val id: Int = t.id.asReified().n
                                    when (val rez = getName(id) ) {
                                         null -> TODO("Can't find an ID = $id")
                                         else -> rez
                                    }
                                }

                                else ->  "FUCK"
                            }

                        b.append("Interface $name")
                        when (t.args) {
                            is LogicList -> {
                                if (t.args.toList().isNotEmpty()) {
                                    b.append("<")
                                    t.args.toList().forEachIndexed { i, it ->
                                        if (i!=0) b.append(", ")
                                        this.ppJarg(it, b)
                                    }
                                    b.append(">")
                                }
                            }

                            else -> b.append("/*TODO*/")
                        }
                        Unit
                    }

                    is Array_ -> {
                        b.append("Array<")
                        ppJtype(t.typ, b)
                        b.append(">")
                        Unit
                    }

                    else -> {
                        b.append("/*TODO 2 */", t)
                        Unit
                    }
                }
            }

            else -> Unit
        }


    fun ppJtype(jt: Term<Jtype<ID>>): String {
        val b = StringBuilder()
        ppJtype(jt, b)
        return b.toString()
    }
}
