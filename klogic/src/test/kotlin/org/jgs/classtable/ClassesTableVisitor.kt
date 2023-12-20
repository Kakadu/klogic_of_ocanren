package org.jgs.classtable

import org.jacodb.api.JcArrayType
import org.jacodb.api.JcBoundedWildcard
import org.jacodb.api.JcClassOrInterface
import org.jacodb.api.JcClassType
import org.jacodb.api.JcClasspath
import org.jacodb.api.JcPrimitiveType
import org.jacodb.api.JcRefType
import org.jacodb.api.JcType
import org.jacodb.api.JcTypeVariable
import org.jacodb.api.JcTypeVariableDeclaration
import org.jacodb.api.JcUnboundWildcard
import org.jacodb.api.PredefinedPrimitives
import org.jacodb.api.ext.objectClass
import org.jacodb.api.ext.toType
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.logicTo
import org.klogic.utils.terms.toLogicList
import org.klogic.utils.terms.toPeanoLogicNumber
import utils.JGS.*
import utils.JGS.PrimitiveType.PrimitiveBoolean
import utils.JGS.PrimitiveType.PrimitiveByte
import utils.JGS.PrimitiveType.PrimitiveChar
import utils.JGS.PrimitiveType.PrimitiveDouble
import utils.JGS.PrimitiveType.PrimitiveFloat
import utils.JGS.PrimitiveType.PrimitiveInt
import utils.JGS.PrimitiveType.PrimitiveLong
import utils.JGS.PrimitiveType.PrimitiveShort
import utils.JGS.PrimitiveType.PrimitiveVoid
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.None
import utils.toOption
import java.io.File

val EmptyClassTable = ClassesTable(
    classNames = (mutableMapOf()), table = mutableMapOf(), idOfName = mutableMapOf()
)

data class ClassesTable(
    val classNames: MutableMap<JcClassOrInterface, Int>,
    val table: MutableMap<Int, Decl<LogicInt>> = mutableMapOf(
        1 to C(
            params = logicListOf(), superClass = Class_(1.toLogic(), logicListOf()), logicListOf()
        ), 2 to I(
            params = logicListOf(), supers = logicListOf()
        ), 3 to I(
            params = logicListOf(), supers = logicListOf()
        )
    ),
    val idOfName: MutableMap<String, Int> = mutableMapOf(
        "java.lang.Object" to 1, "java.lang.Cloneable" to 2, "java.io.Serializable" to 3
    ),
    val nameOfId: MutableMap<Int, String> = mutableMapOf(
        1 to "java.lang.Object", 2 to "java.lang.Cloneable", 3 to "java.io.Serializable"
    ),
    val missingTypes: MutableSet<String> = mutableSetOf(),
    val kindOfId: MutableMap<Int, Jtype_kind> = mutableMapOf(
        1 to Class_kind, 2 to Interface_kind, 3 to Interface_kind
    ),
) {

    public var classPath: JcClasspath? = null
    private fun addName(name: String, id: Int) {
        check(!idOfName.containsKey(name))
        check(!nameOfId.containsKey(id))
        idOfName[name] = id
        nameOfId[id] = name
    }

    private var lastID = 10
    private fun mkId(name: String, kind: Jtype_kind): Int {
        assert(!name.contains('<'))
        return if (idOfName.containsKey(name)) {
            val id = idOfName[name]!!
            check(kindOfId[id] == kind) {
                "FUCK  $id. kind =  $kind, expectedKind = ${kindOfId[id]}"
            }
            idOfName[name]!!
        } else {
            lastID++
            addName(name, lastID)
            kindOfId[lastID] = kind
            lastID
        }
    }

    private fun Jtype<LogicInt>.toJvmTypeArgument(): Jarg<Jtype<LogicInt>> = Type(this)

    fun JcClassOrInterface.toDeclaration(classpath: JcClasspath) {
        val type = toType()
        val typeParams = type.typeParameters.mapIndexed { index, param ->
            toJtype(param, index, classpath, depth = 0)
        }.toLogicList()
        val preInterfaces =
            try { type.interfaces }
            catch (exc: org.jacodb.api.NoClassInClasspathException) {
                println("Class Load error for interfaces: $exc")
                listOf()
            }
        val supers = preInterfaces.map { it.toJtype(classpath, depth = 0) }.toLogicList()

        val decl = when {
            isInterface -> I(typeParams, supers)
            else -> {
                val superTyp =
                    try {
                        type.superType?.toJtype(classpath, depth = 0) ?: toJtype(
                            classpath.objectClass,
                            classpath, 0
                        )
                    } catch (exc: org.jacodb.api.NoClassInClasspathException) {
                        println("Substituting Object: $exc")
                        toJtype(classpath.objectClass,classpath, 0)
                    }
                C(typeParams, superTyp, supers)
            }
        }
        val name = this.name

        if (idOfName.containsKey(name) && table.containsKey(idOfName[name]!!)) {
            // We have already visited this type
            return
        } else {
            val kind = if (this.isInterface) Interface_kind else Class_kind
            val id = // TODO: only else is needed
                if (idOfName[name] != null) idOfName[name]!! else mkId(name, kind)

            //            if (table.containsKey(id)) {
            //                println("Current value: ${table[id]} with name = ${}")
            //                println("New value: ${decl}")
            //                checkt(!table.containsKey(id)) { String.format("Duplicate ID generated: $id") }
            //            }
            table[id] = decl
            check(idOfName[name] == id) {
                "FUCK"
            }
            table.containsKey(id)
        }
    }

    private fun JcClassType.toJtype(classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeParams = typeArguments.mapIndexed { index, param ->
            param.toJvmTypeArgument(index, classpath, depth + 1)
        }.toLogicList()

        val kind = if (jcClass.isInterface) Interface_kind else Class_kind
        val id = mkId(this.jcClass.name, kind)
        return if (jcClass.isInterface) Interface(id.toLogic(), typeParams)
        else Class_(id.toLogic(), typeParams)
    }

    private fun JcType.toJtype(
        index: Int, classpath: JcClasspath, depth: Int,
    ): Jtype<LogicInt> = when (this) {
        is JcRefType -> toJtype(this, index, classpath, depth + 1)
        is JcPrimitiveType -> typeName.toPrimitiveType()
        else -> error("Unknown JcType $this")
    }

    fun toJtype(refTyp: JcRefType, index: Int, classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        if (depth > 50) {
            TODO("Too deep recursive type")
        }
        return when (refTyp) {
            is JcArrayType -> Array_(refTyp.elementType.toJtype(index, classpath, depth + 1))
            is JcClassType -> refTyp.toJtype(classpath, depth + 1)
            is JcTypeVariable -> refTyp.toJtype(index, classpath, depth + 1)
            is JcBoundedWildcard -> error("Unexpected $this")
            is JcUnboundWildcard -> error("Unexpected $this")
            else -> error("Unknown ref type $this")
        }
    }

    private fun JcRefType.toJvmTypeArgument(
        index: Int, classpath: JcClasspath, depth: Int,
    ): Jarg<Jtype<LogicInt>> = when (this) {
        is JcArrayType -> Array_(
            elementType.toJtype(index, classpath, depth + 1)
        ).toJvmTypeArgument()

        is JcClassType -> toJtype(classpath, depth + 1).toJvmTypeArgument()
        is JcTypeVariable -> toJtype(index, classpath, depth + 1).toJvmTypeArgument()
        is JcBoundedWildcard -> toJvmTypeArgument(index, classpath, depth + 1)
        is JcUnboundWildcard -> Wildcard(None.noneLogic())
        else -> error("Unknown ref type $this")
    }

    private fun JcBoundedWildcard.toJvmTypeArgument(
        index: Int, classpath: JcClasspath, depth: Int,
    ): Jarg<Jtype<LogicInt>> {
        require(lowerBounds.isEmpty() != upperBounds.isEmpty())

        if (lowerBounds.isNotEmpty()) {
            require(lowerBounds.size == 1) {
                TODO()
            }

            val polarityJtypeLogicPair = Super logicTo lowerBounds.single()
                .toJtype(index, classpath, depth + 1)
            return Wildcard(polarityJtypeLogicPair.toOption())
        }

        require(upperBounds.size == 1) {
            TODO()
        }
        val jtypePair = Extends logicTo upperBounds.single().toJtype(index, classpath, depth + 1)
        return Wildcard(jtypePair.toOption())
    }

    fun JcTypeVariable.toJtype(index: Int, classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeBounds = bounds

        val upperBound = when {
            typeBounds.isEmpty() -> toJtype(classpath.objectClass, classpath, depth + 1)
            typeBounds.size == 1 -> typeBounds.single().toJtype(depth + 1, classpath, index)
            else -> Intersect(
                typeBounds.map { it.toJtype(depth + 1, classpath, index) }.toLogicList()
            )
        }

        return Var(
            symbol.hashCode().toLogic(), index.toPeanoLogicNumber(), upperBound, None.noneLogic()
        )
    }

    fun toJtype(varDecl: JcTypeVariableDeclaration,
        index: Int, classpath: JcClasspath, depth: Int,
    ): Jtype<LogicInt> {
        val typeBounds = varDecl.bounds
        val symbol = varDecl.symbol

        val upperBound = when {
            typeBounds.isEmpty() -> toJtype(classpath.objectClass, classpath, depth + 1)
            typeBounds.size == 1 -> toJtype(typeBounds.single(), depth + 1, classpath, index)
            else -> Intersect(
                typeBounds.map { toJtype(it, depth + 1, classpath, index) }.toLogicList()
            )
        }

        return Var(
            symbol.hashCode().toLogic(), index.toPeanoLogicNumber(), upperBound, None.noneLogic()
        )
    }

    fun toJtype(coi: JcClassOrInterface, classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeParams = coi.toType().typeArguments.mapIndexed { index, param ->
            param.toJvmTypeArgument(index, classpath, depth + 1)
        }.toLogicList()

        val name = coi.name
        if (idOfName.containsKey(name)) {
            val id = idOfName[name]!!
            return when (kindOfId[id]!!) {
                is Class_kind -> Class_(id.toLogic(), typeParams)
                is Interface_kind -> Interface(id.toLogic(), typeParams)
            }
        }
        return when (name) {
            "java.lang.Object" -> Class_(0.toLogic(), typeParams)
            "java.lang.Cloneable" -> Interface(1.toLogic(), typeParams)
            "java.io.Serializable" -> Interface(2.toLogic(), typeParams)
            else -> {
                val kind = if (coi.isInterface) Interface_kind else Class_kind
                val id: Int = this.mkId(coi.javaClass.name, kind)
                if (coi.isInterface) Interface(id.toLogic(), typeParams) else Class_(
                    id.toLogic(),
                    typeParams
                )
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    fun String.toPrimitiveType(): Jtype<LogicInt> = when (this) {
        PredefinedPrimitives.Byte -> PrimitiveByte
        PredefinedPrimitives.Short -> PrimitiveShort
        PredefinedPrimitives.Int -> PrimitiveInt
        PredefinedPrimitives.Long -> PrimitiveLong
        PredefinedPrimitives.Float -> PrimitiveFloat
        PredefinedPrimitives.Double -> PrimitiveDouble
        PredefinedPrimitives.Boolean -> PrimitiveBoolean
        PredefinedPrimitives.Char -> PrimitiveChar
        PredefinedPrimitives.Void -> PrimitiveVoid
        else -> error("Unknown primitive type $this")
    } as Jtype<LogicInt>

    private fun toJvmDeclarationsSafe(
        classes: List<JcClassOrInterface>,
        classpath: JcClasspath,
    ) = classes.forEach {
        it.toDeclaration(classpath)
    }

    companion object {
        fun makeClassesTable(
            classes: List<JcClassOrInterface>,
            classpath: JcClasspath,
        ): ClassesTable {
            println("Classes length = ${classes.size}")
            val table = ClassesTable(hashMapOf())
            table.toJvmDeclarationsSafe(classes, classpath)
            check(table.table.containsKey(1)) { "No object with ID=1 generated" }
            check(table.table.containsKey(2)) { "No object with ID=2 generated" }
            check(table.table.containsKey(3)) { "No object with ID=3 generated" }
            println("Table's last ID = ${table.lastID}")
//            println("9137 = ${table.table[9137]}")
//            println(
//                "table.idOfName[\"java.lang.Iterable\"] = ${
//                    table.idOfName["java.lang" +
//                            ".Iterable"]
//                }"
//            )
//            println("table.nameOfId[9137] = ${table.nameOfId[9137]}")
            table.classPath = classpath
            return table
        }
    }
}

fun extractClassesTable(cpFiles: List<File> = emptyList()): ClassesTable =
    extractClassesTableTask(cpFiles).use { (classes, classpath) ->
        ClassesTable.makeClassesTable(classes.sortedBy { it.name }, classpath)
    }.also {
        println(it.table.size)
    }

fun main() {
    val ct = extractClassesTable()
    val lookup = { clas: String ->
        println("\nLooking for $clas in the nameOfID")
        ct.nameOfId.forEach {
            if (it.value.contains(clas)) {
                check(ct.idOfName[it.value] == it.key)
                println("${it.key} ~~> ${it.value}")
                println("    --- ${ct.table[it.key]}")
            }
        }
    }
    lookup("Cloneable")
    lookup("AbstractList")
    lookup("java.util.Collection")
    lookup("java.util.List")
    lookup("java.lang.Iterable")

    lookup("java.util.AbstractList")
    lookup("<")

    //    println("\nLooking for AbstractList in the humanName")
    //    ct.nameOfId.forEach {
    //        if (it.value.contains("AbstractList")) {
    //            println("${it.key} ~~> ${it.value}")
    //            println("    --- ${ct.table[it.key]}")
    //        }
    //    }
    //    println("\nLooking for Cloneables in the declarations")
    //    ct.table.forEach {
    //        if (it.value.contains("Cloneable"))
    //            println("${it.key} ~~> ${it.value}")
    //    }
}
