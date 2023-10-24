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

val EmptyClassTable = ClassesTable(classNames = (mutableMapOf()), table = mutableMapOf(),
    idOfName = mutableMapOf())

data class ClassesTable(
    val classNames: MutableMap<JcClassOrInterface, Int>,
    val table: MutableMap<Int, Decl<LogicInt>> = mutableMapOf(
        1 to C(params = logicListOf(),
            superClass = Class_(1.toLogic(), logicListOf(), "java.lang.Object"),
            logicListOf(),
            humanName = "java.lang.Object"),
        2 to I(params = logicListOf(),
            supers = logicListOf(),
            humanName = "java.lang.Cloneable"),
        3 to I(params = logicListOf(),
            supers = logicListOf(),
            humanName = "java.io.Serializable")
        ),
    val idOfName: MutableMap<String, Int> = mutableMapOf(
        "java.lang.Object" to 1,
        "java.lang.Cloneable" to 2,
        "java.io.Serializable" to 3
    ),
    val missingTypes: MutableSet<String> = mutableSetOf()
) {

    private fun addName(name: String, id: Int) {
        //        println ("Add name $name ~~> $id")
        assert(!idOfName.containsKey(name))
        idOfName[name] = id
    }

    private var lastID = 10
    private fun JcClassOrInterface.mkId(name: String): Int {
        return if (idOfName.containsKey(name))
            idOfName[name]!!
        else {
            lastID++;
            addName(name, lastID)
            lastID
        }
    }

    private fun Jtype<LogicInt>.toJvmTypeArgument(): Jarg<Jtype<LogicInt>> = Type(this)

    fun JcClassOrInterface.toDeclaration(classpath: JcClasspath) {
        val type = toType()
        val typeParams =
            type.typeParameters.mapIndexed { index, param ->
                param.toJtype(index, classpath, depth = 0)
            }.toLogicList()
        val supers = type.interfaces.map { it.toJtype(classpath, depth = 0) }.toLogicList()

        val decl = when {
            isInterface -> I(typeParams, supers, humanName = this.simpleName)
            else -> C(
                typeParams,
                type.superType?.toJtype(classpath, depth = 0) ?: classpath.objectClass.toJtype(
                    classpath, 0),
                supers,
                humanName = this.simpleName
            )
        }
        if (idOfName.containsKey(this.simpleName)) {
            //            when (th)
            return
        }


        val id = mkId(this.simpleName)
        //            if (table.containsKey(id)) {
        //                println("Current value: ${table[id]} with name = ${}")
        //                println("New value: ${decl}")
        //                assert(!table.containsKey(id)) { String.format("Duplicate ID generated: $id") }
        //            }
        table[id] = decl
        assert(idOfName[this.simpleName] == id)
        table.containsKey(id)


    }

    fun JcClassType.toJtype(classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeParams = typeArguments.mapIndexed { index, param ->
            param.toJvmTypeArgument(index, classpath, depth + 1)
        }.toLogicList()

        val id = jcClass.mkId(this.typeName).toLogic()
        return if (jcClass.isInterface) Interface(id, typeParams, this.typeName) else Class_(
            id,
            typeParams,
            this.typeName
        )
    }

    private fun JcType.toJtype(index: Int, classpath: JcClasspath,
                               depth: Int): Jtype<LogicInt> = when (this) {
        is JcRefType -> toJtype(index, classpath, depth + 1)
        is JcPrimitiveType -> typeName.toPrimitiveType()
        else -> error("Unknown JcType $this")
    }

    private fun JcRefType.toJtype(index: Int, classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        if (depth > 50) {
            TODO("Too deep recursive type")
        }
        return when (this) {
            is JcArrayType -> Array_(elementType.toJtype(index, classpath, depth + 1))
            is JcClassType -> toJtype(classpath, depth + 1)
            is JcTypeVariable -> toJtype(index, classpath, depth + 1)
            is JcBoundedWildcard -> error("Unexpected $this")
            is JcUnboundWildcard -> error("Unexpected $this")
            else -> error("Unknown ref type $this")
        }
    }

    private fun JcRefType.toJvmTypeArgument(index: Int, classpath: JcClasspath,
                                            depth: Int): Jarg<Jtype<LogicInt>> =
        when (this) {
            is JcArrayType -> Array_(
                elementType.toJtype(index, classpath, depth + 1)).toJvmTypeArgument()

            is JcClassType -> toJtype(classpath, depth + 1).toJvmTypeArgument()
            is JcTypeVariable -> toJtype(index, classpath, depth + 1).toJvmTypeArgument()
            is JcBoundedWildcard -> toJvmTypeArgument(index, classpath, depth + 1)
            is JcUnboundWildcard -> Wildcard(None.noneLogic())
            else -> error("Unknown ref type $this")
        }

    private fun JcBoundedWildcard.toJvmTypeArgument(
        index: Int,
        classpath: JcClasspath,
        depth: Int
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
            typeBounds.isEmpty() -> classpath.objectClass.toJtype(classpath, depth + 1)
            typeBounds.size == 1 -> typeBounds.single().toJtype(depth + 1, classpath, index)
            else -> Intersect(
                typeBounds.map { it.toJtype(depth + 1, classpath, index) }.toLogicList())
        }

        return Var(symbol.hashCode().toLogic(), index.toPeanoLogicNumber(), upperBound,
            None.noneLogic())
    }

    fun JcTypeVariableDeclaration.toJtype(index: Int, classpath: JcClasspath,
                                          depth: Int): Jtype<LogicInt> {
        val typeBounds = bounds

        val upperBound = when {
            typeBounds.isEmpty() -> classpath.objectClass.toJtype(classpath, depth + 1)
            typeBounds.size == 1 -> typeBounds.single().toJtype(depth + 1, classpath, index)
            else -> Intersect(
                typeBounds.map { it.toJtype(depth + 1, classpath, index) }.toLogicList())
        }

        return Var(symbol.hashCode().toLogic(), index.toPeanoLogicNumber(), upperBound,
            None.noneLogic())
    }

    fun JcClassOrInterface.toJtype(classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeParams = toType().typeArguments.mapIndexed { index, param ->
            param.toJvmTypeArgument(index, classpath, depth + 1)
        }.toLogicList()

        return when (this.simpleName) {
            "java.lang.Object" -> Class_(0.toLogic(), typeParams, this.simpleName)
            "java.lang.Cloneable" -> Interface(1.toLogic(), typeParams, this.simpleName)
            "java.io.Serializable" -> Interface(2.toLogic(), typeParams, this.simpleName)
            else -> {
                val id = mkId(this.simpleName).toLogic()
                if (isInterface) Interface(id, typeParams, this.simpleName) else
                    Class_(id, typeParams, this.simpleName)
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
        runCatching { it.toDeclaration(classpath) }
            .onFailure { error ->
                println("Class ${it.name} | $error")
            }
    }

    companion object {
        fun makeClassesTable(
            classes: List<JcClassOrInterface>,
            classpath: JcClasspath,
        ): ClassesTable {
            val table = ClassesTable(hashMapOf())
            table.toJvmDeclarationsSafe(classes, classpath)
            assert(table.table.containsKey(1)) { "No object with ID=1 generated" }
            assert(table.table.containsKey(2)) { "No object with ID=2 generated" }
            assert(table.table.containsKey(3)) { "No object with ID=3 generated" }
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
    extractClassesTable()
}
