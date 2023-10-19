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
import org.klogic.utils.terms.logicTo
import org.klogic.utils.terms.toLogicList
import org.klogic.utils.terms.toPeanoLogicNumber
import utils.JGS.Array_
import utils.JGS.C
import utils.JGS.Class_
import utils.JGS.Decl
import utils.JGS.Extends
import utils.JGS.I
import utils.JGS.Intersect
import utils.JGS.Jarg
import utils.JGS.Jtype
import utils.JGS.PrimitiveType.PrimitiveBoolean
import utils.JGS.PrimitiveType.PrimitiveByte
import utils.JGS.PrimitiveType.PrimitiveChar
import utils.JGS.PrimitiveType.PrimitiveDouble
import utils.JGS.PrimitiveType.PrimitiveFloat
import utils.JGS.PrimitiveType.PrimitiveInt
import utils.JGS.PrimitiveType.PrimitiveLong
import utils.JGS.PrimitiveType.PrimitiveShort
import utils.JGS.PrimitiveType.PrimitiveVoid
import utils.JGS.Super
import utils.JGS.Type
import utils.JGS.TypeInterface
import utils.JGS.Var
import utils.JGS.Wildcard
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.None
import utils.toOption
import java.io.File

val EmptyClassTable = ClassesTable(classNames = (mutableMapOf<JcClassOrInterface, Int>()), table = mutableMapOf<Int, Decl<LogicInt>>())

data class ClassesTable(
        val classNames: MutableMap<JcClassOrInterface, Int>,
        val table: MutableMap<Int, Decl<LogicInt>>
) {
    private var lastID = 10
    private fun JcClassOrInterface.mkId(name: String): Int {
        return when (name) {
            "java.lang.Object" -> 1
            "java.lang.Cloneable" -> 2
            "java.io.Serializable" -> 3
            else -> {
                lastID++;
                lastID
            }
        }
    }

    private fun Jtype<LogicInt>.toJvmTypeArgument(): Jarg<Jtype<LogicInt>> = Type(this)

    fun JcClassOrInterface.toDeclaration(classpath: JcClasspath) {
        val type = toType()
        val typeParams =
                type.typeParameters.mapIndexed { index, param -> param.toJtype(index, classpath, depth = 0) }.toLogicList()
        val supers = type.interfaces.map { it.toJtype(classpath, depth = 0) }.toLogicList()

        val decl = when {
            isInterface -> I(typeParams, supers)
            else -> C(
                    typeParams,
                    type.superType?.toJtype(classpath, depth = 0) ?: classpath.objectClass.toJtype(classpath, 0),
                    supers
            )
        }
        table[mkId(this.simpleName)] = decl
    }

    fun JcClassType.toJtype(classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeParams = typeArguments.mapIndexed { index, param ->
            param.toJvmTypeArgument(index, classpath, depth + 1)
        }.toLogicList()

        val id = jcClass.mkId(this.typeName).toLogic()
        return if (jcClass.isInterface) TypeInterface(id, typeParams, this.typeName) else Class_(id, typeParams, this.typeName)
    }

    private fun JcType.toJtype(index: Int, classpath: JcClasspath, depth: Int): Jtype<LogicInt> = when (this) {
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

    private fun JcRefType.toJvmTypeArgument(index: Int, classpath: JcClasspath, depth: Int): Jarg<Jtype<LogicInt>> =
            when (this) {
                is JcArrayType -> Array_(elementType.toJtype(index, classpath, depth + 1)).toJvmTypeArgument()
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

            val polarityJtypeLogicPair = Super logicTo lowerBounds.single().toJtype(index, classpath, depth + 1)
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
            else -> Intersect(typeBounds.map { it.toJtype(depth + 1, classpath, index) }.toLogicList())
        }

        return Var(symbol.hashCode().toLogic(), index.toPeanoLogicNumber(), upperBound, None.noneLogic())
    }

    fun JcTypeVariableDeclaration.toJtype(index: Int, classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeBounds = bounds

        val upperBound = when {
            typeBounds.isEmpty() -> classpath.objectClass.toJtype(classpath, depth + 1)
            typeBounds.size == 1 -> typeBounds.single().toJtype(depth + 1, classpath, index)
            else -> Intersect(typeBounds.map { it.toJtype(depth + 1, classpath, index) }.toLogicList())
        }

        return Var(symbol.hashCode().toLogic(), index.toPeanoLogicNumber(), upperBound, None.noneLogic())
    }

    fun JcClassOrInterface.toJtype(classpath: JcClasspath, depth: Int): Jtype<LogicInt> {
        val typeParams = toType().typeArguments.mapIndexed { index, param ->
            param.toJvmTypeArgument(index, classpath, depth + 1)
        }.toLogicList()

        return when (this.simpleName) {
            "java.lang.Object" -> Class_(0.toLogic(), typeParams, this.simpleName)
            "java.lang.Cloneable" -> TypeInterface(1.toLogic(), typeParams, this.simpleName)
            "java.io.Serializable" -> TypeInterface(2.toLogic(), typeParams, this.simpleName)
            else -> {
                val id = mkId(this.simpleName).toLogic()
                if (isInterface) TypeInterface(id, typeParams, this.simpleName) else
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
            val table = ClassesTable(hashMapOf(), hashMapOf())
            table.toJvmDeclarationsSafe(classes, classpath)
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
