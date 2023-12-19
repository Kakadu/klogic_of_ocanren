package org.jgs.classtable
import org.jacodb.api.JcClassOrInterface
import org.jacodb.api.JcTypeVariableDeclaration

interface TypeSolver {
    // To support ouput sequence we need some help from Klogic
    //fun getSuitableTypes(type: JcTypeVariableDeclaration): Sequence<JcClassOrInterface>
    fun getSuitableTypes(type: JcTypeVariableDeclaration, printTime: Boolean = false): JcClassOrInterface?
    fun getRandomSubclassOf(superClasses: List<JcClassOrInterface>, printTime: Boolean = false): JcClassOrInterface?
}
