package org.jgs.classtable

import kotlinx.coroutines.runBlocking
import org.jacodb.api.*
import org.jacodb.api.ext.objectClass
import org.jacodb.impl.features.InMemoryHierarchy
import org.jacodb.impl.features.classpaths.UnknownClasses
import org.jacodb.impl.features.hierarchyExt
import org.jacodb.impl.jacodb
import java.io.Closeable
import java.io.File

class ClassesExtractorTask : JcClassProcessingTask {
    private val _classes: MutableList<JcClassOrInterface> = mutableListOf()

    val classes: List<JcClassOrInterface> = _classes

    override fun process(clazz: JcClassOrInterface) {
        _classes += clazz
    }
}

data class ClassesDatabase(
    val classes: List<JcClassOrInterface>,
    val classpath: JcClasspath,
    val db: JcDatabase,
) : Closeable {
    override fun close() {
        classpath.close()
        db.close()
    }
}

@Suppress("UNUSED_PARAMETER")
private suspend fun extractClassesTableAsync(
    classPath: List<File>,
    vararg features: JcFeature<*, *>
): ClassesDatabase {
    val db = jacodb {
        useProcessJavaRuntime()
        installFeatures(InMemoryHierarchy)
        installFeatures(*features)
    }

    db.awaitBackgroundJobs();

    val classpath = runBlocking { db.classpath(emptyList()) }
    val classes = runBlocking {
        classpath.hierarchyExt().findSubClasses(classpath.objectClass, allHierarchy = true, includeOwn = true)
    }

    return ClassesDatabase(classes.toList(), classpath, db)
}

internal fun extractClassesTableTask(
    classPath: List<File>,
    vararg features: JcFeature<*, *>
): ClassesDatabase = runBlocking {
    extractClassesTableAsync(classPath, *features)
}
