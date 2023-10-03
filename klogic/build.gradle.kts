import com.github.jengelman.gradle.plugins.shadow.tasks.ShadowJar
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("java")
    kotlin("jvm") version "1.8.21"
    id("com.github.johnrengelman.shadow") version "7.1.2"
}

repositories {
    mavenCentral()
    maven {
        url = uri("https://jitpack.io")
    }
}

dependencies {
    testImplementation(platform("org.junit:junit-bom:5.9.1"))
    testImplementation("org.junit.jupiter:junit-jupiter")
    // core
//    testImplementation("com.github.UnitTestBot.klogic:klogic-core:0.1.5")
    // util terms
//    testImplementation("com.github.UnitTestBot.klogic:klogic-utils:0.1.5")
    // Pin klogic commit with wildcards
    testImplementation(
            "com.github.UnitTestBot.klogic:klogic-core:e17613a29a5932661b81a915b2de64d2f7bf43e6") // core
    testImplementation(
            "com.github.UnitTestBot.klogic:klogic-utils:e17613a29a5932661b81a915b2de64d2f7bf43e6") // util terms
}

tasks.withType<KotlinCompile> {
    kotlinOptions {
        freeCompilerArgs += listOf("-Xcontext-receivers")
        //allWarningsAsErrors = true
    }
}

tasks.withType<ShadowJar> {
    minimize()
    // Replace the original jar with this executable jar
    archiveClassifier.set("")

    from(sourceSets.test.get().output)
    configurations = listOf(project.configurations.testRuntimeClasspath.get())
    manifest {
        attributes["Main-Class"] = "TestRunnerKt"
    }
}

tasks.test {
    useJUnitPlatform()
    testLogging {
        outputs.upToDateWhen { false }
        showStandardStreams = true
    }
}
