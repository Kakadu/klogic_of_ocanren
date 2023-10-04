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

    testImplementation("com.github.UnitTestBot.klogic:klogic-core:0.2.1") // core
    testImplementation("com.github.UnitTestBot.klogic:klogic-utils:0.2.1") // util terms
    // Pin klogic commit with wildcards
//    testImplementation(
//            "com.github.UnitTestBot.klogic:klogic-core:65882576927ce590f6d927b40f3a4c06060d7c9b") // core
//    testImplementation(
//            "com.github.UnitTestBot.klogic:klogic-utils:65882576927ce590f6d927b40f3a4c06060d7c9b") // util terms
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
