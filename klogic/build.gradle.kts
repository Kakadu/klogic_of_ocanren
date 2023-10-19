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

//    testImplementation("com.github.UnitTestBot.klogic:klogic-core:0.2.1") // core
//    testImplementation("com.github.UnitTestBot.klogic:klogic-utils:0.2.1") // util terms
//     Pin klogic commit with wildcards
    testImplementation(
            "com.github.UnitTestBot.klogic:klogic-core:df988d091aa17312f9a488ed0705ab0c87d89d28") // core
    testImplementation(
            "com.github.UnitTestBot.klogic:klogic-utils:df988d091aa17312f9a488ed0705ab0c87d89d28") // util terms

    implementation("org.jacodb:jacodb-core:1.3.1")
    implementation("org.jacodb:jacodb-analysis:1.3.1")

    implementation("org.jgrapht:jgrapht-core:1.5.2")
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

    minHeapSize = "512m"
    maxHeapSize = "2048m"
}
