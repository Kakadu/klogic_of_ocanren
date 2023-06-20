import com.github.jengelman.gradle.plugins.shadow.tasks.ShadowJar

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
    testImplementation("com.github.UnitTestBot.klogic:klogic-core:0.1.5")
    // util terms
    testImplementation("com.github.UnitTestBot.klogic:klogic-utils:0.1.5")
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
        outputs.upToDateWhen {false}
        showStandardStreams = true
    }
}