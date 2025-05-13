val scala3Version = "3.7.0"

lazy val root = project
  .in(file("."))
  .settings(
    name := "smtlia",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    libraryDependencies += "org.scalameta" %% "munit" % "1.0.0" % Test,
    libraryDependencies += "com.github.vagmcs" %% "optimus" % "3.4.5",
    libraryDependencies += "com.github.vagmcs" %% "optimus-solver-oj" % "3.4.5",
    libraryDependencies += "com.github.vagmcs" %% "optimus-solver-lp" % "3.4.5"
  )
