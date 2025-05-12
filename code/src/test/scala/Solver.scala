
import theories.*
import solvers.{*, given}

class SolverTest extends munit.FunSuite {
  val solvers: List[(String, Solver[Prop])] = List(
    "SimpleSAT" -> SimpleSAT,
    "DPLL" -> DPLL,
    "ClausalDPLL" -> ClausalDPLL,
    // "CDCL" -> CDCL,
  )

  val theorySolvers: List[(String, TheorySolver[Prop])] = List(
    "ClausalDPLL(T)" -> ClausalDPLL[Prop]()
  )

  val trueTest = (name: String, solver: Solver[Prop]) => 
    test(s"$name: True is SAT") {
      val f = True
      val result = solver.checkSat(f)
      assert(result.isSat)
    }

  val falseTest = (name: String, solver: Solver[Prop]) =>
    test(s"$name: False is UNSAT") {
      val f = False
      val result = solver.checkSat(f)
      assert(!result.isSat)
    }

  val trivialSATFormulas = List(
    Var.next,
    Var.next \/ Var.next,
    Var.next /\ Var.next,
    !Var.next,
    Var.next -> Var.next,
    Var.next <-> Var.next,
    Var.next <-> (Var.next /\ Var.next),
  )

  val trivialSATTest = (name: String, solver: Solver[Prop]) =>
    test(s"$name: Trivial SAT formulas") {
      for (f <- trivialSATFormulas) {
        val result = solver.checkSat(f)
        assert(result.isSat)
      }
    }

  // run tests
  val tests = List(
    trueTest,
    falseTest,
    trivialSATTest
  )

  for ((name, solver) <- solvers) {
    tests.foreach(test => test(name, solver))
  }
}

