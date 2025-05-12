
import theories.*
import solvers.{*, given}

class SolverTest extends munit.FunSuite {
  val solvers: List[(String, Solver[Prop])] = List(
    "SimpleSAT" -> SimpleSAT,
    "DPLL" -> DPLL,
    "ClausalDPLL" -> ClausalDPLL,
    "ClausalDPLL(T)" -> ClausalDPLL[Prop](),
    // "CDCL" -> CDCL,
  )

  val a = Var.next
  val b = Var.next
  val c = Var.next

  val trueTest = (name: String, solver: Solver[Prop]) => 
    test(s"$name: True is SAT") {
      val f = True
      val result = solver.checkSat(f)
      assert(result.isSat, s"$name: $f should be SAT")
    }

  val falseTest = (name: String, solver: Solver[Prop]) =>
    test(s"$name: False is UNSAT") {
      val f = False
      val result = solver.checkSat(f)
      assert(!result.isSat, s"$name: $f should be UNSAT")
    }

  val trivialSATFormulas = List(
    a,
    a \/ a,
    a /\ b,
    !a,
    b -> a,
    a <-> b,
    a <-> (b /\ a),
  )

  val trivialUNSATFormulas = List(
    a /\ !a,
    a <-> !a,
  )

  val trivialSATTest = (name: String, solver: Solver[Prop]) =>
    test(s"$name: Trivial SAT formulas") {
      for (f <- trivialSATFormulas) {
        val result = solver.checkSat(f)
        assert(result.isSat, s"$name: $f should be SAT")
      }
    }

  val trivialUNSATTest = (name: String, solver: Solver[Prop]) =>
    test(s"$name: Trivial UNSAT formulas") {
      for (f <- trivialUNSATFormulas) {
        val result = solver.checkSat(f)
        assert(!result.isSat, s"$name: $f should be UNSAT")
      }
    }

  // run tests
  val tests = List(
    trueTest,
    falseTest,
    trivialSATTest,
    trivialUNSATTest,
  )

  for ((name, solver) <- solvers) {
    tests.foreach(test => test(name, solver))
  }
}

