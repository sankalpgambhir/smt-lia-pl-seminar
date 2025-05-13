
import theories.*
import solvers.{*, given}

class TestTest extends munit.FunSuite {
  test("cdcl false"):
    val a = Atom(Prop(1))
    val f = a /\ !a
    val result = CDCL[Prop]().checkSat(f)
    assert(!result.isSat, s"$f should be UNSAT")
}

class SolverTest extends munit.FunSuite {
  val solvers: List[(String, Solver[Prop])] = List(
    "SimpleSAT" -> SimpleSAT,
    "DPLL" -> DPLL,
    "ClausalDPLL" -> ClausalDPLL,
    "ClausalDPLL(T)" -> ClausalDPLL[Prop](),
    "CDCL" -> CDCL[Prop](),
  )

  val a = Atom(Prop(1))
  val b = Atom(Prop(2))
  val c = Atom(Prop(3))

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
        assert(result.isSat, s"$name: $f should be SAT, got $result")
      }
    }

  val trivialUNSATTest = (name: String, solver: Solver[Prop]) =>
    test(s"$name: Trivial UNSAT formulas") {
      for (f <- trivialUNSATFormulas) {
        val result = solver.checkSat(f)
        assert(!result.isSat, s"$name: $f should be UNSAT, got $result")
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

