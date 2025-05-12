
import theories.*

class Propositional extends munit.FunSuite:
  val a = Var.next
  val b = Var.next
  val c = Var.next

  type Prop = Formula[Int]

  val testFormulas = List(
    True,
    False,
    a,
    b,
    c,
    a /\ b,
    a \/ b,
    !a,
    a -> b,
    a <-> (b /\ c)
  )

  val testModels = Set(a, b, c).subsets()

  test("Printing") {

    val f1 = a /\ b
    val f2 = a \/ b
    val f3 = !a
    val f4 = a -> b
    val f5 = a <-> (b /\ c)

    assertEquals(f1.toString, "(v1 /\\ v2)")
    assertEquals(f2.toString, "(v1 \\/ v2)")
    assertEquals(f3.toString, "!(v1)")
    assertEquals(f4.toString, "(v1 -> v2)")
    assertEquals(f5.toString, "(v1 <-> (v2 /\\ v3))")
  }

  test("Trivial Evaluation") {
    assertEquals(True.evaluateUnder(Set.empty), true)
    assertEquals(False.evaluateUnder(Set.empty), false)
  }

  test("Evaluation") {
    assertEquals(a.evaluateUnder(Set(a)), true)
    assertEquals(a.evaluateUnder(Set(b)), false)
    assertEquals((a /\ b).evaluateUnder(Set(a, b)), true)
    assertEquals((a /\ b).evaluateUnder(Set(a)), false)
    assertEquals((a \/ b).evaluateUnder(Set(a, b)), true)
    assertEquals((a \/ b).evaluateUnder(Set(b)), true)
    assertEquals((a \/ b).evaluateUnder(Set.empty), false)
    assertEquals((!a).evaluateUnder(Set(a)), false)
    assertEquals((!a).evaluateUnder(Set(b)), true)
  }

end Propositional
