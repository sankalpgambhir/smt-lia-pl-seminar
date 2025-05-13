package theories

sealed trait Atomic[+T]

sealed trait Formula[+T]:
  override def toString: String = this match
    case True            => "true"
    case False           => "false"
    case Var(id)         => s"v$id"
    case Atom(a)         => a.toString
    case Not(b)          => s"!(${b.toString})"
    case And(b1, b2)     => s"(${b1.toString} /\\ ${b2.toString})"
    case Or(b1, b2)      => s"(${b1.toString} \\/ ${b2.toString})"
    case Implies(b1, b2) => s"(${b1.toString} -> ${b2.toString})"
    case Iff(b1, b2)     => s"(${b1.toString} <-> ${b2.toString})"

  infix def `/\\`[S >: T](b2: Formula[S]): Formula[S] = And(this, b2)
  infix def `\\/`[S >: T](b2: Formula[S]): Formula[S] = Or(this, b2)
  infix def `->`[S >: T](b2: Formula[S]): Formula[S] = Implies(this, b2)
  infix def `<->`[S >: T](b2: Formula[S]): Formula[S] = Iff(this, b2)
  def unary_! : Formula[T] = Not(this)

  def frees: Seq[Atomic[T]] = this match
    case True            => Seq()
    case False           => Seq()
    case v @ Var(_)      => Seq(v)
    case a @ Atom(_)     => Seq(a)
    case Not(b)          => b.frees
    case And(b1, b2)     => b1.frees ++ b2.frees
    case Or(b1, b2)      => b1.frees ++ b2.frees
    case Implies(b1, b2) => b1.frees ++ b2.frees
    case Iff(b1, b2)     => b1.frees ++ b2.frees

  def map[S >: T](f: Formula[S] => Formula[S]): Formula[S] = this match
    case Not(b)          => f(Not(b.map(f)))
    case And(b1, b2)     => f(And(b1.map(f), b2.map(f)))
    case Or(b1, b2)      => f(Or(b1.map(f), b2.map(f)))
    case Implies(b1, b2) => f(Implies(b1.map(f), b2.map(f)))
    case Iff(b1, b2)     => f(Iff(b1.map(f), b2.map(f)))
    case _ => f(this)

  def substitute[S >: T](m: Map[Formula[S], Formula[S]]): Formula[S] =
    map(ff => m.getOrElse(ff, ff))

case object True extends Formula[Nothing]
case object False extends Formula[Nothing]
case class Var private (id: Int) extends Formula[Nothing] with Atomic[Nothing]
case class Atom[T](atom: T) extends Formula[T] with Atomic[T]
case class Not[T](b: Formula[T]) extends Formula[T]
case class And[T](b1: Formula[T], b2: Formula[T]) extends Formula[T]
case class Or[T](b1: Formula[T], b2: Formula[T]) extends Formula[T]
case class Implies[T](b1: Formula[T], b2: Formula[T]) extends Formula[T]
case class Iff[T](b1: Formula[T], b2: Formula[T]) extends Formula[T]

object Var:
  private var counter = 0
  def next: Var =
    counter += 1
    Var(counter)

extension (b: Boolean)
  def asFormula: Formula[Nothing] = if b then True else False

case class Clause[T](pos: Set[Atomic[T]], neg: Set[Atomic[T]]):
  def isEmpty: Boolean =
    pos.isEmpty && neg.isEmpty

  /** Remove the atomic `a` (as a positive literal) from the clause.
    */
  infix def `-+`(a: Atomic[T]): Clause[T] =
    this.copy(pos = pos - a)

  /** Remove the atomic `a` (as a negative literal `!a`) from the clause.
    */
  infix def `--`(a: Atomic[T]): Clause[T] =
    this.copy(neg = neg - a)

  /** Add the atomic `a` (as a positive literal) to the clause.
    */
  infix def `++`(a: Atomic[T]): Clause[T] =
    this.copy(pos = pos + a)

  /** Add the atomic `a` (as a negative literal `!a`) to the clause.
    */
  infix def `+-`(a: Atomic[T]): Clause[T] =
    this.copy(neg = neg + a)

case class CNF[T](clauses: Seq[Clause[T]]):
  def frees: Set[Atomic[T]] =
    clauses.toSet.flatMap(c => c.pos ++ c.neg)

private def tseitin[T](f: Formula[T]): CNF[T] =
  // construct the set of clauses representing (f <-> label)
  def tseitinRec(f: Formula[T], label: Var): Seq[Clause[T]] = f match
    case True       => Seq(Clause(Set(label), Set())) // (label)
    case False      => Seq(Clause(Set(), Set(label))) // (!label)
    case v @ Var(_) =>
      // (label <-> v)
      Seq(
        Clause(Set(v), Set(label)), // (label -> v) = (!label \/ v)
        Clause(Set(label), Set(v)) // (v -> label) = (!v \/ label)
      )
    case a @ Atom(_) =>
      // (label <-> a)
      Seq(
        Clause(Set(a), Set(label)), // (label -> a) = (!label \/ a)
        Clause(Set(label), Set(a)) // (a -> label) = (!a \/ label)
      )
    case Not(b) =>
      val inner = Var.next
      tseitinRec(b, inner) // (b <-> inner)
      // (label <-> !inner)
        :+ Clause(
          Set(),
          Set(inner, label)
        ) // (label -> !inner) = (!inner \/ !label)
        :+ Clause(
          Set(inner, label),
          Set()
        ) // (!inner -> label) = (inner \/ label)
    case And(b1, b2) =>
      val i1 = Var.next
      val i2 = Var.next
      tseitinRec(b1, i1) ++ tseitinRec(b2, i2)
      // (label <-> (i1 /\ i2))
        :+ Clause(
          Set(label),
          Set(i1, i2)
        ) // ((i1 /\ i2) -> label) = (!i1 \/ !i2 \/ label)
        :+ Clause(Set(i1), Set(label)) // (label -> i1) = (!label \/ i1)
        :+ Clause(Set(i2), Set(label)) // (label -> i2) = (!label \/ i2)
    case Or(b1, b2) =>
      val i1 = Var.next
      val i2 = Var.next
      tseitinRec(b1, i1) ++ tseitinRec(b2, i2)
      // (label <-> (i1 \/ i2))
        :+ Clause(
          Set(i1, i2),
          Set(label)
        ) // (label -> (i1 \/ i2)) = (!label \/ i1 \/ i2)
        :+ Clause(Set(label), Set(i1)) // (i1 -> label) = (!i1 \/ label)
        :+ Clause(Set(label), Set(i2)) // (i2 -> label) = (!i2 \/ label)
    case Implies(b1, b2) =>
      // just desugar
      // (b1 -> b2) = (!b1 \/ b2)
      tseitinRec(Or(Not(b1), b2), label)
    case Iff(b1, b2) =>
      // just desugar
      // (b1 <-> b2) = (!b1 \/ b2) /\ (!b2 \/ b1)
      tseitinRec(And(Or(Not(b1), b2), Or(b1, Not(b2))), label)

  val topLabel = Var.next
  val topClause = Clause[T](Set(topLabel), Set()) // (topLabel)
  val clauses = tseitinRec(f, topLabel) :+ topClause

  CNF(clauses)
extension [T](f: Formula[T])
  /** Formula in CNF form equisatisfiable to the original formula.
    */
  def toCNF: CNF[T] = tseitin(f)

  def evaluateUnder(assignments: Set[Atomic[T]]): Boolean = f match
    case True        => true
    case False       => false
    case v @ Var(_)  => assignments(v)
    case a @ Atom(_) => assignments(a)
    case Not(b)      => !b.evaluateUnder(assignments)
    case And(b1, b2) =>
      b1.evaluateUnder(assignments) && b2.evaluateUnder(assignments)
    case Or(b1, b2) =>
      b1.evaluateUnder(assignments) || b2.evaluateUnder(assignments)
    case Implies(b1, b2) =>
      !b1.evaluateUnder(assignments) || b2.evaluateUnder(assignments)
    case Iff(b1, b2) =>
      b1.evaluateUnder(assignments) == b2.evaluateUnder(assignments)

case class PropModel[+T](assignments: Seq[T]) extends Model:
  private val _assignments: Set[Any] = assignments.toSet
  def evaluate[S >: T](a: S): Boolean = _assignments(a)
  inline def apply[S >: T](a: S): Boolean = evaluate(a)
  def atoms: Seq[T] = _assignments.toSeq.asInstanceOf

  def prettyModel: String =
    assignments
      .map(a => s"$a = ${_assignments(a)}")
      .mkString("{", ", ", "}")    

extension [T](assignments: Seq[Atomic[T]])
  def asModel: PropModel[T] =
    PropModel(
      assignments.collect:
        case Atom(a) => a
    )

sealed trait Literal[T]:
  def unary_! : Literal[T] = this match
    case Pos(a) => Neg(a)
    case Neg(a) => Pos(a)
  def atom: Atomic[T] = this match
    case Pos(a) => a
    case Neg(a) => a
case class Pos[T](a: Atomic[T]) extends Literal[T]
case class Neg[T](a: Atomic[T]) extends Literal[T]
  

extension [T] (ls : Seq[Literal[T]])
  def withoutVars: Seq[Literal[T]] =
      ls.collect:
        case a @ Pos(Atom(_)) => a
        case a @ Neg(Atom(_)) => a