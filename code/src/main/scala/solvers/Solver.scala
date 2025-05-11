package solvers

import theories.*

trait Solver[-T]:
  def checkSat[S <: T](f: Formula[S]): Option[Model[S]]

opaque type Prop = Int

object Prop:
  def apply(i: Int): Prop = i

object SimpleSAT extends Solver[Prop]:
  def checkSat[S <: Prop](f: Formula[S]): Option[Model[S]] =
    f.frees.toSet.subsets
      .find(f.evaluateUnder)
      .map(_.asModel)

object DPLL extends Solver[Any]:
  private def reduce[T](f: Formula[T], a: Atomic[T], polarity: Boolean): Formula[T] =
    f match
      case True                    => True
      case False                   => False
      case at @ Var(_) if at == a  => polarity.asFormula
      case at @ Atom(_) if at == a => polarity.asFormula
      case Not(b)                  => Not(reduce(b, a, polarity))
      case And(b1, b2) => And(reduce(b1, a, polarity), reduce(b2, a, polarity))
      case Or(b1, b2)  => Or(reduce(b1, a, polarity), reduce(b2, a, polarity))
      case Implies(b1, b2) =>
        Implies(reduce(b1, a, polarity), reduce(b2, a, polarity))
      case Iff(b1, b2) => Iff(reduce(b1, a, polarity), reduce(b2, a, polarity))
      case _           => f

  private def dpll[T](
      f: Formula[T],
      chosen: List[Atomic[T]],
      left: List[Atomic[T]]
  ): Option[List[Atomic[T]]] =
    if f.evaluateUnder(Set.empty) then Some(chosen)
    else if left.isEmpty then None
    else // choose next
      val nextChosen = left.head :: chosen
      val nextLeft = left.tail
      // pos
      val leftBranch = dpll(
        reduce(f, left.head, true),
        nextChosen,
        nextLeft
      )
      if leftBranch.isDefined then leftBranch
      else // neg
        dpll(
          reduce(f, left.head, false),
          nextChosen,
          nextLeft
        )

  def checkSat[T](f: Formula[T]): Option[Model[T]] = 
    val free = f.frees.toList
    dpll(f, Nil, free).map(_.toSet.asModel)

object ClausalDPLL extends Solver[Any]:
  private def reduce[T](cc: CNF[T], a: Atomic[T], polarity: Boolean): CNF[T] =
    // set a to true
    // = set neg a to false
    // = remove all clauses containing a
    // /\ remove neg a from every clause
    // (flip if !polarity)
    val pred = (c: Clause[T]) => if polarity then c.pos.contains(a) else c.neg.contains(a)
    val reduct = (c : Clause[T]) => if polarity then c -- a else c -+ a
    val newClauses = cc.clauses.filterNot(pred).map(reduct)

    CNF(newClauses)

  private def dpll[T](
      cc: CNF[T],
      chosen: List[Atomic[T]],
      left: List[Atomic[T]]
  ): Option[List[Atomic[T]]] =
    if cc.clauses.isEmpty then Some(chosen)
    else if cc.clauses.exists(_.isEmpty) then None
    else if left.isEmpty then None
    else // choose next
      val nextChosen = left.head :: chosen
      val nextLeft = left.tail
      // pos
      val leftBranch = dpll(
        reduce(cc, left.head, true),
        nextChosen,
        nextLeft
      )
      if leftBranch.isDefined then leftBranch
      else // neg
        dpll(
          reduce(cc, left.head, false),
          nextChosen,
          nextLeft
        )

  def checkSat[T](f: Formula[T]): Option[Model[T]] = 
    val cnf = f.toCNF
    val free = cnf.frees.toList
    dpll(cnf, Nil, free).map(_.toSet.asModel)
