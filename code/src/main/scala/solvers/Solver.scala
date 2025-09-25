package solvers

import theories.*

trait Solver[T]:
  def checkSat(f: Formula[T]): SatResult[Model]

opaque type Prop = Int

object Prop:
  def apply(i: Int): Prop = i
  
/**
  * Simple stupid SAT solver by checking all possible assignments.
  *
  * An assignment is a subset of variables that are considered to be true.
  */
object SimpleSAT extends Solver[Prop]:
  def checkSat(f: Formula[Prop]): SatResult[PropModel[Prop]] =
    f.frees.toSet.subsets
      // the entire sat solver:
      .find(f.evaluateUnder)
      // then convert to the right model type
      .map(_.toSeq.asModel)
      .asSatResult

// There is actually no unit propagation here;
// so calling it DPLL is a stretch;
// we don't even have clauses so unit propagation is a bit meaningless
object DPLL extends Solver[Prop]:
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
          chosen,
          nextLeft
        )

  def checkSat(f: Formula[Prop]): SatResult[PropModel[Prop]] = 
    val free = f.frees.toList
    dpll(f, Nil, free).map(_.asModel).asSatResult

object ClausalDPLL extends Solver[Prop]:
  private def reduce[T](cc: CNF[T], a: Atomic[T], polarity: Boolean): CNF[T] =
    // set a to true
    // = set neg a to false
    // = remove all clauses containing a
    // /\ remove neg a from every clause
    // (flip if !polarity)
    val pred = 
      if polarity then
        (c: Clause[T]) => c.pos.contains(a)
      else
        (c: Clause[T]) => c.neg.contains(a)
    val reduct = 
      if polarity then
        (c: Clause[T]) => c -- a
      else
        (c: Clause[T]) => c -+ a
    val newClauses = cc.clauses.filterNot(pred).map(reduct)

    CNF(newClauses)
  
  private def unitPropagate[T](
      cc: CNF[T],
      chosen: List[Literal[T]],
      left: List[Atomic[T]]
  ): (CNF[T], List[Literal[T]], List[Atomic[T]]) =
    val unitClause = cc.clauses.find(c => c.size == 1)

    unitClause match
      case None => (cc, chosen, left) // no more unit clauses
      case Some(c) => 
          // is this unit literal positive or negative?
          val (a, polarity) = 
            if c.pos.nonEmpty then (c.pos.head, true)
            else (c.neg.head, false)

          // remove it from left
          val newLeft = left.filterNot(_ == a)
          
          // add it to chosen if needed
          val newChosen = 
            if polarity then Pos(a) :: chosen
            else Neg(a) :: chosen

          // reduce the clauses
          val newClauses = reduce(cc, a, polarity)

          unitPropagate(newClauses, newChosen, newLeft)

  private def dpll[T](
      cc: CNF[T],
      chosen: List[Literal[T]],
      left: List[Atomic[T]]
  ): Option[List[Atomic[T]]] =
    unitPropagate(cc, chosen, left) match
      case (cc, chosen, left) =>
        if cc.clauses.isEmpty then 
          // return model; which is the set of true literals
          Some(chosen.collect({case Pos(a) => a}))
        else if cc.clauses.exists(_.isEmpty) then None
        else if left.isEmpty then None
        else // choose next
          val nextLeft = left.tail

          lazy val posBranch = dpll(
            reduce(cc, left.head, true),
            Pos(left.head) :: chosen,
            nextLeft
          )
          lazy val negBranch = dpll(
            reduce(cc, left.head, false),
            chosen,
            nextLeft
          )

          posBranch.orElse(negBranch)

  def checkSat(f: Formula[Prop]): SatResult[PropModel[Prop]] = 
    val cnf = f.toCNF
    val free = cnf.frees.toList
    dpll(cnf, Nil, free).map(_.asModel).asSatResult

trait TheorySolver[T](using val th: Theory[T]) extends Solver[T]:
  def checkSat(f: th.Formula): th.SatResult

case class ClausalDPLL[T: Theory]() extends TheorySolver[T]:

  import ClausalDPLL.{reduce, unitPropagate}

  private def dpll(
      cc: CNF[th.Atom],
      chosen: List[th.Literal],
      left: List[th.Atomic]
  ): th.SatResult =
    unitPropagate(cc, chosen, left) match
      case (cc, chosen, left) =>
        if cc.clauses.isEmpty then 
          // check if these atoms are satisfiable
          th.checkSat(chosen.withoutVars)
        else if cc.clauses.exists(_.isEmpty) then Unsat
        else if left.isEmpty then Unsat
        else // choose next
          val nextLeft = left.tail
          
          lazy val posBranch = dpll(
            reduce(cc, left.head, true),
            Pos(left.head) :: chosen,
            nextLeft
          )
          lazy val negBranch = dpll(
            reduce(cc, left.head, false),
            Neg(left.head) :: chosen,
            nextLeft
          )

          posBranch.orElse(negBranch)

  def checkSat(f: th.Formula): th.SatResult = 
    if !th.wellformed(f) then Unknown
    else
      val cnf = th.preprocess(f).toCNF
      val free = cnf.frees.toList
      dpll(cnf, Nil, free)

given Theory[Prop] with
  type Atom = Prop
  type Model = PropModel[Prop]

  def checkSat(fs: Seq[Literal]): SatResult = 
    Sat(PropModel(fs.collect {case Pos(Atom(a)) => a}))

  def preprocess(f: Formula): Formula = f

  def wellformed(f: Formula): Boolean = true
