package solvers

import theories.*
import util.Extensions.*
import scala.collection.immutable.SortedSet

sealed trait Source
case object Problem extends Source
case object Decision extends Source
case class Combine(left: Source, right: Source) extends Source
case class Contradiction(inner: Source) extends Source

object CDCL:
  case object NoConflictingClauseException extends Exception

class CDCL[T: Theory]() extends TheorySolver[T]:
  import th.*

  type Implicants = SortedSet[Int]
  type Assignment = Map[Literal, (Implicants, Source)]

  case class Clause(literals: Set[Literal], source: Source):
    def isEmpty: Boolean = literals.isEmpty
    def isUnit: Boolean = literals.size == 1
    def contains(lit: Literal): Boolean = literals.contains(lit)
    def isValidated(model: Assignment): Boolean =
      literals.exists(l => model.contains(l))
    def isFalsified(model: Assignment): Boolean =
      literals.forall(l => model.contains(!l))
    def unitDecomposition(model: Assignment): Option[(Literal, (Implicants, Source))] =
      lazy val remainingLiterals = literals.filterNot(l => model.contains(!l))
      if isValidated(model) then
        // clause is satisfied, no need to decompose
        None
      else if remainingLiterals.size == 1 then
        val lit = remainingLiterals.head
        // implicants *not* minimized to UIP
        val implicants = (literals - lit)
                          .map(l => model(!l))
                          .foldLeft((SortedSet.empty[Int], this.source)) :
                            case ((imps, src), (nextImp, nextSource)) =>
                              (imps ++ nextImp, Combine(src, nextSource))
        Some((lit, implicants))
      else if remainingLiterals.isEmpty then
        // pick the last chosen literal
        val lastLit = literals.maxBy(l => model(!l)._1.maxOption)
        val implicants = (literals - lastLit).map(l => model(!l))
                          .foldLeft((SortedSet.empty[Int], this.source)) :
                            case ((imps, src), (nextImp, nextSource)) =>
                              (imps ++ nextImp, Combine(src, nextSource))
        Some((lastLit, implicants)) 
      else None
    def negationOf(other: Clause): Boolean =
      // check if this clause is the negation of another
      val negatedLiterals = literals.map(!_)
      other.literals == negatedLiterals
  
  @annotation.tailrec
  private def unitPropagateRec(
      leftClauses: List[Clause],
      openClauses: List[Clause],
      assignment: Assignment,
      decisionLevel: Int,
      recsize: Int = Int.MaxValue
  ): Assignment =
    leftClauses match
      case Nil          =>
        if openClauses.isEmpty || openClauses.size == recsize then
          // no more clauses to propagate
          // or we reached a fixed point
          assignment
        else
          // continue with the open clauses 
          unitPropagateRec(
            openClauses,
            List.empty,
            assignment,
            decisionLevel,
            openClauses.size
          )
      case head :: next => 
        // can we unit propagate off of head?
        head.unitDecomposition(assignment) match
          case None => 
            // leave head around in open clauses if it isn't already solved,
            // move on
            val nextOpen = if head.isValidated(assignment) || head.isFalsified(assignment) then
              openClauses
            else
              head :: openClauses
            unitPropagateRec(next, nextOpen, assignment, decisionLevel, recsize)
          case Some(kv) =>
            val newAssignment = assignment + kv
            // continue with the rest of the clauses
            unitPropagateRec(
              next,
              openClauses,
              newAssignment,
              decisionLevel,
              recsize
            )

  private def unitPropagate(
      clauses: Set[Clause],
      assignment: Assignment,
      decisionLevel: Int
  ): Assignment = 
    unitPropagateRec(
      clauses.toList,
      List.empty,
      assignment,
      decisionLevel
    )

  private def rollback(
      assignment: Assignment,
      to: Int
  ): Assignment = 
    assignment.filterNot{ case (_, (implicants, _)) => implicants.exists(_ > to) }

  /**
   * Analyze a set of assignments for self-consistency. If the set is inconsistent,
   * returns a list of conflict clauses and the decision level to backtrack to. 
   */
  private def analyzeConflict(
      frees: Set[Atomic],
      assignment: Assignment,
      decisions: Map[Int, Literal],
      currentDecisionLevel: Int
  ): Option[(Set[Clause], Int)] =
    // find conflicting atoms in the assignment
    val conflictingAtoms =
      frees.filter(atom => assignment.contains(Pos(atom)) && assignment.contains(Neg(atom)))
    if conflictingAtoms.isEmpty then
      // no conflict
      None
    else
      def backjumpOf(atom: Atomic): Int =
        // if we are backjumping, both must exist
        val posImp = assignment(Pos(atom))._1 - currentDecisionLevel
        val negImp = assignment(Neg(atom))._1 - currentDecisionLevel
        val posLevel = posImp.maxOption.getOrElse(Int.MinValue)
        val negLevel = negImp.maxOption.getOrElse(Int.MinValue)
        math.max(posLevel, negLevel)

      def conflictClause(atom: Atomic): Clause =
        // if we are computing conflicts, both must exist
        val (posImp, posSrc) = assignment(Pos(atom))
        val (negImp, negSrc) = assignment(Neg(atom))
        val allImplicants = posImp ++ negImp
        // every implicant must be existing decision levels
        val implicantLiterals = (allImplicants: Set[Int]).map(decisions(_))
        // we have a proof of false, i.e. just combine posImp, negImp
        // essentially, this is a proof of the sequent
        // /\ implicantLiterals |- false
        // or equivalently () |- \/ !implicantLiterals
        val contra = Combine(posSrc, negSrc)
        Clause(implicantLiterals.map(l => !l).toSet, contra)

      val backjumpLevel = conflictingAtoms.map(backjumpOf).min
      val conflictClauses = conflictingAtoms.map(conflictClause)
      Some((conflictClauses, backjumpLevel))

  private def cdcl(
    clauses: Set[Clause],
    frees: Set[Atomic],
    assignment: Assignment,
    decisions: Map[Int, Literal],
    decisionLevel: Int
  ): SatResult =
    // unit propagate
    val propagatedAssignment = unitPropagate(clauses, assignment, decisionLevel)
    // check for conflicts at the current level
    val conflict = analyzeConflict(frees, propagatedAssignment, decisions, decisionLevel)
    conflict match
      case Some((conflictClauses, backjumpLevelRaw)) =>
        // backjump with learned clauses
        if backjumpLevelRaw <= 0 then
          // clauses are inconsistent at decision level 0
          // return unsat
          // how do we construct a proof here?
          // since we must have a conflict cause implicants |- false with no implicants
          // we must have an empty clause? or a conflicting pair?
          val allClauses = clauses ++ conflictClauses
          lazy val emptyClause = allClauses.filter(_.isEmpty).headOption.map(_.source)
          lazy val conflictingPair = allClauses
                                      .findDefined(c1 => allClauses.find(c2 => c1.negationOf(c2)).map(c2 => (c1, c2)))
                                      .map((c1, c2) => Combine(c1.source, c2.source))
          val contra = emptyClause.orElse(conflictingPair).getOrElse(throw CDCL.NoConflictingClauseException)
          Unsat
        else
          // add learned clauses to the set of clauses
          // and continue with the new assignment
          val backjumpLevel = math.max(backjumpLevelRaw, 0)
          val newAssignment = rollback(propagatedAssignment, backjumpLevel)
          val newClauses = clauses ++ conflictClauses
          cdcl(newClauses, frees, newAssignment, decisions, backjumpLevel)
      case None =>
        // unit propagation was consistent
        // check if we are done
        if propagatedAssignment.size == frees.size then
          // all free variables are assigned
          th.checkSat(propagatedAssignment.keySet.toSeq)
        else
          // decide
          val nextDecisionLevel = decisionLevel + 1
          val nextDecision = frees.diff(propagatedAssignment.keySet.map(_.atom)).head

          val nextCycle = (lit: Literal) =>
            cdcl(
              clauses,
              frees,
              propagatedAssignment + (lit -> (SortedSet(nextDecisionLevel), Decision)),
              decisions + (nextDecisionLevel -> lit),
              nextDecisionLevel
            )

          nextCycle(Pos(nextDecision))
            .orElse:
              nextCycle(Neg(nextDecision))

  private def mapCNF(
      cnf: CNF[Atom]
  ): Set[Clause] =
    def unrollOne(clause: theories.Clause[Atom]): Clause =
      Clause(clause.pos.map(Pos(_)) ++ clause.neg.map(Neg(_)), Problem)
    
    cnf.clauses.map(unrollOne).toSet
    
  def checkSat(f: Formula): SatResult = 
    val cnf = f.toCNF
    val frees = cnf.frees
    val clauses = mapCNF(cnf)
    val emptyDecisions = Map.empty[Int, Literal]
    val decisionLevel = -1

    // decide unit clauses (as negative decision levels)
    val decisions = clauses.filter(_.isUnit).zipWithIndex.map((clause, i) => (-(i + 1), clause.literals.head)).toMap
    val assignment = decisions.map((k, v) => (v, SortedSet(k) -> Problem))

    // check and reject trivial cases
    if clauses.isEmpty then
      return th.checkSat(Seq.empty)
    else if clauses.exists(_.isEmpty) then
      return Unsat

    cdcl(clauses, frees, assignment, decisions, decisionLevel)

end CDCL
