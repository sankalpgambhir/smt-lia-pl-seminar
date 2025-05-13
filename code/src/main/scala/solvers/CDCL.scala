package solvers

import theories.*

class CDCL[T: Theory]() extends TheorySolver[T]:
  import th.*

  type Implicants = Set[Int]
  type Assignment = Map[Literal, Implicants]

  case class Clause(lits: Set[Literal]):
    def isEmpty: Boolean = lits.isEmpty
    def isUnit: Boolean = lits.size == 1
    def contains(lit: Literal): Boolean = lits.contains(lit)
    def isValidated(model: Assignment): Boolean =
      lits.exists(l => model.contains(l))
    def unitDecomposition(model: Assignment): Option[(Literal, Implicants)] =
      val remainingLits = lits.filterNot(l => model.contains(!l))
      if remainingLits.size == 1 then
        val lit = remainingLits.head
        // implicants *not* minimized to UIP
        val implicants = lits.flatMap(l => model.getOrElse(l, Set()))
        // if there are no implicants, this is a unit clause in the input
        // it is unit propagated at decision level 0
        val paddedImplicants = if implicants.isEmpty then Set(0) else implicants
        Some((lit, paddedImplicants))
      // empty is possible, but should be handled by initializing the assignment
      // with "true" unit clauses
      // else if remainingLits.isEmpty then
      else None
  
  private def unitPropagateRec(
      leftClauses: List[Clause],
      openClauses: List[Clause],
      assignment: Assignment,
      decisionLevel: Int
  ): (Assignment, List[Clause]) =
    leftClauses match
      case Nil          => (assignment, openClauses)
      case head :: next => 
        // can we unit propagate off of head?
        head.unitDecomposition(assignment) match
          case None => 
            // leave head around in open clauses, move on
            unitPropagateRec(next, head :: openClauses, assignment, decisionLevel)
          case Some(kv) =>
            val locallyUpdatedAssignment = assignment + kv
            val (newAssignment, leftOpen) = unitPropagateRec(
              openClauses,
              List.empty,
              locallyUpdatedAssignment,
              decisionLevel
            )
            // continue with the rest of the clauses
            unitPropagateRec(
              next,
              leftOpen,
              newAssignment,
              decisionLevel
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
    )._1

  private def rollback(
      assignment: Assignment,
      to: Int
  ): Assignment = 
    assignment.filterNot((_, implicants) => implicants.exists(_ > to))

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
        val posImp = assignment.getOrElse(Pos(atom), Set.empty) - currentDecisionLevel
        val negImp = assignment.getOrElse(Neg(atom), Set.empty) - currentDecisionLevel
        val posLevel = posImp.maxOption.getOrElse(0)
        val negLevel = negImp.maxOption.getOrElse(0)
        math.max(posLevel, negLevel)

      def conflictClause(atom: Atomic): Clause =
        val posImp = assignment.getOrElse(Pos(atom), Set.empty)
        val negImp = assignment.getOrElse(Neg(atom), Set.empty)
        val allImplicants = posImp ++ negImp
        // every implicant must be existing decision levels
        val implicantLiterals = allImplicants.map(decisions(_))
        Clause(implicantLiterals.map(l => !l).toSet)

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
              propagatedAssignment + (lit -> Set(nextDecisionLevel)),
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
      Clause(clause.pos.map(Pos(_)) ++ clause.neg.map(Neg(_)))
    
    cnf.clauses.map(unrollOne).toSet
    
  def checkSat(f: Formula): SatResult = 
    val cnf = f.toCNF
    val frees = cnf.frees
    val clauses = mapCNF(cnf)
    val emptyDecisions = Map.empty[Int, Literal]
    val decisionLevel = -1

    // decide unit clauses (as negative decision levels)
    val decisions = clauses.filter(_.isUnit).zipWithIndex.map((clause, i) => (-(i + 1), clause.lits.head)).toMap
    val assignment = decisions.map((k, v) => (v, Set(k)))

    // check and reject trivial cases
    if clauses.isEmpty then
      return th.checkSat(Seq.empty)
    else if clauses.exists(_.isEmpty) then
      return Unsat

    cdcl(clauses, frees, assignment, decisions, decisionLevel)


end CDCL
