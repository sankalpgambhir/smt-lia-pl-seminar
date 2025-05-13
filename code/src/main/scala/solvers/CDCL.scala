package solvers

import theories.*

class CDCL[T: Theory]() extends TheorySolver[T]:
  import th.*

  type Implicants = Set[Int]
  type Assignment = Map[Literal, Implicants]

  case class Clause(lits: Set[Literal]):
    def isEmpty: Boolean = lits.isEmpty
    def contains(lit: Literal): Boolean = lits.contains(lit)
    def isFalsified(model: Set[Literal]): Boolean =
      lits.forall(l => model.contains(!l))
    def unitDecomposition(model: Assignment): Option[(Literal, Implicants)] =
      val remainingLits = lits.filterNot(l => model.contains(!l))
      if remainingLits.size == 1 then
        val lit = remainingLits.head
        // implicants *not* minimized to UIP
        val implicants = lits.flatMap(l => model.getOrElse(l, Set()))
        Some((lit, implicants))
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
      decisions: Seq[Literal],
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
        val posLevel = posImp.max
        val negLevel = negImp.max
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
    decisions: Seq[Literal],
    decisionLevel: Int
  ): SatResult =
    // unit propagate
    val propagatedAssignment = unitPropagate(clauses, assignment, decisionLevel)
    // check for conflicts at the current level
    val conflict = analyzeConflict(frees, propagatedAssignment, decisions, decisionLevel)
    conflict match
      case Some((conflictClauses, backjumpLevel)) =>
        // backjump with learned clauses
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
              decisions :+ lit,
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
    val assignment = Map.empty[Literal, Implicants]
    val decisions = Seq.empty[Literal]
    val decisionLevel = 0

    cdcl(clauses, frees, assignment, decisions, decisionLevel)


end CDCL
