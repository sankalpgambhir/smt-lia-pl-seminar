package theories

trait Model:
  override def toString(): String = prettyModel

  def prettyModel: String

trait SatResult[+T]:
  def isSat: Boolean = this match
    case Sat(_) => true
    case _ => false
  
case class Sat[T <: Model](model: T) extends SatResult[T]
case object Unsat extends SatResult[Nothing]
case object Unknown extends SatResult[Nothing]

extension [M <: Model] (o: Option[M])
  def asSatResult: SatResult[M] = o match
    case Some(m) => Sat(m)
    case None => Unsat

trait Theory[T]:
  type Atom = T
  type Model <: theories.Model
  
  type Atomic = theories.Atomic[Atom]
  type Formula = theories.Formula[Atom]
  type SatResult = theories.SatResult[Model]

  /**
    * Check whether a conjunction of atoms in this theory are consistent. If
    * yes, produce a theory model.
    */
  def checkSat(fs: Seq[Atom]): SatResult

  /**
    * Preprocess a formula as required by the theory
    */
  def preprocess(f: Formula): Formula

  /**
    * Is this formula well-formed and within the fragment of this theory?
    */
  def wellformed(f: Formula): Boolean
