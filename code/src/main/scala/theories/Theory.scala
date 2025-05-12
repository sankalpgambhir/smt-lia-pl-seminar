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

trait Theory[-T]:
  type Atom
  type Atomic = theories.Atomic[Atom]
  type Formula = theories.Formula[Atom]
  type Model <: theories.Model
  type SatResult = theories.SatResult[Model]

  def checkSat(fs: Seq[Atom]): SatResult

  def preprocess(f: Formula): Formula
