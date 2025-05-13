package theories

import optimus.optimization.*
import optimus.optimization.enums.SolverLib
import optimus.optimization.model.MPFloatVar
import optimus.algebra.Int2Const
import optimus.algebra.Constraint
import optimus.algebra.Expression
import optimus.algebra
import optimus.optimization.model.MPIntVar

object LRA:
  sealed trait RealTerm
  case class RealVar(name: String) extends RealTerm
  case class RealConst(value: Double) extends RealTerm
  case class RealLinear(coeff: RealConst, atom: RealVar) extends RealTerm
  case class RealAdd(left: RealTerm, right: RealTerm) extends RealTerm

  // syntax
  extension (ra: RealTerm)
    def +(that: RealTerm): RealTerm = RealAdd(ra, that)

  extension (ra: RealVar)
    def *(that: RealConst): RealTerm = RealLinear(that, ra)
  
  extension (ra: RealConst)
    def *(that: RealVar): RealTerm = RealLinear(ra, that)

  given Conversion[Double, RealConst] with
    def apply(d: Double): RealConst = RealConst(d)

  object Real:
    def apply(name: String): RealVar = RealVar(name)

  sealed trait Real
  case class RealEq(left: RealTerm, right: RealTerm) extends Real
  case class RealLe(left: RealTerm, right: RealTerm) extends Real
  case class RealLt(left: RealTerm, right: RealTerm) extends Real

  extension (ra: RealTerm)
    def <=(that: RealTerm): Real = RealLe(ra, that)
    def ===(that: RealTerm): Real = RealEq(ra, that)
    def <(that: RealTerm): Real = RealLt(ra, that)

  given Theory[Real] with
    object Opt:
      private val optVars = scala.collection.mutable.Map[String, MPFloatVar]()
      def getVar(name: String): MPFloatVar = 
        optVars.getOrElseUpdate(name, MPFloatVar(name))

    def toOptimus(t: RealTerm): Expression = t match
      case RealVar(name) => Opt.getVar(name)
      case RealConst(value) => algebra.Const(value)
      case RealLinear(coeff, atom) => toOptimus(coeff) * toOptimus(atom)
      case RealAdd(left, right) => toOptimus(left) + toOptimus(right)
    
    def toOptimus(f: Atom): Constraint = f match
      case RealEq(left, right) => toOptimus(left) := toOptimus(right)
      case RealLe(left, right) => toOptimus(left) <:= toOptimus(right)
      case RealLt(left, right) => throw new Exception("RealLt not supported")
    override def checkSat(fs: Seq[Literal]): SatResult = 
      // this is the hard part :)
      val inequalities = fs.flatMap:
        case Pos(RealLe(left, right)) => Seq((left, right))
        case Pos(RealEq(left, right)) => Seq((left, right))
        case Neg(RealLe(left, right)) => Seq((right, left))
        case Neg(RealEq(left, right)) => Seq((right, left))
        case _ => throw new Exception("Unexpected Real atom")
      ???

    override def preprocess(f: Formula): Formula = f.map:
      case Atom(RealLe(left, right)) => And(Atom(RealLt(left, right)), Not(Atom(RealEq(left, right))))
      case ff => ff

    override def wellformed(f: Formula): Boolean = true

    given optModel: MPModel = MPModel(SolverLib.oJSolver)

    val x = MPFloatVar("x")
    val y = MPFloatVar("y")

    add(x + y <:= 1)
    

    @main
    def go: Unit =
      start()
      println(s"${x.value} ${y.value}")
      release()

    // simplex

    // start with a vector pointing to the first hyperplane, from the origin
    // given the next hyperplane, walk along the edge to the next hyperplane
    // repeat

    // how does this generalize to n-dimensions?
    // how do you pick a direction on the hyperplane?

    // given a hyperplane, you have an n-1d tangent space
    // choose any vector, and solve the single equation to find (and cross) the next plane?


object LIA:
  sealed trait IntTerm
  case class IntVar(name: String) extends IntTerm
  case class IntConst(value: Double) extends IntTerm
  case class IntLinear(coeff: IntConst, atom: IntVar) extends IntTerm
  case class IntAdd(left: IntTerm, right: IntTerm) extends IntTerm

  // syntax
  extension (ra: IntTerm)
    def +(that: IntTerm): IntTerm = IntAdd(ra, that)

  extension (ra: IntVar)
    def *(that: IntConst): IntTerm = IntLinear(that, ra)
  
  extension (ra: IntConst)
    def *(that: IntVar): IntTerm = IntLinear(ra, that)

  given Conversion[Double, IntConst] with
    def apply(d: Double): IntConst = IntConst(d)

  object LInt:
    def apply(name: String): IntVar = IntVar(name)

  sealed trait LInt
  case class IntEq(left: IntTerm, right: IntTerm) extends LInt
  case class IntLe(left: IntTerm, right: IntTerm) extends LInt
  case class IntLt(left: IntTerm, right: IntTerm) extends LInt

  extension (ra: IntTerm)
    def <=(that: IntTerm): LInt = IntLe(ra, that)
    def ===(that: IntTerm): LInt = IntEq(ra, that)
    def <(that: IntTerm): LInt = IntLt(ra, that)

  given Theory[LInt] with
    object Opt:
      private val optVars = scala.collection.mutable.Map[String, MPFloatVar]()
      def getVar(name: String): MPFloatVar = 
        optVars.getOrElseUpdate(name, MPFloatVar(name))

    def toOptimus(t: IntTerm): Expression = t match
      case IntVar(name) => Opt.getVar(name)
      case IntConst(value) => algebra.Const(value)
      case IntLinear(coeff, atom) => toOptimus(coeff) * toOptimus(atom)
      case IntAdd(left, right) => toOptimus(left) + toOptimus(right)
    
    def toOptimus(f: Atom): Constraint = f match
      case IntEq(left, right) => toOptimus(left) := toOptimus(right)
      case IntLe(left, right) => toOptimus(left) <:= toOptimus(right)
      case IntLt(left, right) => throw new Exception("IntLt not supported")
    override def checkSat(fs: Seq[Literal]): SatResult = 
      // this is the hard part :)
      val inequalities = fs.flatMap:
        case Pos(IntLe(left, right)) => Seq((left, right))
        case Pos(IntEq(left, right)) => Seq((left, right))
        case Neg(IntLe(left, right)) => Seq((right, left))
        case Neg(IntEq(left, right)) => Seq((right, left))
        case _ => throw new Exception("Unexpected Int atom")
      ???

    override def preprocess(f: Formula): Formula = f.map:
      case Atom(IntLe(left, right)) => And(Atom(IntLt(left, right)), Not(Atom(IntEq(left, right))))
      case ff => ff

    override def wellformed(f: Formula): Boolean = true

    given optModel: MPModel = MPModel(SolverLib.oJSolver)

    // val x = MPIntVar("x")
    // val y = MPIntVar("y")

    // add(x + y <:= 1)

    // @main
    // def gogo: Unit =
    //   start()
    //   println(s"${x.value} ${y.value}")
    //   release()

    // simplex

    // start with a vector pointing to the first hyperplane, from the origin
    // given the next hyperplane, walk along the edge to the next hyperplane
    // repeat

    // how does this generalize to n-dimensions?
    // how do you pick a direction on the hyperplane?

    // given a hyperplane, you have an n-1d tangent space
    // choose any vector, and solve the single equation to find (and cross) the next plane?
    