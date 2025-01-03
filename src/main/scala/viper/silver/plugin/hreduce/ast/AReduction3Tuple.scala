package viper.silver.plugin.hreduce.ast

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.plugin.hreduce.DomainsGenerator
import viper.silver.verifier.VerificationResult

sealed trait AReduction3Tuple extends ExtensionExp {
  def receiver: Exp
  def op: Exp
  def mapping: Exp

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("hreduce") <+>  toParenDoc(op) <+> toParenDoc(receiver)

  override val extensionSubnodes: Seq[Node] = Seq(receiver, mapping, op).flatten

  override def extensionIsPure: Boolean = true

  override def typ: Type = op.typ match {
    case d @ DomainType(DomainsGenerator.opDKey, _) =>
      d.typVarsMap.values.head
    case _ => throw new Exception("Operator must be an operator. Resolving should have failed.")
  }

  val tripleType: (Type, Type, Type)   = {
    val recA = receiver.typ match {
      case d: DomainType if d.domainName == DomainsGenerator.recDKey =>
        d.typVarsMap.values
      case _ => throw new Exception(s"Receiver must be a ${DomainsGenerator.recDKey} type")
    }
    if (recA.size != 1) {
      throw new Exception("Receiver must be a Receiver of 1 variable. Resolving should have failed.")
    }
    val A = recA.head
    val VB = mapping.typ match {
      case d: DomainType if d.domainName == DomainsGenerator.mapDKey =>
        d.typVarsMap.values
      case _ => throw new Exception(s"Mapping must be a ${DomainsGenerator.mapDKey} type. " +
        s"Resolving should have failed.")
    }
    if (VB.size != 2) {
      throw new Exception("Mapping must be a mapping from 2 variables")
    }
    val V = VB.head
    val B = VB.tail.head
    (A, V, B)
  }

  def reduceDKeyName(): String
  def reduceConstructKeyName(): String
  def reduceEvalFuncName(): String

  def toViper(input: Program) : DomainFuncApp = {
    val typeVars = input.findDomain(reduceDKeyName()).typVars
    if (typeVars.length != 3) {
      throw new Exception("Reduce domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> tripleType._1,
      typeVars(1) -> tripleType._2,
      typeVars(2) -> tripleType._3
    )
    val reduceFunc = input.findDomainFunction(reduceConstructKeyName())
    DomainFuncApp.apply(reduceFunc, Seq(receiver, mapping, op), typeVarMap)(pos, info, errT)
  }
  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented")
  }
}

object AReduction3Tuple {
  def apply(receiver: Exp, mapping: Exp, op: Exp, hasID: Boolean)
           (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): AReduction3Tuple =
  if (hasID) {
    AReduction3TupleWithId(receiver, mapping, op)(pos, info, errT)
  } else {
    AReduction3TupleWithoutId(receiver, mapping, op)(pos, info, errT)
  }

  def unapply(a: AReduction3Tuple): Some[(Exp, Exp, Exp)] = Some((a.receiver, a.mapping, a.op))
}

case class AReduction3TupleWithId(receiver: Exp, mapping: Exp, op: Exp)
                           (val pos: Position = NoPosition, val info: Info = NoInfo,
                                                     val errT: ErrorTrafo = NoTrafos) extends AReduction3Tuple {
  override def reduceDKeyName(): String = DomainsGenerator.reduceDKeyM
  override def reduceConstructKeyName(): String = DomainsGenerator.reduceConstructKeyM
  override def reduceEvalFuncName(): String = DomainsGenerator.reduceApplyKeyM
}

case class AReduction3TupleWithoutId(receiver: Exp, mapping: Exp, op: Exp)
                                 (val pos: Position = NoPosition, val info: Info = NoInfo,
                                  val errT: ErrorTrafo = NoTrafos) extends AReduction3Tuple {
  override def reduceDKeyName(): String = DomainsGenerator.reduceDKeyS
  override def reduceConstructKeyName(): String = DomainsGenerator.reduceConstructKeyS
  override def reduceEvalFuncName(): String = DomainsGenerator.reduceApplyKeyS
}