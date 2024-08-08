package viper.silver.plugin.toto

import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.verifier.VerificationResult


case class AComprehension3Tuple(receiver: Exp, mapping: Exp, op: Exp)
                               (val pos: Position = NoPosition, val info: Info = NoInfo,
                                                     val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("comp") <+>  toParenDoc(op) <+> toParenDoc(receiver)

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


  def toViper(input: Program) : DomainFuncApp = {
    val typeVars = input.findDomain(DomainsGenerator.compDKey).typVars
    if (typeVars.length != 3) {
      throw new Exception("Comp domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> tripleType._1,
      typeVars(1) -> tripleType._2,
      typeVars(2) -> tripleType._3
    )
//    val typViper = DomainType.apply(compDomain, typeVarMap)
    val compFunc = input.findDomainFunction(DomainsGenerator.compConstructKey)
    DomainFuncApp.apply(compFunc, Seq(receiver, mapping, op), typeVarMap)(pos, info, errT)
//    DomainFuncApp("comp", Seq(receiver, mapping.orNull, op, unit),typeVarMap)(
//      pos, info, typViper , "Comp", errT
  }


  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
      throw new Exception("Not implemented");
  }

//  def translateToViper : Exp = {
//    DomainFuncApp
//
//  }

}
