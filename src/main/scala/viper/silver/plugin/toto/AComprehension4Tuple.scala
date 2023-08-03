package viper.silver.plugin.toto

import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.verifier.VerificationResult


case class AComprehension4Tuple(receiver: Exp, mapping: Option[Exp], op: Exp, unit: Exp)
                               (val pos: Position = NoPosition, val info: Info = NoInfo,
                                                     val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("comp") <+>  toParenDoc(op) <+> toParenDoc(unit) <+> toParenDoc(receiver)

  override val extensionSubnodes: Seq[Node] = Seq(receiver, mapping, op, unit).flatten

  override def extensionIsPure: Boolean = true

  override def typ: Type = unit.typ


  val tripleType: (Type, Type, Type)   = {
    val recA = receiver.typ match {
      case d: DomainType if d.domainName == "Receiver" =>
        d.typVarsMap.values
      case _ => throw new Exception("Receiver must be a  type")
    }
    if (recA.size != 1) {
      throw new Exception("Receiver must be a Receiver of 1 variable. Resolving should have failed.")
    }
    val A = recA.head
    val VB = mapping match {
      case Some(m) =>
        m.typ match {
          case d: DomainType if d.domainName == "Mapping" =>
            d.typVarsMap.values
          case _ => throw new Exception("Mapping must be a mapping. Resolving should have failed.")
        }
      case None => Seq(unit.typ, unit.typ)
    }
    if (VB.size != 2) {
      throw new Exception("Mapping must be a mapping from 2 variables")
    }
    val V = VB.head
    val B = VB.tail.head
    (A, V, B)
  }


  def toViper(input: Program) : DomainFuncApp = {
    val typeVars = input.findDomain("Comp").typVars
    if (typeVars.length != 3) {
      throw new Exception("Comp domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> tripleType._1,
      typeVars(1) -> tripleType._2,
      typeVars(2) -> tripleType._3
    )
//    val typViper = DomainType.apply(compDomain, typeVarMap)
    val compFunc = input.findDomainFunction("comp")
    DomainFuncApp.apply(compFunc, Seq(receiver, mapping.orNull, op, unit), typeVarMap)(pos, info, errT)
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
