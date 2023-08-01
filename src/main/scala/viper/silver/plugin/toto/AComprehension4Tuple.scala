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
    val A = receiver.typ
    val VB = mapping match {
      case Some(m) =>
        m.typ match {
          case d: DomainType if d.domainName == "Mapping" =>
            d.typVarsMap.values
          case _ => throw new Exception("Mapping must be a mapping")
        }
      case None => throw new Exception("Not implemented")
    }
    if (VB.size != 2) {
      throw new Exception("Mapping must be a mapping from 2 variables")
    }
    val V = VB.head
    val B = VB.tail.head
    (A, V, B)
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
