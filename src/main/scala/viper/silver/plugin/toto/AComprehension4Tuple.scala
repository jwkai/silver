package viper.silver.plugin.toto

import viper.silver.ast.{ErrorTrafo, Exp, ExtensionExp, Field, Info, LocalVar, NoInfo, NoPosition, NoTrafos, Node, Position, Type}
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.parser.PIdnUse
import viper.silver.verifier.VerificationResult


case class AComprehension4Tuple(receiver: Exp, mapping: Option[Exp], op: Exp, unit: Exp)
                               (val pos: Position = NoPosition, val info: Info = NoInfo,
                                                     val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("comp") <+>  toParenDoc(op) <+> toParenDoc(unit) <+> toParenDoc(receiver)

  override val extensionSubnodes: Seq[Node] = Seq(receiver, mapping, op, unit).flatten

  override def extensionIsPure: Boolean = true

  override def typ: Type = unit.typ

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
      throw new Exception("Not implemented");
  }
}
