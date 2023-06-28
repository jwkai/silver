package viper.silver.plugin.toto

import viper.silver.ast.{ErrorTrafo, Exp, ExtensionExp, Info, NoInfo, NoPosition, NoTrafos, Node, Position, Type}
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.VerificationResult


case class Comprehension(op: Exp, unit: Exp, receiver: Exp, filter: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo,
                                     val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("comp") <+>  toParenDoc(op) <+> toParenDoc(unit) <+> toParenDoc(receiver) <+> toParenDoc(filter)

  override val extensionSubnodes: Seq[Node] = Seq(op, unit, receiver, filter)

  override def extensionIsPure: Boolean = true

  override def typ: Type = unit.typ

  override def verifyExtExp(): VerificationResult = ???
}
