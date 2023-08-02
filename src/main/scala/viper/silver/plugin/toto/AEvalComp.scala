package viper.silver.plugin.toto

import viper.silver.ast.{DomainFuncApp, ErrorTrafo, Exp, ExtensionExp, Info, NoInfo, NoPosition, NoTrafos, Node, Position, Type}
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.VerificationResult

case class AEvalComp(comp: AComprehension4Tuple, snap: ASnapshotApp)(val pos: Position = NoPosition, val info: Info = NoInfo,
                                                     val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  def toViper : Exp = {
    DomainFuncApp("evalComp", Seq(comp.toViper, snap.toViper), Map())(
      pos, info, comp.tripleType._3 , "Comp" , errT
    )
  }

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("evalComp") <+>  toParenDoc(comp) <+> toParenDoc(snap)

  override val extensionSubnodes: Seq[Node] = Seq(comp, snap)


  override def extensionIsPure: Boolean = true

  override def typ: Type = comp.typ

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented");
  }
}
