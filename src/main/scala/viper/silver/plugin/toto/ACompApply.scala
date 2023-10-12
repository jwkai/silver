package viper.silver.plugin.toto

import viper.silver.ast.{DomainFuncApp, ErrorTrafo, Exp, ExtensionExp, Info, NoInfo, NoPosition, NoTrafos, Node, Position, Program, Type}
import viper.silver.ast.pretty.FastPrettyPrinter._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.VerificationResult

case class ACompApply(comp: AComprehension3Tuple, snap: ASnapshotApp)(val pos: Position = NoPosition, val info: Info = NoInfo,
                                                                      val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  def toViper(input: Program) : Exp = {

    val compEvalFunc = input.findDomainFunction(DomainsGenerator.compApplyKey)
    val compConstructed = comp.toViper(input)
    val snapConstructed = snap.toViper(input)

    DomainFuncApp(compEvalFunc,
      Seq(comp.toViper(input), snap.toViper(input)), compConstructed.typVarMap
    )(this.pos, this.info, this.errT)

//    DomainFuncApp(DomainsGenerator.compEvalKey, Seq(comp.toViper(input), snap.toViper(input)), Map())(
//      pos, info, comp.tripleType._3 , DomainsGenerator.compDKey , errT
//    )
  }

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text(DomainsGenerator.compApplyKey) <+>  parens(ssep(Seq(show(comp), show(snap)), group(char (',') <> line)))

  override val extensionSubnodes: Seq[Node] = Seq(comp, snap)

  override def extensionIsPure: Boolean = true

  override def typ: Type = comp.typ

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented");
  }
}
