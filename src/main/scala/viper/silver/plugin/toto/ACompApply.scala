package viper.silver.plugin.toto

import viper.silver.ast.pretty.FastPrettyPrinter._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.{Position, _}
import viper.silver.verifier.VerificationResult

case class ACompApply(comp: AComprehension3Tuple, snap: ASnapshotApp)(val pos: Position = NoPosition, val info: Info = NoInfo,
                                                                      val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  def toViper(input: Program) : Exp = {

    val compEvalFunc = input.findDomainFunction(DomainsGenerator.compApplyKey)
    val compConstructed = comp.toViper(input)
    val snapConstructed = snap.toViper(input)

    DomainFuncApp(compEvalFunc,
      Seq(compConstructed, snapConstructed), compConstructed.typVarMap
    )(this.pos, this.info, this.errT)

//    DomainFuncApp(DomainsGenerator.compEvalKey, Seq(comp.toViper(input), snap.toViper(input)), Map())(
//      pos, info, comp.tripleType._3 , DomainsGenerator.compDKey , errT
//    )
  }

  def includeMapping(inside: Cont, mapping: Exp): Cont = {
    val mapApplied = mapping.asInstanceOf[DomainFuncApp]
    if (mapApplied.funcname == "mapIdenKey") {
      inside
    } else {
      text(mapApplied.funcname) <> parens(ssep(inside +: (mapApplied.args map show), group(char (',') <> line)))
    }
  }


  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text(DomainsGenerator.compConstructKey) <> brackets(show(comp.op)) <>
      parens(includeMapping(show(comp.receiver) <> char('.') <> text(snap.field), comp.mapping) <+>
        char('|') <+> show(snap.filter))
  //parens(ssep(Seq(show(comp), show(snap)), group(char (',') <> line)))

  override val extensionSubnodes: Seq[Node] = Seq(comp, snap)

  override def extensionIsPure: Boolean = true

  override def typ: Type = comp.typ

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented");
  }
}
