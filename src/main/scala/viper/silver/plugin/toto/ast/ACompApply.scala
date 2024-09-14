package viper.silver.plugin.toto.ast

import viper.silver.ast.pretty.FastPrettyPrinter._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.{Position, _}
import viper.silver.plugin.toto.DomainsGenerator
import viper.silver.verifier.VerificationResult

case class ACompApply(comp: AComprehension3Tuple, filter: Exp, fieldName: String)
                     (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
  extends ExtensionExp {

  var compFunctionDeclaration: ACompDecl = {
    val receiverType = comp.tripleType
    ACompDecl(receiverType, fieldName)
  }

  var fHeap: AFHeap = null

  def toViper(input: Program): Exp = {
    val compEvalFunc = input.findDomainFunction(DomainsGenerator.compApplyKey)
    val compConstructed = comp.toViper(input)

    DomainFuncApp(
      compEvalFunc,
      Seq(fHeap, compConstructed, filter),
      compConstructed.typVarMap
    )(this.pos, this.info, this.errT + NodeTrafo(this))
  }

  def includeMapping(inside: Cont, mapping: Exp): Cont = {
    val mapApplied = mapping.asInstanceOf[DomainFuncApp]
    if (mapApplied.funcname == DomainsGenerator.mapIdenKey) {
      inside
    } else {
      text(mapApplied.funcname) <> parens(ssep(inside +: (mapApplied.args map show), group(char (',') <> line)))
    }
  }

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text(DomainsGenerator.compConstructKey) <> brackets(show(comp.op)) <>
      parens(includeMapping(show(comp.receiver) <> char('.') <> text(fieldName), comp.mapping) <+>
        char('|') <+> show(filter))

  override val extensionSubnodes: Seq[Node] = Seq(comp, filter)

  override def extensionIsPure: Boolean = true

  override def typ: Type = comp.typ

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented")
  }
}
