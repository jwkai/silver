package viper.silver.plugin.hreduce.ast

import viper.silver.ast.pretty.FastPrettyPrinter._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.{Position, _}
import viper.silver.plugin.hreduce.DomainsGenerator
import viper.silver.verifier.VerificationResult

case class AReduceApply(reduction: AReduction3Tuple, filter: Exp, fieldName: String)
                       (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
  extends ExtensionExp {

  var reduceFunctionDeclaration: AReduceDecl = {
    val receiverType = reduction.tripleType
    AReduceDecl(receiverType, fieldName)
  }

  var rHeap: Option[ARHeap] = None

  def toViper(input: Program): Exp = {
    val reduceEvalFunc = input.findDomainFunction(DomainsGenerator.reduceApplyKey)
    val reduceConstructed = reduction.toViper(input)

    rHeap match {
      case Some(fh) =>
        DomainFuncApp(
          reduceEvalFunc,
          Seq(fh.toExp, reduceConstructed, filter),
          reduceConstructed.typVarMap
        )(this.pos, this.info, this.errT + NodeTrafo(this))
      case None =>
        throw new Exception("Reduce to Viper undefined with rHeap = None")
    }

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
    text(DomainsGenerator.reduceConstructKey) <> brackets(show(reduction.op)) <>
      parens(includeMapping(show(reduction.receiver) <> char('.') <> text(fieldName), reduction.mapping) <+>
        char('|') <+> show(filter))

  override val extensionSubnodes: Seq[Node] = Seq(reduction, filter)

  override def extensionIsPure: Boolean = true

  override def typ: Type = reduction.typ

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented")
  }
}