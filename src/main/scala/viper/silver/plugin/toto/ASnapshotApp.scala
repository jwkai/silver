package viper.silver.plugin.toto

import viper.silver.ast.{Declaration, ErrorTrafo, Exp, ExtensionExp, Field, Info, MapType, NoInfo, NoPosition, NoTrafos, Node, Position, Type}
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.{FastPrettyPrinter, PrettyPrintPrimitives}
import viper.silver.verifier.VerificationResult

case class ASnapshotApp(comprehension4Tuple: AComprehension4Tuple, filter: Exp, field: String)
                       (val pos: Position = NoPosition, val info: Info = NoInfo,
                                           val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  private var snapshotFunctionDeclaration : Declaration = _

  def linkToSnapFunction(d: Declaration): Unit = {
    snapshotFunctionDeclaration = d
  }

  def getSnapFunctionDeclaration : Declaration = {
    snapshotFunctionDeclaration
  }

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    //TODO
    text("snap_") <+> FastPrettyPrinter.show(field)
  }

  // Is field considered a subnode?
  override val extensionSubnodes: Seq[Node] = Seq(comprehension4Tuple, filter).flatten

  override def extensionIsPure: Boolean = true

  // TODO
  override def typ: Type = MapType(filter.typ.typeVariables.head,
    comprehension4Tuple.mapping.getOrElse(comprehension4Tuple.unit).typ)

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented");
  }
}
