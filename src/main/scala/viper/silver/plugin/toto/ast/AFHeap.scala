package viper.silver.plugin.toto.ast

import viper.silver.ast.{Position, _}
import viper.silver.ast.pretty.FastPrettyPrinter._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.plugin.toto.DomainsGenerator
import viper.silver.verifier.VerificationResult

case class AFHeap(name: String)
                 (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
  extends ExtensionExp {

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq()

  override def typ: Type = AFHeap.getType

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented")
  }

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
   * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(name)
}

object AFHeap {
  def getType: Type = DomainType(DomainsGenerator.fHeapKey, Map[viper.silver.ast.TypeVar,viper.silver.ast.Type]())(Nil)
}