package viper.silver.plugin.toto

import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.verifier.VerificationResult

case class ASnapshotApp(comprehension4Tuple: AComprehension4Tuple, filter: Exp, field: String)
                       (val pos: Position = NoPosition, val info: Info = NoInfo,
                                           val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  var snapshotFunctionDeclaration : Declaration = {
    val receiverType = comprehension4Tuple.tripleType
    ASnapshotDecl.getOrMakeNewSnapDecl(receiverType, field)
  }

//  def linkToSnapFunction(d: Declaration): Unit = {
//    snapshotFunctionDeclaration = d
//  }
//
//  def getSnapFunctionDeclaration : Declaration = {
//    snapshotFunctionDeclaration
//  }

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    //TODO
    text("snap_") <+> field
  }

  // Is field considered a subnode?
  override val extensionSubnodes: Seq[Node] = Seq(comprehension4Tuple, filter)

  override def extensionIsPure: Boolean = true

  // TODO
  override def typ: Type = {
    val filterOn = filter.typ match {
      case c : SetType =>
        c.elementType
      case _ =>
        throw new Exception("Filter must be a set")
    }
    MapType(filterOn, comprehension4Tuple.unit.typ)
  }
  //    MapType(filter.typ.typeVariables.head,
//    comprehension4Tuple.mapping.getOrElse(comprehension4Tuple.unit).typ)

  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented");
  }
}
