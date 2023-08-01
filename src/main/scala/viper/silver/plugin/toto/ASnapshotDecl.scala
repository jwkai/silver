package viper.silver.plugin.toto

import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._

// Constructor should not be called directly, use getOrMakeNewSnapDecl
case class ASnapshotDecl private (compType: (Type, Type, Type), fieldID: String)(val pos : Position = NoPosition) extends ExtensionMember
{

  def key: String = compType.toString() + "_" + fieldID

  override def name: String = key
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(key)

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = ???

}


object ASnapshotDecl {

  private val snapshotDecls: scala.collection.mutable.Map[String, ASnapshotDecl] = scala.collection.mutable.Map()

  def getOrMakeNewSnapDecl(compType: (Type, Type, Type), fieldID: String): ASnapshotDecl = {
    val key = compType.toString() + "_" + fieldID
    snapshotDecls.getOrElseUpdate(key, ASnapshotDecl(compType, fieldID)())
  }

}
