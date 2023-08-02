package viper.silver.plugin.toto

import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.plugin.toto.ASnapshotDecl.tupleFieldToString

// Constructor should not be called directly, use getOrMakeNewSnapDecl
case class ASnapshotDecl private (compType: (Type, Type, Type), fieldID: String)(val pos : Position = NoPosition)
  extends ExtensionMember
{
  def key: String = tupleFieldToString(compType, fieldID)

  override def name: String = key
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(key)

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = Seq()

  val viperDecl: Function = {
    val typeVarMap = Map(
      TypeVar("A") -> compType._1,
      TypeVar("V") -> compType._2,
      TypeVar("B") -> compType._3
    )

    val args0 = LocalVarDecl("c",
      DomainType("Comp", typeVarMap)(typeVarMap.keys.toSeq)
    )()
    val args1 =
      LocalVarDecl("f", SetType(compType._1))()
    Function(name, Seq(args0, args1), compType._3, Seq(), Seq(), None)()
  }



}


object ASnapshotDecl {

  private val snapshotDecls: scala.collection.mutable.Map[String, ASnapshotDecl] = scala.collection.mutable.Map()

  def getOrMakeNewSnapDecl(compType: (Type, Type, Type), fieldID: String): ASnapshotDecl = {
    val key = tupleFieldToString(compType, fieldID)
    snapshotDecls.getOrElseUpdate(key, ASnapshotDecl(compType, fieldID)())
  }

  def tupleFieldToString(t: (Type, Type, Type), fieldID: String): String = {
    "snap_" + t._1.toString() + "_" + t._2.toString() + "_" + t._3.toString() + "_" + fieldID
  }


  def getAllSnapDecls: Seq[Function] = {
    snapshotDecls.values.map(_.viperDecl).toSeq
  }

}
