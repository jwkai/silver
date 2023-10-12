package viper.silver.plugin.toto

import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.plugin.toto.ASnapshotDecl.tupleFieldToString

// Constructor should not be called directly, use getOrMakeNewSnapDecl
case class ASnapshotDecl private(compType: (Type, Type, Type), fieldName: String)(val pos : Position = NoPosition)
  extends ExtensionMember
{
  def key: String = tupleFieldToString(compType, fieldName)

  override def name: String = key
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(key)

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = Seq()

  val outType: Type = {
    MapType(compType._1, compType._3)
  }

  def compDType(input: Program) = {
    val compDomain = input.findDomain(DomainsGenerator.compDKey)
    val typeVars = compDomain.typVars
    if (typeVars.length != 3) {
      throw new Exception("Comp domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> compType._1,
      typeVars(1) -> compType._2,
      typeVars(2) -> compType._3
    )
    DomainType.apply(compDomain, typeVarMap)
  }


  def viperDecl(input: Program): Function = {
    val compDomain = input.findDomain(DomainsGenerator.compDKey)
    val typeVars = compDomain.typVars
    if (typeVars.length != 3) {
      throw new Exception("Comp domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> compType._1,
      typeVars(1) -> compType._2,
      typeVars(2) -> compType._3
    )
    val args0 = LocalVarDecl("c",
      DomainType.apply(compDomain, typeVarMap)
    )()
    val args1 = LocalVarDecl("f", SetType(compType._1))()
    Function(name, Seq(args0, args1), outType, Seq(), Seq(), None)()
  }

  def findFieldInProgram(p: Program): Field = {
    p.findField(fieldName)
  }


}


object ASnapshotDecl {

  private val snapshotDecls: scala.collection.mutable.Map[String, ASnapshotDecl] = scala.collection.mutable.Map()

  private def getOrMakeNewSnapDecl(compType: (Type, Type, Type), fieldID: String): ASnapshotDecl = {
    val key = tupleFieldToString(compType, fieldID)
    snapshotDecls.getOrElseUpdate(key, new ASnapshotDecl(compType, fieldID)(NoPosition))
  }

  def apply(compType: (Type, Type, Type), fieldID: String): ASnapshotDecl = {
    getOrMakeNewSnapDecl(compType, fieldID)
  }

  def tupleFieldToString(t: (Type, Type, Type), fieldID: String): String = {
    "__snap_" + t._1.toString() + "_" + t._2.toString() + "_" + t._3.toString() + "_" + fieldID
  }


  def getAllSnapDecls(input: Program) : Seq[Function] = {
    snapshotDecls.values.map(_.viperDecl(input)).toSeq
  }

}
