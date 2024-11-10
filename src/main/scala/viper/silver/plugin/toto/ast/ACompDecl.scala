package viper.silver.plugin.toto.ast

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.plugin.toto.DomainsGenerator
import viper.silver.plugin.toto.util.AxiomHelper.tupleFieldToString

// Constructor should not be called directly, use getOrMakeNewSnapDecl
case class ACompDecl private(compType: (Type, Type, Type), fieldName: String)(val pos : Position = NoPosition)
  extends ExtensionMember
{
  def key: String = tupleFieldToString(compType, fieldName)

  override def name: String = key
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(key)

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = Seq()

  val outType: Type = compType._3

  def compDType(input: Program): DomainType = {
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

  def compDRecvType(input: Program): DomainType = {
    val recvDomain = input.findDomain(DomainsGenerator.recDKey)
    val typeVars = recvDomain.typVars
    if (typeVars.length != 1) {
      throw new Exception("Receiver domain must have 1 type variable")
    }
    val typeVarMap = Map(
      typeVars.head -> compType._1,
    )
    DomainType.apply(recvDomain, typeVarMap)
  }

  def findFieldInProgram(p: Program): Field = {
    p.findField(fieldName)
  }
}


object ACompDecl {

  private val compDecls: scala.collection.mutable.Map[String, ACompDecl] = scala.collection.mutable.Map()

  private var uniqueFieldInt = 0

  private val fieldIDMap: scala.collection.mutable.Map[String, Int] = scala.collection.mutable.Map()

  private def getOrMakeNewCompDecl(compType: (Type, Type, Type), fieldID: String): ACompDecl = {
    val key = tupleFieldToString(compType, fieldID)
    addFieldtoMap(fieldID)
    compDecls.getOrElseUpdate(key, new ACompDecl(compType, fieldID)(NoPosition))
  }

  def apply(compType: (Type, Type, Type), fieldID: String): ACompDecl = {
    getOrMakeNewCompDecl(compType, fieldID)
  }

  def addFieldtoMap(fieldName: String): Unit = {
    if (!fieldIDMap.contains(fieldName)) {
      fieldIDMap(fieldName) = uniqueFieldInt
      uniqueFieldInt += 1
    }
  }

  def getFieldInt(field: String): Int = {
    fieldIDMap(field)
  }
}
