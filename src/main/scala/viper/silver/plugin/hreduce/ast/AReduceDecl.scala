package viper.silver.plugin.hreduce.ast

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.plugin.hreduce.DomainsGenerator
import viper.silver.plugin.hreduce.util.AxiomHelper.tupleFieldToString

// Constructor should not be called directly, use getOrMakeNewReduceDecl
case class AReduceDecl private(reduceType: (Type, Type, Type), fieldName: String)(val pos : Position = NoPosition)
  extends ExtensionMember
{
  def key: String = tupleFieldToString(reduceType, fieldName)

  override def name: String = key
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(key)

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = Seq()

  val outType: Type = reduceType._3

  def reduceDType(input: Program): DomainType = {
    val reduceDomain = input.findDomain(DomainsGenerator.reduceDKey)
    val typeVars = reduceDomain.typVars
    if (typeVars.length != 3) {
      throw new Exception("Reduce domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> reduceType._1,
      typeVars(1) -> reduceType._2,
      typeVars(2) -> reduceType._3
    )
    DomainType.apply(reduceDomain, typeVarMap)
  }

  def reduceDRecvType(input: Program): DomainType = {
    val recvDomain = input.findDomain(DomainsGenerator.recDKey)
    val typeVars = recvDomain.typVars
    if (typeVars.length != 1) {
      throw new Exception("Receiver domain must have 1 type variable")
    }
    val typeVarMap = Map(
      typeVars.head -> reduceType._1,
    )
    DomainType.apply(recvDomain, typeVarMap)
  }

  def findFieldInProgram(p: Program): Field = {
    p.findField(fieldName)
  }
}


object AReduceDecl {

  private val reduceDecls: scala.collection.mutable.Map[String, AReduceDecl] = scala.collection.mutable.Map()

  private var uniqueFieldInt = 0

  private val fieldIDMap: scala.collection.mutable.Map[String, Int] = scala.collection.mutable.Map()

  private def getOrMakeNewReduceDecl(reduceType: (Type, Type, Type), fieldID: String): AReduceDecl = {
    val key = tupleFieldToString(reduceType, fieldID)
    addFieldtoMap(fieldID)
    reduceDecls.getOrElseUpdate(key, new AReduceDecl(reduceType, fieldID)(NoPosition))
  }

  def apply(reduceType: (Type, Type, Type), fieldID: String): AReduceDecl = {
    getOrMakeNewReduceDecl(reduceType, fieldID)
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
