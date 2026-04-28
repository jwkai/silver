package viper.silver.plugin.crimp.ast

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.plugin.crimp.DomainsGenerator
import viper.silver.plugin.crimp.util.AxiomHelper.tupleFieldToString

// Constructor should not be called directly, use getOrMakeNewReduceDecl
case class CrimpDecl private(domainKey: String, crimpType: (Type, Type, Type), fieldName: String)(val pos : Position = NoPosition)
  extends ExtensionMember
{
  def key: String = tupleFieldToString(crimpType, fieldName)
  def hasID: Boolean = if (domainKey == DomainsGenerator.crimpDKeyM) true else
    if (domainKey == DomainsGenerator.crimpDKeyS) false else
      throw new Exception("Reduce domain has unknown key " + domainKey)

  override def name: String = key
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(key)

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = Seq()

  val outType: Type = crimpType._3

  def crimpDType(input: Program): DomainType = {
    val crimpDomain = input.findDomain(domainKey)
    val typeVars = crimpDomain.typVars
    if (typeVars.length != 3) {
      throw new Exception("Reduce domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> crimpType._1,
      typeVars(1) -> crimpType._2,
      typeVars(2) -> crimpType._3
    )
    DomainType.apply(crimpDomain, typeVarMap)
  }

  def crimpDRecvType(input: Program): DomainType = {
    val recvDomain = input.findDomain(DomainsGenerator.recDKey)
    val typeVars = recvDomain.typVars
    if (typeVars.length != 1) {
      throw new Exception("Receiver domain must have 1 type variable")
    }
    val typeVarMap = Map(
      typeVars.head -> crimpType._1,
    )
    DomainType.apply(recvDomain, typeVarMap)
  }

  def findFieldInProgram(p: Program): Field = {
    p.findField(fieldName)
  }
}


object CrimpDecl {

  private val crimpDecls: scala.collection.mutable.Map[String, CrimpDecl] = scala.collection.mutable.Map()

  private var uniqueFieldInt = 0

  private val fieldIDMap: scala.collection.mutable.Map[String, Int] = scala.collection.mutable.Map()

  private def getOrMakeNewReduceDecl(domainKey: String, crimpType: (Type, Type, Type), fieldID: String): CrimpDecl = {
    val key = tupleFieldToString(crimpType, fieldID)
    addFieldtoMap(fieldID)
    crimpDecls.getOrElseUpdate(key, new CrimpDecl(domainKey, crimpType, fieldID)(NoPosition))
  }

  def apply(domainKey: String, crimpType: (Type, Type, Type), fieldID: String): CrimpDecl = {
    getOrMakeNewReduceDecl(domainKey, crimpType, fieldID)
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
