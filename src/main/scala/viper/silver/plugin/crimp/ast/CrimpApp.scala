package viper.silver.plugin.crimp.ast

import viper.silver.ast.pretty.FastPrettyPrinter._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.{Position, _}
import viper.silver.plugin.crimp.DomainsGenerator
import viper.silver.verifier.VerificationResult

case class CrimpApp(reduction: CrimpTriple, filter: Exp, fieldName: String)
                       (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
  extends ExtensionExp {

  var crimpFunctionDeclaration: CrimpDecl = {
    val domainKey = reduction.crimpDKeyName()
    val receiverType = reduction.tripleType
    CrimpDecl(domainKey, receiverType, fieldName)
  }

  var fuelExp: Option[Exp] = None
  var cHeap: Option[CHeap] = None

  def toViper(input: Program): Exp = {
    val crimpEvalFunc = input.findDomainFunction(reduction.crimpEvalFuncName())
    val crimpConstructed = reduction.toViper(input)

    cHeap match {
      case Some(ch) =>
        fuelExp match {
          case Some(fuel) =>
            DomainFuncApp(
              crimpEvalFunc,
              Seq(fuel, ch.toExp, crimpConstructed, filter),
              crimpConstructed.typVarMap
            )(this.pos, this.info, this.errT + NodeTrafo(this))
          case None =>
            throw new Exception("Crimp to Viper undefined with fuel = None")
        }
      case None =>
        throw new Exception("Crimp to Viper undefined with cHeap = None")
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
    text(reduction.crimpConstructKeyName()) <> brackets(show(reduction.op)) <>
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

sealed trait CrimpTriple extends ExtensionExp {
  def receiver: Exp
  def op: Exp
  def mapping: Exp

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("hcrimp") <+>  toParenDoc(op) <+> toParenDoc(receiver)

  override val extensionSubnodes: Seq[Node] = Seq(receiver, mapping, op).flatten

  override def extensionIsPure: Boolean = true

  override def typ: Type = op.typ match {
    case d @ DomainType(DomainsGenerator.opDKey, _) =>
      d.typVarsMap.values.head
    case _ => throw new Exception("Operator must be an operator. Resolving should have failed.")
  }

  val tripleType: (Type, Type, Type)   = {
    val recA = receiver.typ match {
      case d: DomainType if d.domainName == DomainsGenerator.recDKey =>
        d.typVarsMap.values
      case _ => throw new Exception(s"Receiver must be a ${DomainsGenerator.recDKey} type")
    }
    if (recA.size != 1) {
      throw new Exception("Receiver must be a Receiver of 1 variable. Resolving should have failed.")
    }
    val A = recA.head
    val VB = mapping.typ match {
      case d: DomainType if d.domainName == DomainsGenerator.mapDKey =>
        d.typVarsMap.values
      case _ => throw new Exception(s"Mapping must be a ${DomainsGenerator.mapDKey} type. " +
        s"Resolving should have failed.")
    }
    if (VB.size != 2) {
      throw new Exception("Mapping must be a mapping from 2 variables")
    }
    val V = VB.head
    val B = VB.tail.head
    (A, V, B)
  }

  def crimpDKeyName(): String
  def crimpConstructKeyName(): String
  def crimpEvalFuncName(): String

  def toViper(input: Program) : DomainFuncApp = {
    val typeVars = input.findDomain(crimpDKeyName()).typVars
    if (typeVars.length != 3) {
      throw new Exception("Crimp domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> tripleType._1,
      typeVars(1) -> tripleType._2,
      typeVars(2) -> tripleType._3
    )
    val crimpFunc = input.findDomainFunction(crimpConstructKeyName())
    DomainFuncApp.apply(crimpFunc, Seq(receiver, mapping, op), typeVarMap)(pos, info, errT)
  }
  // Does not get used, transform to ordinary Viper before verification
  override def verifyExtExp(): VerificationResult = {
    throw new Exception("Not implemented")
  }
}

object CrimpTriple {
  def apply(receiver: Exp, mapping: Exp, op: Exp, hasID: Boolean)
           (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): CrimpTriple =
    if (hasID) {
      CrimpTripleWithId(receiver, mapping, op)(pos, info, errT)
    } else {
      CrimpTripleWithoutId(receiver, mapping, op)(pos, info, errT)
    }

  def unapply(a: CrimpTriple): Some[(Exp, Exp, Exp)] = Some((a.receiver, a.mapping, a.op))
}

case class CrimpTripleWithId(receiver: Exp, mapping: Exp, op: Exp)
                                 (val pos: Position = NoPosition, val info: Info = NoInfo,
                                  val errT: ErrorTrafo = NoTrafos) extends CrimpTriple {
  override def crimpDKeyName(): String = DomainsGenerator.crimpDKeyM
  override def crimpConstructKeyName(): String = DomainsGenerator.crimpConstructKeyM
  override def crimpEvalFuncName(): String = DomainsGenerator.crimpApplyKeyM
}

case class CrimpTripleWithoutId(receiver: Exp, mapping: Exp, op: Exp)
                                    (val pos: Position = NoPosition, val info: Info = NoInfo,
                                     val errT: ErrorTrafo = NoTrafos) extends CrimpTriple {
  override def crimpDKeyName(): String = DomainsGenerator.crimpDKeyS
  override def crimpConstructKeyName(): String = DomainsGenerator.crimpConstructKeyS
  override def crimpEvalFuncName(): String = DomainsGenerator.crimpApplyKeyS
}