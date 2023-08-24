package viper.silver.plugin.toto

import viper.silver.ast.NoPosition
import viper.silver.parser._

object DomainsGeneratorPAST {
  final val compDKey = "Comp"
  final val compDTV0 = "A"
  final val compDTV1 = "V"
  final val compDTV2 = "B"


  final val compFKey = "comp"
  final val compEvalKey = "evalComp"
  final val recEvalKey = "eval"
  final val opEvalKey = "oper"
  final val mapEvalKey = "applyMap"

  final val recDKey = "Receiver"
  final val mapDKey = "Mapping"
  final val opDKey = "Operator"

  final val USER_D = "__DummyUserDomain"


  private def makeFilterDef(pf: PFilter): (PDomainFunction, Seq[PAxiom]) = {
    val fd = PDomainFunction(
      idndef = pf.idndef,
      formalArgs = pf.formalArgs,
      resultType = pf.typ,
      unique = false,
      interpretation = None
    )(PIdnUse(USER_D)(noPosTuple))(pf.pos,Seq())



    (fd, Seq())
  }

  private def makeMappingDef(pm: PMapping): (PDomainFunction, Seq[PAxiom]) = {
    val md = PDomainFunction(
      idndef = pm.idndef,
      formalArgs = pm.formalArgs,
      resultType = pm.typ,
      unique = false,
      interpretation = None
    )(PIdnUse(USER_D)(noPosTuple))(pm.pos,Seq())
    (md, Seq())
  }


  private def makeRecDef(pr: PReceiver): (PDomainFunction, Seq[PAxiom]) = {
    val rd = PDomainFunction(
      idndef = pr.idndef,
      formalArgs = pr.formalArgs,
      resultType = pr.typ,
      unique = false,
      interpretation = None
    )(PIdnUse(USER_D)(noPosTuple))(pr.pos, Seq())

    PLogicalVarDecl(pr.formalArgs(0))

    val ad = PAxiom(None,
      PForall(Seq)

    )

    (rd, Seq())
  }

  private




  private def makeOpDef(po: POperator): (PDomainFunction, Seq[PAxiom]) = {
    val od = PDomainFunction(
      idndef = po.idndef,
      formalArgs = po.formalArgs,
      resultType = po.typ,
      unique = false,
      interpretation = None
    )(PIdnUse(USER_D)(noPosTuple))(po.pos, Seq())
    (od, Seq())
  }


  def convertUserDefs(allDefs : Seq[PExtender]) : PDomain = {
    var allDomainF : Seq[PDomainFunction] = Seq()
    var allAxioms : Seq[PAxiom] = Seq()
    allDefs.foreach( d => {
      d match {
        case pf : PFilter =>
          val (fd, ax) = makeFilterDef(pf)
          allDomainF = allDomainF :+ fd
          allAxioms = allAxioms ++ ax
        case pm : PMapping =>
          val (md, ax) = makeMappingDef(pm)
          allDomainF = allDomainF :+ md
          allAxioms = allAxioms ++ ax
        case pr : PReceiver =>
          val (rd, ax) = makeRecDef(pr)
          allDomainF = allDomainF :+ rd
          allAxioms = allAxioms ++ ax
        case po : POperator =>
          val (od, ax) = makeOpDef(po)
          allDomainF = allDomainF :+ od
          allAxioms = allAxioms ++ ax
        case _ =>
      }
    })
    val userDomain = PDomain(
      PIdnDef(USER_D)(noPosTuple),
      Seq(),
      allDomainF,
      allAxioms,
      None)(noPosTuple, Seq())
    userDomain
  }


  private def makeReceiverDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV0)(noPosTuple))(noPosTuple)
    val receiverDomain = PDomain(PIdnDef(recDKey)(noPosTuple),
      Seq(typVar0), Seq(), Seq(), None)(noPosTuple, Seq())
    receiverDomain
  }

  private def makeMappingDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV1)(noPosTuple))(noPosTuple)
    val typVar1 = PTypeVarDecl(PIdnDef(compDTV2)(noPosTuple))(noPosTuple)
    val mappingDomain = PDomain(PIdnDef(mapDKey)(noPosTuple),
      Seq(typVar0, typVar1), Seq(), Seq(), None)(noPosTuple, Seq())
    mappingDomain
  }

  private def makeOperatorDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV2)(noPosTuple))(noPosTuple)
    val operatorDomain = PDomain(PIdnDef(opDKey)(noPosTuple),
      Seq(typVar0), Seq(), Seq(), None)(noPosTuple, Seq())
    operatorDomain
  }


  private def makeCompDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV0)(noPosTuple))(noPosTuple)
    val typVar1 = PTypeVarDecl(PIdnDef(compDTV1)(noPosTuple))(noPosTuple)
    val typVar2 = PTypeVarDecl(PIdnDef(compDTV2)(noPosTuple))(noPosTuple)
    val compDomain = PDomain(PIdnDef(compDKey)(noPosTuple),
      Seq(typVar0, typVar1, typVar2), Seq(), Seq(), None)(noPosTuple, Seq())
    compDomain
  }

  private def makeEvalCompFunction(): PDomainFunction = {
    val compType = PDomainType(PIdnUse(compDKey)(noPosTuple),
      Seq(PTypeVar(compDTV0),
        PTypeVar(compDTV1),
        PTypeVar(compDTV2)))(noPosTuple)
    val snapType = PMapType(PTypeVar(compDTV0),
      PTypeVar(compDTV2))(noPosTuple)
    val compArg = PFormalArgDecl(PIdnDef("c")(noPosTuple), compType)(noPosTuple)
    val snapArg = PFormalArgDecl(PIdnDef("snap")(noPosTuple), snapType)(noPosTuple)
    val evalCompFunc = PDomainFunction(PIdnDef(compEvalKey)(noPosTuple),
      Seq(compArg, snapArg), PTypeVar(compDTV2), unique = false, None)(
      PIdnUse(compDKey)(noPosTuple))(noPosTuple, Seq())
    evalCompFunc

  }

  private def makeCompFunction(): PDomainFunction = {
    val receiverType = PDomainType(PIdnUse(recDKey)(noPosTuple),
      Seq(PTypeVar(compDTV0)))(noPosTuple)
    val mappingType = PDomainType(PIdnUse(mapDKey)(noPosTuple),
      Seq(PTypeVar(compDTV1), PTypeVar(compDTV2)))(noPosTuple)
    val operatorType = PDomainType(PIdnUse(opDKey)(noPosTuple),
      Seq(PTypeVar(compDTV2)))(noPosTuple)
    val unitType = PTypeVar(compDTV2)

    val compFuncArg0 = PFormalArgDecl(PIdnDef("r")(noPosTuple), receiverType)(noPosTuple)
    val compFuncArg1 = PFormalArgDecl(PIdnDef("m")(noPosTuple), mappingType)(noPosTuple)
    val compFuncArg2 = PFormalArgDecl(PIdnDef("op")(noPosTuple), operatorType)(noPosTuple)
    val compFuncArg3 = PFormalArgDecl(PIdnDef("u")(noPosTuple), unitType)(noPosTuple)

    val compFuncOutType = PDomainType(PIdnUse(compDKey)(noPosTuple),
      Seq(PTypeVar(compDTV0),
        PTypeVar(compDTV1),
        PTypeVar(compDTV2)))(noPosTuple)

    val compFunc = PDomainFunction(PIdnDef(compFKey)(noPosTuple),
      Seq(compFuncArg0, compFuncArg1, compFuncArg2, compFuncArg3), compFuncOutType, unique = false, None)(
      PIdnUse(compDKey)(noPosTuple))(noPosTuple, Seq())
    compFunc
  }


  def addCompDomain(input: PProgram): PProgram = {
    // checks and add an Comp domain if doesn't exist
    if (checkCompExists(input)) {
      return input
    }
    input.copy(domains = input.domains :+ makeCompDomain())(input.pos)
  }

  def addCompFunc(input: PProgram, domainName: String = compDKey): PProgram = {
    // checks and add an Comp function if doesn't exist
    if (checkCompFuncExists(input, domainName)) {
      return input
    }
    input.domains.find(d => d.idndef.name == domainName) match {
      case None =>
        throw new Exception("Should not get here.")
      case Some(domain) =>
        val newDomainFuncs = domain.funcs :+ makeCompFunction()
        val newCompDomain = domain.copy(funcs = newDomainFuncs)(domain.pos, domain.annotations)
        val newDomains = input.domains.filter(d => d.idndef.name != domainName) :+ newCompDomain
        input.copy(domains = newDomains)(input.pos)
    }
  }

  def receiverDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val receiverOut =
      s"""domain $recDKey[$compDTV0] {
         |    function $recEvalKey(r:$recDKey[$compDTV0], a:$compDTV0) : Ref
         |    function invers$recEvalKey(rec:$recDKey[$compDTV0], ref:Ref) : $compDTV0
         |    function filterReceiverGood(f: Set[$compDTV0], r: $recDKey[$compDTV0]) : Bool
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    receiverOut
  }

  def mappingDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val mappingOut =
      s"""domain $mapDKey[$compDTV1,$compDTV2] {
         |    function $mapEvalKey(m: $mapDKey[$compDTV1,$compDTV2], val:$compDTV1) : $compDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    mappingOut
  }

  def opDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val opOut =
      s"""domain $opDKey[$compDTV2] {
         |    function $opEvalKey(op: $opDKey[$compDTV2], val1:$compDTV2, val2:$compDTV2) : $compDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    opOut
  }

  def compDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val compOut =
      s"""domain $compDKey[$compDTV0,$compDTV1,$compDTV2] {
         |    function $compFKey(r:$recDKey[$compDTV0], m: $mapDKey[$compDTV1,$compDTV2],
         |        op: $opDKey[$compDTV2],u: $compDTV2) : $compDKey[$compDTV0,$compDTV1,$compDTV2]
         |    function $compEvalKey(c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |        snap: Map[$compDTV0,$compDTV2]) : $compDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    compOut
  }

  private def checkCompFuncExists(input: PProgram, domainName: String = compDKey): Boolean = {
    input.domains.find(d => d.idndef.name == domainName) match {
      case Some(domain) =>
        domain.funcs.find(f => f.idndef.name == compFKey) match {
          case Some(_) =>
            true
          case None =>
            false
        }
      case None =>
        throw new Exception("Should not get here.")
    }

  }


  private def checkCompExists(input: PProgram): Boolean = {
    input.domains.find(d => d.idndef.name == compDKey) match {
      case Some(value) =>
        val dTypeVars = value.typVars
        if (dTypeVars.length >= 3) {
          throw new Exception("Comp domain should have at least 3 type variables")
        }
        true
      case None =>
        false
    }
  }

  private def noPosTuple = (NoPosition, NoPosition)


}
