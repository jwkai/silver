package viper.silver.plugin.toto

import viper.silver.ast.NoPosition
import viper.silver.parser.PDelimited.impliedBlock
import viper.silver.parser.PGrouped.impliedBrace
import viper.silver.parser._
import viper.silver.plugin.toto.parser.{PCompComponentDecl, PCompOperator, PFilter, PMapping, PReceiver}

// No longer used. Strings instead.
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

  private def makeDef(pc: PCompComponentDecl): (PDomainFunction, Seq[PAxiom]) =
    (PDomainFunction(
      annotations = pc.annotations,
      keyword = PReserved.implied(PKw.FunctionD),
      idndef = pc.idndef,
      args = formalArgsToDomainFunctionArgs(pc.formalArgs),
      c = PReserved.implied(PSym.Colon),
      resultType = pc.typ,
      unique = None,
      interpretation = None
    )(pc.pos), Seq())

  def convertUserDefs(allDefs : Seq[PExtender]) : PDomain = {
    var allDomainF : Seq[PDomainFunction] = Seq()
    var allAxioms : Seq[PAxiom] = Seq()
    allDefs.foreach {
      case pf: PFilter =>
        val (fd, ax) = makeDef(pf)
        allDomainF = allDomainF :+ fd
        allAxioms = allAxioms ++ ax
      case pm: PMapping =>
        val (md, ax) = makeDef(pm)
        allDomainF = allDomainF :+ md
        allAxioms = allAxioms ++ ax
      case pr: PReceiver =>
        val (rd, ax) = makeDef(pr)
        allDomainF = allDomainF :+ rd
        allAxioms = allAxioms ++ ax
      case po: PCompOperator =>
        val (od, ax) = makeDef(po)
        allDomainF = allDomainF :+ od
        allAxioms = allAxioms ++ ax
      case _ =>
    }
    val userDomain = PDomain(
      annotations = Seq(),
      domain = PReserved.implied(PKw.Domain),
      idndef = PIdnDef(USER_D)(noPosTuple),
      typVars = makeBracketedTypes(Seq()),
      interpretations = None,
      members = impliedBrace(
        PDomainMembers(
          impliedBlock(allDomainF).inner,
          impliedBlock(allAxioms).inner
        )(noPosTuple))
    )(noPosTuple)
    userDomain
  }

  private def makeReceiverDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV0)(noPosTuple))(noPosTuple)
    val receiverDomain = makePDomain(recDKey, Seq(typVar0))
    receiverDomain
  }

  private def makeMappingDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV1)(noPosTuple))(noPosTuple)
    val typVar1 = PTypeVarDecl(PIdnDef(compDTV2)(noPosTuple))(noPosTuple)
    val mappingDomain = makePDomain(mapDKey, Seq(typVar0, typVar1))
    mappingDomain
  }

  private def makeOperatorDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV2)(noPosTuple))(noPosTuple)
    val operatorDomain = makePDomain(opDKey, Seq(typVar0))
    operatorDomain
  }

  private def makeCompDomain(): PDomain = {
    val typVar0 = PTypeVarDecl(PIdnDef(compDTV0)(noPosTuple))(noPosTuple)
    val typVar1 = PTypeVarDecl(PIdnDef(compDTV1)(noPosTuple))(noPosTuple)
    val typVar2 = PTypeVarDecl(PIdnDef(compDTV2)(noPosTuple))(noPosTuple)
    val compDomain = makePDomain(compDKey, Seq(typVar0, typVar1, typVar2))
    compDomain
  }

  private def makeEvalCompFunction(): PDomainFunction = {
    val compType = PDomainType(
      PIdnRef(compDKey)(noPosTuple),
      makeBracketedTypes(
        Seq(PTypeVar(compDTV0), PTypeVar(compDTV1), PTypeVar(compDTV2)))
      )(noPosTuple)
    val snapType = TypeHelper.MakeMap(
      PTypeVar(compDTV0),
      PTypeVar(compDTV2)
    )
    val compArg = PFormalArgDecl(PIdnDef("c")(noPosTuple), PReserved.implied(PSym.Colon), compType)(noPosTuple)
    val snapArg = PFormalArgDecl(PIdnDef("snap")(noPosTuple), PReserved.implied(PSym.Colon), snapType)(noPosTuple)
    val evalCompFunc = makePDomainFunction(compEvalKey, Seq(compArg, snapArg), PTypeVar(compDTV2))
    evalCompFunc
  }

  private def makeCompFunction(): PDomainFunction = {
    val receiverType = PDomainType(
      PIdnRef(recDKey)(noPosTuple),
      makeBracketedTypes(Seq(PTypeVar(compDTV0)))
    )(noPosTuple)

    val mappingType = PDomainType(
      PIdnRef(mapDKey)(noPosTuple),
      makeBracketedTypes(Seq(PTypeVar(compDTV1), PTypeVar(compDTV2)))
    )(noPosTuple)

    val operatorType = PDomainType(
      PIdnRef(opDKey)(noPosTuple),
      makeBracketedTypes(Seq(PTypeVar(compDTV2)))
    )(noPosTuple)

    val unitType = PTypeVar(compDTV2)

    val compFuncArg0 = PFormalArgDecl(PIdnDef("r")(noPosTuple), PReserved.implied(PSym.Colon), receiverType)(noPosTuple)
    val compFuncArg1 = PFormalArgDecl(PIdnDef("m")(noPosTuple), PReserved.implied(PSym.Colon), mappingType)(noPosTuple)
    val compFuncArg2 = PFormalArgDecl(PIdnDef("op")(noPosTuple), PReserved.implied(PSym.Colon), operatorType)(noPosTuple)
    val compFuncArg3 = PFormalArgDecl(PIdnDef("u")(noPosTuple), PReserved.implied(PSym.Colon), unitType)(noPosTuple)

    val compFuncOutType = PDomainType(
      PIdnRef(compDKey)(noPosTuple),
      makeBracketedTypes(Seq(PTypeVar(compDTV0), PTypeVar(compDTV1), PTypeVar(compDTV2)))
    )(noPosTuple)

    val compFunc = makePDomainFunction(
      compFKey, Seq(compFuncArg0, compFuncArg1, compFuncArg2, compFuncArg3), compFuncOutType)
    compFunc
  }


  def addCompDomain(input: PProgram): PProgram = {
    // checks and add an Comp domain if doesn't exist
    if (checkCompExists(input)) {
      return input
    }
    input.copy(
      members = input.members :+ makeCompDomain()
    )(input.pos, input.localErrors)
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
        val newDomainFuncs = domain.members.inner.funcs.toSeq :+ makeCompFunction()
        val newCompDomain = domain.copy(members = domain.members.update {
          case p@PDomainMembers(_, axs) => PDomainMembers(impliedBlock(newDomainFuncs).inner, axs)(p.pos)
        })(domain.pos)
        val newDomains = input.domains.filter(d => d.idndef.name != domainName) :+ newCompDomain
        input.copy(
          members = input.members ++ newDomains
        )(input.pos, input.localErrors)
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
        domain.members.inner.funcs.toSeq.find(f => f.idndef.name == compFKey) match {
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
        val dTypeVars = value.typVars.toSeq
        if (dTypeVars.length >= 3) {
          throw new Exception("Comp domain should have at least 3 type variables")
        }
        true
      case None =>
        false
    }
  }

  private def emptyDomainMembers: PGrouped[PSym.Brace, PDomainMembers] =
    impliedBrace(PDomainMembers(PDelimited.empty, PDelimited.empty)(noPosTuple))

  private def formalArgsToDomainFunctionArgs(fas: Seq[PFormalArgDecl]): PDelimited.Comma[PSym.Paren, PDomainFunctionArg] = {
    PDelimited.impliedParenComma(fas map {
      case p@PFormalArgDecl(idndef, c, typ) =>
        PDomainFunctionArg(Some(idndef), Some(c), typ)(p.pos)
    })
  }

  private def makeBracketedTypes[T <: PType](typVars: Seq[T]): Option[PDelimited.Comma[PSym.Bracket, T]] =
    Some(PDelimited.impliedBracketComma(typVars))

  private def makePDomainFunction(name: String, args: Seq[PFormalArgDecl], resultType: PType): PDomainFunction = {
    PDomainFunction(
      annotations = Seq(),
      unique = None,
      keyword = PReserved.implied(PKw.FunctionD),
      idndef = PIdnDef(name)(noPosTuple),
      args = formalArgsToDomainFunctionArgs(args),
      c = PReserved.implied(PSym.Colon),
      resultType = resultType,
      interpretation = None
    )(noPosTuple)
  }

  private def makePDomain(name: String, typVars: Seq[PTypeVarDecl]): PDomain =
    PDomain(
      annotations = Seq(),
      domain = PReserved.implied(PKw.Domain),
      idndef = PIdnDef(name)(noPosTuple),
      typVars = makeBracketedTypes(typVars),
      interpretations = None,
      members = emptyDomainMembers
    )(noPosTuple)

  private def noPosTuple = (NoPosition, NoPosition)
}
