package viper.silver.plugin.crimp.parser

import viper.silver.ast._
import viper.silver.parser.PDelimited.Comma
import viper.silver.parser.PSym.{Colon, ColonColon}
import viper.silver.parser.TypeHelper.Ref
import viper.silver.parser.{PFormalArgDecl, PGlobalCallableNamedArgs, Translator, _}
import viper.silver.plugin.crimp.util.AxiomHelper
import viper.silver.plugin.crimp.{CrimpPlugin, DomainsGenerator, ReduceErrors, ReduceReasons}
import viper.silver.verifier.errors.AssertFailed

case object PFunInlineKeyword extends PKw("fun") with PKeywordLang
case object PFilterKeyword extends PKw("filter") with PKeywordLang with PKw.AnySpec
case object POperatorKeyword extends PKw("operator") with PKeywordLang with PKw.AnySpec
case object PMappingKeyword extends PKw("mapping") with PKeywordLang with PKw.AnySpec
case object PReceiverKeyword extends PKw("receiver") with PKeywordLang with PKw.AnySpec

case class PFunInline(keyword: PReserved[PFunInlineKeyword.type],
                      args: PDelimited.Comma[PSym.Paren, PFormalArgDecl],
                      c: Colon,
                      returnType: PType,
                      cc: ColonColon,
                      body: PExp)
                     (val pos : (Position, Position)) extends PExtender {

  override def subnodes: Iterator[PNode] = getArgs.iterator ++ Iterator(body)

  def getArgs: Seq[PFormalArgDecl] = this.args.inner.toSeq
  //  var resultType: PType = resultType

  def typecheckReceiver(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // this calls t.checkTopTyped, which will call checkInternal, which calls the above typecheck
    if (this.getArgs.length != 1) {
      return Some(Seq("Receiver body should have exactly one argument."))
    }
    this.getArgs.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, Some(TypeHelper.Ref))
    None
  }

  def typecheckOp(t: TypeChecker, n: NameAnalyser, expected: Option[PType]): Option[Seq[String]] = {
    if (this.getArgs.length != 2) {
      return Some(Seq("Operator body should have exactly two arguments."))
    }
    this.getArgs.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, expected)
    None
  }

  def typecheckFilter(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    if (this.getArgs.length != 1) {
      return Some(Seq("Filter body should have exactly one argument."))
    }
    this.getArgs.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, Some(TypeHelper.Bool))
    None
  }

  def typecheckMapping(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    if (this.getArgs.length != 1) {
      return Some(Seq("Mapping body should have exactly one argument."))
    }
    this.getArgs.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, None)
    None
  }
}

// Defines a component declaration. This is a PExtender node (extended as a plugin) and acts as a Function declaration,
// hence the PAnyFunction.
trait PCrimpComponent extends PExtender with PNoSpecsFunction with PSingleMember with PGlobalCallableNamedArgs {

  var typToInfer: PType = null
  override def resultType: PType = typToInfer
  override def body: Some[PFunInline]

  val componentName: String
  def genDomainName: String = "___" + idndef.name + "_" + componentName + "_Domain"

  override def translateMemberSignature(t: Translator): Member = {
    //    val pospos: Position = PDomain(null, null, null, null, null)(null, null)
    Domain(name = genDomainName, functions = Seq(), axioms = Seq())(
      pos = t.liftPos(this), info = Translator.toInfo(this.annotations, this)
    )
  }

  def getEvalFuncAxiom(domain: Domain, evalFuncOpt: Option[DomainFunc],
                       t: Translator): (DomainFunc,AnonymousDomainAxiom) = {

    val funct = DomainFunc(idndef.name, formalArgs.map(f => t.liftAnyArgDecl(f)), t.ttyp(resultType), unique = false, None)(
      pos = t.liftPos(this), info = Translator.toInfo(this.annotations, this), domain.name)
    val posInfoError = (t.liftPos(this), Translator.toInfo(this.annotations, this), NoTrafos)

    // ex. receiver(a)
    // Note: typVar can be empty here because user-defined comprehension components are not generic.
    // i.e. Its always Receiver[Int] defined in a domain without typeVars, never Receiver[A].
    val funcApp = (DomainFuncApp.apply(funct,
      formalArgs.map(a =>(LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError)),
      typVarMap = Map.empty) _).tupled(posInfoError)

    // ex. i or could be i1 i2 for opApply
    val iteratorVar = body.get.getArgs.map(a => (LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError))

    // ex. eval(receiver(a),i)
    val evalApp : Exp = evalFuncOpt match {
      case Some(evalFunc) =>
        val evalTypMap = funct.typ match {
          case gt: DomainType =>
            gt.typVarsMap
          case _ =>
            throw new Exception(s"Function $funct should be a generic/domain type.")

        }
        (DomainFuncApp.apply(evalFunc, Seq(funcApp) ++ iteratorVar,
          typVarMap = evalTypMap) _).tupled(posInfoError)
      case None =>
        // This is for set contains, for filter definition axiom.i.e. i in filter(a,b)
        (AnySetContains(iteratorVar.head, funcApp)_).tupled(posInfoError)
    }

    // ex. loc(a,i)
    val rhs = t.exp(body.get.body)

    // ex. eval(receiver(a),i) == loc(a,i)
    val equal = (EqCmp(evalApp, rhs)_).tupled(posInfoError)

    // Todo: make triggers
    var triggers = Seq(Trigger(Seq(evalApp))())

    // If the rhs is a possible trigger, add it to the triggers seq. Useful for the `loc(a,i)` receiver case
    rhs match {
      case _: PossibleTrigger =>
        triggers :+= Trigger(Seq(rhs))()
      case _ => ()
    }

    // all Vars. ex. a and i
    val allVarsForall = (this.formalArgs ++ body.get.getArgs).map(a => t.liftArgDecl(a))
    val forall = (Forall(allVarsForall, triggers, equal)_).tupled(posInfoError)
    val axiom = AnonymousDomainAxiom(forall)(domainName = domain.name)
    (funct, axiom)
  }

  def translateMemberWithName(t: Translator, evalName: Option[String]): Member = {
    // Gets the dummy domain
    val d = t.getMembers()(genDomainName).asInstanceOf[Domain]
    // Gets the evalRec function
    val evalFuncOpt = evalName.map(f => t.getMembers()(f).asInstanceOf[DomainFunc])
    val (funct, axiom) = getEvalFuncAxiom(d, evalFuncOpt, t)
    val dd = d.copy(
      functions = d.functions :+ funct,
      axioms = d.axioms :+ axiom
    )(d.pos, d.info, d.errT)
    t.getMembers()(genDomainName) = dd
    t.getMembers().put(funct.name, funct)
    dd
  }

  override def annotations: Seq[PAnnotation] = Seq()

  override def c: Colon = PReserved.implied(PSym.Colon)

  override def args: Comma[PSym.Paren, PFormalArgDecl] = PDelimited.impliedParenComma(formalArgs)

  //  override def keyword: PReserved[PKeywordLang] = super.keyword

}

case class PFilter(keyword: PReserved[PFilterKeyword.type], idndef: PIdnDef, override val args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], body: Some[PFunInline])(val pos: (Position, Position))
  extends PExtender with PCrimpComponent {

  override val componentName: String = "Filter"

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach( a => t.check(a.typ))
      val s = body.get.typecheckFilter(t, n)
      s match {
        case out @ Some(_) => return out
        case None => this.typToInfer = CrimpPlugin.makeSetType(body.get.getArgs.head.typ)
      }
    }
    None
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, None)
  }
}

case class POperator(keyword: PReserved[POperatorKeyword.type], idndef: PIdnDef, override val args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], body: Some[PFunInline], returnType: PType, opUnit: Option[PExp])(val pos: (Position, Position))
  extends PExtender with PSingleMember with PCrimpComponent {
  override val componentName: String = "Operator"
  var sourcePos : Position = null
  var helper : AxiomHelper = null

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this){
      formalArgs.foreach(a => t.check(a.typ))
      opUnit match {
        case None =>
          body.get.typecheckOp(t, n, None) match {
            case out@Some(_) => return out
            case None => typToInfer = CrimpPlugin.makeDomainType(DomainsGenerator.opDKey, Seq(returnType))
          }
        case Some(opExp) =>
          t.checkTopTyped(opExp, None)
          body.get.typecheckOp(t, n, Some(opExp.typ)) match {
            case out@Some(_) => return out
            case None => typToInfer = CrimpPlugin.makeDomainType(DomainsGenerator.opDKey, Seq(returnType))
          }
      }
    }
    None
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, Some(DomainsGenerator.opApplyKey))
    // Gets the dummy domain
    val d = t.getMembers()(genDomainName).asInstanceOf[Domain]
    val dd = opUnit match {
      case None => d
      case Some(opExp) =>
        // Gets the evalRec function
        val axiom = getOperUnitAxiom(t, opExp)
        d.copy(
          functions = d.functions,
          axioms = d.axioms :+ axiom
        )(d.pos, d.info, d.errT)
    }
    sourcePos = t.liftPos(this)
    t.getMembers()(genDomainName) = dd
    dd
  }

  def genOpUnitAssert(opExp: DomainFuncApp,
                      opTypeVarMap: Map[TypeVar, Type],
                      input: LocalVarDecl,
                      outerArgs: Seq[LocalVarDecl]): Seq[Stmt] = {
    opUnit match {
      case None => Seq()
      case Some(_) =>     // Identity check
        val opUnitExp = helper.applyDomainFunc(
          DomainsGenerator.opIdenKey, Seq(opExp), opTypeVarMap)
        val opAppliedUnit = helper.applyDomainFunc(
          DomainsGenerator.opApplyKey, Seq(opExp, input.localVar, opUnitExp), opTypeVarMap)
        val dummyTrigger2 = helper.applyDomainFunc(
          "_noTrigOp", Seq(opAppliedUnit), opTypeVarMap)
        val forallIden = Forall(
          outerArgs ++ Seq(input),
          Seq(Trigger(Seq(dummyTrigger2))()),
          EqCmp(opAppliedUnit, input.localVar)())()

        val errIden = ErrTrafo({
          case AssertFailed(offendingNode, _, cached) =>
            val reason = ReduceReasons.IncorrectIdentity(offendingNode, this)
            ReduceErrors.OpWellDefinednessError(offendingNode, this, reason, cached)
          //      case ExhaleFailed(offendingNode, _, cached) => {
          //        val reason = FoldReasons.IncorrectIdentity(offendingNode, this)
          //        FoldErrors.OpWellDefinednessError(offendingNode, this, reason, cached)
          //      }
        })
        Seq(Assert(forallIden)(errT = errIden))
    }
  }

  def getOperUnitAxiom(t: Translator, opExp: PExp): AnonymousDomainAxiom = {
    val getUnitFunc = t.getMembers()(DomainsGenerator.opIdenKey).asInstanceOf[DomainFunc]
    val operFunc = t.getMembers()(idndef.name).asInstanceOf[DomainFunc]
    val posInfoError = (t.liftPos(this), Translator.toInfo(this.annotations, this), NoTrafos)

    val funcApp = (DomainFuncApp.apply(operFunc,
      formalArgs.map(a => (LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError)),
      typVarMap = Map.empty) _).tupled(posInfoError)

    val evalTypMap = operFunc.typ match {
      case gt: DomainType =>
        gt.typVarsMap
      case _ =>
        throw new Exception(s"Function $operFunc should be a generic/domain type.")
    }

    val getUnitApp = (DomainFuncApp.apply(getUnitFunc, Seq(funcApp),
      typVarMap = evalTypMap) _).tupled(posInfoError)

    val rhs = t.exp(opExp)
    val equal = (EqCmp(getUnitApp, rhs)_).tupled(posInfoError)

    val triggers = Seq(Trigger(Seq(getUnitApp))())

    // all Vars
    val allVarsForall = this.formalArgs.map(a => t.liftArgDecl(a))
    var forall : Exp = null
    if (allVarsForall.isEmpty) {
      forall = equal
    } else {
      forall = (Forall(allVarsForall, triggers, equal) _).tupled(posInfoError)
    }
    val axiom = AnonymousDomainAxiom(forall)(domainName = genDomainName)
    axiom
  }

  def generatedOpWelldefinednessCheck(program: Program): Method = {
    helper = new AxiomHelper(program, false)
    // Find the domain function of the operator
    val domainFuncAST = program.findDomainFunction(idndef.name)

    // Operator domain type var map.
    val opTypeVarMap = domainFuncAST.typ.asInstanceOf[DomainType].typVarsMap

    // input type. So if Operator[Int], we want Int
    val inputType = opTypeVarMap.values.head

    // Outer args. So if add(i), we want i
    val opOuterArgs : Seq[LocalVarDecl] =
      domainFuncAST.formalArgs.flatMap{
        case lv: LocalVarDecl => Seq(lv)
        case _ => Seq()
      }
    val input1 = LocalVarDecl("_i1", inputType)()
    val input2 = LocalVarDecl("_i2", inputType)()

    // Add(i)
    val opExp = DomainFuncApp(domainFuncAST, opOuterArgs.map(lv => lv.localVar),
      typVarMap = opTypeVarMap)()
    // opApply(add(i),i1,i2)
    val opAppliedi1i2 = helper.applyDomainFunc(
      DomainsGenerator.opApplyKey, Seq(opExp, input1.localVar, input2.localVar), opTypeVarMap)
    // opApply(add(i),i2,i1)`
    val opAppliedi2i1 = helper.applyDomainFunc(
      DomainsGenerator.opApplyKey, Seq(opExp, input2.localVar, input1.localVar), opTypeVarMap)
    // Communtativity + assertion
    val dummyTrigger0 = helper.applyDomainFunc(
      "_noTrigOp",Seq(opAppliedi1i2), opTypeVarMap)
    val forallComm = Forall(
      opOuterArgs ++ Seq(input1, input2),
      Seq(Trigger(Seq(dummyTrigger0))()),
      EqCmp(opAppliedi1i2, opAppliedi2i1)())()

    val errComm = ErrTrafo({
      case AssertFailed(offendingNode, _, cached) =>
        val reason = ReduceReasons.NotCommutative(offendingNode, this)
        ReduceErrors.OpWellDefinednessError(offendingNode, this, reason, cached)
    })

    val assert1 = Assert(forallComm)(errT = errComm)

    // 3rd var for associativity check
    val input3 = LocalVarDecl("_i3", inputType)()
    val opAppliedi2i3 = helper.applyDomainFunc(
      DomainsGenerator.opApplyKey, Seq(opExp, input2.localVar, input3.localVar), opTypeVarMap)
    val opAppliedAssocL = helper.applyDomainFunc(
      DomainsGenerator.opApplyKey, Seq(opExp, opAppliedi1i2, input3.localVar), opTypeVarMap)
    val opAppliedAssocR = helper.applyDomainFunc(
      DomainsGenerator.opApplyKey, Seq(opExp, input1.localVar, opAppliedi2i3), opTypeVarMap)
    val dummyTrigger1 = helper.applyDomainFunc(
      "_noTrigOp",Seq(opAppliedAssocL), opTypeVarMap)
    val forallAssoc = Forall(
      opOuterArgs ++ Seq(input1, input2, input3),
      Seq(Trigger(Seq(dummyTrigger1))()),
      EqCmp(opAppliedAssocL, opAppliedAssocR)())()

    val errAssoc = ErrTrafo({
      case AssertFailed(offendingNode, _, cached) =>
        val reason = ReduceReasons.NotAssociative(offendingNode, this)
        ReduceErrors.OpWellDefinednessError(offendingNode, this, reason, cached)
    })
    val assert2 = Assert(forallAssoc)(errT = errAssoc)

    val assert3 = genOpUnitAssert(opExp, opTypeVarMap, input1, opOuterArgs)

    val asserts = Seq(assert1, assert2) ++ assert3

    Method("operator_" + this.idndef.name + "_welldef_check", Seq(), Seq(),Seq(),Seq(),
      Some(Seqn(asserts,Seq())()))()
  }
}

case class PMapping(keyword: PReserved[PMappingKeyword.type], idndef: PIdnDef, override val args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], body: Some[PFunInline], returnType: PType)(val pos: (Position, Position))
  extends PExtender with PCrimpComponent {

  override val componentName: String = "Mapping"
  val inputType: PType = body.get.args.inner.toSeq.head.typ

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach( a => t.check(a.typ))
      body.get.typecheckMapping(t, n)  match {
        case out @ Some(_) => return out
        case None => typToInfer = CrimpPlugin.makeDomainType(DomainsGenerator.mapDKey,
          Seq(body.get.getArgs.head.typ, returnType))
      }
    }
    None
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, Some(DomainsGenerator.mapApplyKey))
  }
}

case class PReceiver(keyword: PReserved[PReceiverKeyword.type], idndef: PIdnDef, override val args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], body: Some[PFunInline])(val pos: (Position, Position))
  extends PExtender with PCrimpComponent {

  val returnType: PType = Ref
  val indexType: PType = body.get.args.inner.toSeq.head.typ
  override val componentName: String = "Receiver"

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach( a => t.check(a.typ))
      body.get.typecheckReceiver(t, n) match {
        case out @ Some(_) => return out
        case None => typToInfer = CrimpPlugin.makeDomainType(DomainsGenerator.recDKey,
          Seq(body.get.getArgs.head.typ))
      }
    }
    None
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // There is no expected type. This is a declaration.
    typecheck(t, n)
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, Some(DomainsGenerator.recApplyKey))
  }
}