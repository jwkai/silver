package viper.silver.plugin.toto

import viper.silver.ast.{AnonymousDomainAxiom, AnyLocalVarDecl, Assert, Domain, DomainFunc, DomainFuncApp, DomainType, EqCmp, ErrTrafo, Exp, Forall, LocalVar, LocalVarDecl, Member, Method, NoTrafos, Position, Program, Seqn, Trigger}
import viper.silver.parser.{PExp, _}
import viper.silver.plugin.toto.util.AxiomHelper
import viper.silver.verifier.errors.AssertFailed

case class POperator(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], opUnit: PExp, body : PFunInline)
                    (val pos: (Position, Position))
  extends PExtender with PAnyFunction with PCompComponentDecl {

  override val componentName: String = "Operator"
  var sourcePos : Position = null;

//  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(opUnit, body)
//
//  var typToInfer: PType = null;
//
//  override def resultType(): PType = typToInfer;


  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this){
      formalArgs.foreach(a => t.check(a.typ))
      t.checkTopTyped(opUnit, None)
      body.typecheckOp(t, n, opUnit.typ) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeDomainType(DomainsGenerator.opDKey, Seq(opUnit.typ))
      }
    }
    None
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, Some(DomainsGenerator.opApplyKey))
    // Gets the dummy domain
    val d = t.getMembers()(genDomainName).asInstanceOf[Domain]
    // Gets the evalRec function
    val axiom = getOperUnitAxiom(t)
    val dd = d.copy(
      functions = d.functions,
      axioms = d.axioms :+ axiom
    )(d.pos, d.info, d.errT)
    sourcePos = t.liftPos(this)
    t.getMembers()(genDomainName) = dd
    dd

  }


  def generatedOpWelldefinednessCheck(program: Program): Method = {
    val helper = new AxiomHelper(program)
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
      case AssertFailed(offendingNode, _, cached) => {
        val reason = FoldReasons.NotCommutative(offendingNode, this)
        FoldErrors.OpWellDefinednessError(offendingNode, this, reason, cached)
      }
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
      case AssertFailed(offendingNode, _, cached) => {
        val reason = FoldReasons.NotAssociative(offendingNode, this)
        FoldErrors.OpWellDefinednessError(offendingNode, this, reason, cached)
      }
    })
    val assert2 = Assert(forallAssoc)(errT = errAssoc)

    // Identity check
    val opUnit = helper.applyDomainFunc(
      DomainsGenerator.opIdenKey, Seq(opExp), opTypeVarMap)
    val opAppliedUnit = helper.applyDomainFunc(
      DomainsGenerator.opApplyKey, Seq(opExp, input1.localVar, opUnit), opTypeVarMap)
    val dummyTrigger2 = helper.applyDomainFunc(
      "_noTrigOp",Seq(opAppliedUnit), opTypeVarMap)
    val forallIden = Forall(
      opOuterArgs ++ Seq(input1),
      Seq(Trigger(Seq(dummyTrigger2))()),
      EqCmp(opAppliedUnit, input1.localVar)())()

    val errIden = ErrTrafo({
      case AssertFailed(offendingNode, _, cached) => {
        val reason = FoldReasons.IncorrectIdentity(offendingNode, this)
        FoldErrors.OpWellDefinednessError(offendingNode, this, reason, cached)
      }
    })
    val assert3 = Assert(forallIden)(errT = errIden)

    Method("operator_" + this.idndef.name + "_welldef_check", Seq(), Seq(),Seq(),Seq(),
      Some(Seqn(Seq(assert1, assert2, assert3),Seq())()))()
  }



  def getOperUnitAxiom(t: Translator): AnonymousDomainAxiom = {
    val getUnitFunc = t.getMembers()(DomainsGenerator.opIdenKey).asInstanceOf[DomainFunc]
    val operFunc = t.getMembers()(idndef.name).asInstanceOf[DomainFunc]
    val posInfoError = (t.liftPos(this), t.toInfo(this.annotations, this), NoTrafos)

    val funcApp = (DomainFuncApp.apply(operFunc,
      formalArgs.map(a => (LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError)),
      typVarMap = Map.empty) _).tupled(posInfoError)

    val evalTypMap = operFunc.typ match {
      case gt: DomainType =>
        gt.typVarsMap
      case _ =>
        throw new Exception(s"Function ${operFunc} should be a generic/domain type.")
    }

    val getUnitApp = (DomainFuncApp.apply(getUnitFunc, Seq(funcApp),
      typVarMap = evalTypMap) _).tupled(posInfoError)

    val rhs = t.exp(opUnit)
    val equal = (EqCmp(getUnitApp, rhs)_).tupled(posInfoError)

    val triggers = Seq(Trigger(Seq(getUnitApp))())

    // all Vars
    val allVarsForall = (this.formalArgs).map(a => t.liftArgDecl(a))
    var forall : Exp = null
    if (allVarsForall.isEmpty) {
      forall = equal
    } else {
      forall = (Forall(allVarsForall, triggers, equal) _).tupled(posInfoError)
    }
    val axiom = AnonymousDomainAxiom(forall)(domainName = genDomainName)
    axiom
  }












}
