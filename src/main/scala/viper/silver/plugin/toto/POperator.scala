package viper.silver.plugin.toto

import viper.silver.ast.{AnonymousDomainAxiom, Domain, DomainFunc, DomainFuncApp, DomainType, EqCmp, Exp, Forall, LocalVar, Member, NoTrafos, Position, Trigger}
import viper.silver.parser.{PExp, _}

case class POperator(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], opUnit: PExp, body : PFunInline)
                    (val pos: (Position, Position))
  extends PExtender with PAnyFunction with PCompComponentDecl {

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
    t.getMembers()(genDomainName) = dd
    dd

  }



  def getOperUnitAxiom(t: Translator): AnonymousDomainAxiom = {
    val getUnitFunc = t.getMembers()(DomainsGenerator.opUnitKey).asInstanceOf[DomainFunc]
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
