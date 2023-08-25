package viper.silver.plugin.toto

import viper.silver.ast.{AnonymousDomainAxiom, AnySetContains, BuiltInType, Domain, DomainFunc, DomainFuncApp, DomainType, EqCmp, Exp, ExtensionType, Forall, GenericType, LocalVar, Member, NoTrafos, Position, TypeVar}
import viper.silver.parser.{PAnyFunction, PBinExp, PExtender, PFormalArgDecl, PIdnDef, PNode, PType, Translator}

trait PCompComponentDecl extends PExtender with PAnyFunction {

  var typToInfer: PType = null;
  override def resultType(): PType = typToInfer;
  override def formalArgs: Seq[PFormalArgDecl]
  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)
  override def annotations: Seq[(String, Seq[String])] = Seq()


  def genDomainName: String = "___" + idndef.name + "D"
  def body: PFunInline

  //  def pViperTranslation(posTuple: (Position, Position)): PBinExp

//  def pos: (Position, Position)

  override def translateMemberSignature(t: Translator): Member = {
    //    val pospos: Position = PDomain(null, null, null, null, null)(null, null)
    Domain(name = genDomainName, functions = Seq(), axioms = Seq())(
      pos = t.liftPos(this), info = t.toInfo(this.annotations, this)
    )
  }


  def getEvalFuncAxiom(domain: Domain, evalFuncOpt: Option[DomainFunc],
                   t: Translator): (DomainFunc,AnonymousDomainAxiom) = {
    val funct = DomainFunc(idndef.name, formalArgs.map(f => t.liftAnyArgDecl(f)), t.ttyp(resultType()), false, None)(
      pos = t.liftPos(this), info = t.toInfo(this.annotations, this), domain.name)
    val posInfoError = (t.liftPos(this), t.toInfo(this.annotations, this), NoTrafos)

    // receiver(a)
    val funcApp = (DomainFuncApp.apply(funct,
      formalArgs.map(a =>(LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError)),
      typVarMap = Map.empty) _).tupled(posInfoError)

    // i
    val iteratorVar = body.args.map(a => (LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError))

    // eval(receiver(a),i)
    val evalApp : Exp = evalFuncOpt match {
      case Some(evalFunc) => {
        val evalTypMap = funct.typ match {
          case gt: DomainType =>
            gt.typVarsMap
          case _ =>
            throw new Exception(s"Function ${funct} should be a generic/domain type.")

        }
        (DomainFuncApp.apply(evalFunc, Seq(funcApp) ++ iteratorVar,
          typVarMap = evalTypMap) _).tupled(posInfoError)
      }
      case None =>
        (AnySetContains(iteratorVar.head , funcApp)_).tupled(posInfoError)
    }
//    val evalReceiverApp = evalReceiverAppDummy.copy()(
//      evalReceiverAppDummy.pos,evalReceiverAppDummy.info,
//    )
    // loc(a,i)
    val rhs = t.exp(body.body)
    val equal = (EqCmp(evalApp, rhs)_).tupled(posInfoError)

    // Todo: make triggers
    val triggers = Seq()

    // all Vars
    val allVarsForall = (this.formalArgs ++ body.args).map(a => t.liftArgDecl(a))
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



}
