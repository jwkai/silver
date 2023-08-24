package viper.silver.plugin.toto

import viper.silver.ast.{AnonymousDomainAxiom, Domain, DomainFunc, DomainFuncApp, EqCmp, Forall, LocalVar, Member, Position}
import viper.silver.parser.{PAnyFunction, PBinExp, PExtender, PFormalArgDecl, PIdnDef, PType, Translator}

trait PCompComponentDecl extends PExtender with PAnyFunction {

  var typToInfer: PType = null;
  override def resultType(): PType = typToInfer;

  def idndef: PIdnDef

  def genDomainName: String = "___" + idndef.name + "D"

  def formalArgs: Seq[PFormalArgDecl]

  def body: PFunInline

  def typ: PType

  def pViperTranslation(posTuple: (Position, Position)): PBinExp

  def pos: (Position, Position)

  override def translateMemberSignature(t: Translator): Member = {
    //    val pospos: Position = PDomain(null, null, null, null, null)(null, null)
    Domain(name = genDomainName, functions = Seq(), axioms = Seq())(
      pos = t.liftPos(this), info = t.toInfo(this.annotations, this)
    )
  }


  def getEvalFuncAxiom(domain: Domain, evalFunc: DomainFunc,
                   t: Translator): (DomainFunc,AnonymousDomainAxiom) = {

    val funct = DomainFunc(idndef.name, formalArgs.map(f => t.liftAnyArgDecl(f)), t.ttyp(resultType()), false, None)(
      pos = t.liftPos(this), info = t.toInfo(this.annotations, this), domain.name)
    // receiver(a)
    val receiverApp = DomainFuncApp.apply(funct,
      formalArgs.map(a => LocalVar(a.idndef.name, t.ttyp(a.typ))()),
      typVarMap = Map.empty)()
    // i
    val iteratorVar = body.args.map(a => LocalVar(a.idndef.name, t.ttyp(a.typ))())
    // eval(receiver(a),i)
    val evalReceiverApp = DomainFuncApp.apply(evalFunc, Seq(receiverApp) ++ iteratorVar,
      typVarMap = Map.empty)()
    // loc(a,i)
    val rhs = t.exp(body.body)
    val equal = EqCmp(evalReceiverApp, rhs)()
    // Todo: make triggers
    val triggers = Seq()
    // all Vars
    val allVarsForall = (this.formalArgs ++ body.args).map(a => t.liftArgDecl(a))
    val forall = Forall(allVarsForall, triggers, equal)()
    val axiom = AnonymousDomainAxiom(forall)(domainName = domain.name)
    (funct, axiom)



  }

}
