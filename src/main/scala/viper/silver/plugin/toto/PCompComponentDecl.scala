package viper.silver.plugin.toto

import viper.silver.ast._
import viper.silver.ast.utility.Triggers
import viper.silver.parser._

// Defines a component declaration. This is a PExtender node (extended as a plugin) and acts as a Function declaration,
// hence the PAnyFunction.
trait PCompComponentDecl extends PExtender with PAnyFunction {

  var typToInfer: PType = null;
  override def resultType: PType = typToInfer;
  override def formalArgs: Seq[PFormalArgDecl]
  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)
  override def annotations: Seq[(String, Seq[String])] = Seq()

  val componentName: String


  def genDomainName: String = "___" + idndef.name + "_" + componentName + "_Domain"
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
    val funct = DomainFunc(idndef.name, formalArgs.map(f => t.liftAnyArgDecl(f)), t.ttyp(resultType), false, None)(
      pos = t.liftPos(this), info = t.toInfo(this.annotations, this), domain.name)
    val posInfoError = (t.liftPos(this), t.toInfo(this.annotations, this), NoTrafos)

    // ex. receiver(a)
    // Note: typVar can be empty here because user-defined comprehension components are not generic.
    // i.e. Its always Receiver[Int], never Receiver[A]
    val funcApp = (DomainFuncApp.apply(funct,
      formalArgs.map(a =>(LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError)),
      typVarMap = Map.empty) _).tupled(posInfoError)

    // ex. i or could be i1 i2 for opApply
    val iteratorVar = body.args.map(a => (LocalVar(a.idndef.name, t.ttyp(a.typ)) _).tupled(posInfoError))

    // ex. eval(receiver(a),i)
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
        // This is for set contains, for filter definition axiom.i.e. i in filter(a,b)
        (AnySetContains(iteratorVar.head , funcApp)_).tupled(posInfoError)
    }

    // ex. loc(a,i)
    val rhs = t.exp(body.body)

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
