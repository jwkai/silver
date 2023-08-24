package viper.silver.plugin.toto

import viper.silver.ast.pretty.Call
import viper.silver.ast.{AnonymousDomainAxiom, Domain, DomainFunc, DomainFuncApp, EqCmp, Forall, LocalVar, Member, Position}
import viper.silver.parser._

case class PReceiver(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body : PFunInline)
                                  (val pos: (Position, Position))
  extends PExtender with PAnyFunction with PCompComponentDecl {


  override def annotations: Seq[(String, Seq[String])] = Seq()

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)


  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach( a => t.check(a.typ))
      body.typecheckReceiver(t, n) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeDomainType(DomainsGenerator.recDKey,
          Seq(body.args(0).typ))
      }
    }
    None
  }

  def pViperTranslation(posTuple: (Position, Position)): PBinExp = {
    val args1 = Seq(PCall(PIdnUse(idndef.name)(posTuple),
      formalArgs.map(a => PIdnUse(a.idndef.name)(posTuple)))(posTuple))
    val args2 = body.args.map(a => PIdnUse(a.idndef.name)(posTuple))
    val lhs = PCall(PIdnUse(DomainsGenerator.recEvalKey)(posTuple), args1 ++ args2)(posTuple)
    val rhs = body.body
    PBinExp(lhs, "==", rhs)(posTuple)
  }


  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // There is no expected type. This is a declaration.
    typecheck(t, n)
  }


  override def translateMember(t: Translator): Member = {
    // Gets the dummy domain
    val d = t.getMembers()(genDomainName).asInstanceOf[Domain]
    // Gets the evalRec function
    val evalFunc = t.getMembers()(DomainsGenerator.recEvalKey).asInstanceOf[DomainFunc]
    val (funct, axiom) = getEvalFuncAxiom(d, evalFunc, t)
    val dd = d.copy(
      functions = d.functions :+ funct,
      axioms = d.axioms :+ axiom
    )(d.pos, d.info, d.errT)
    t.getMembers()(genDomainName) = dd
    dd

  }
//  override def translateMemberSignature(t: Translator): Member = {
////    val pospos: Position = PDomain(null, null, null, null, null)(null, null)
//    Domain(name = genDomainName, functions = Seq(), axioms = Seq())(
//      pos = t.liftPos(this), info = t.toInfo(this.annotations, this)
//    )
//  }



}
