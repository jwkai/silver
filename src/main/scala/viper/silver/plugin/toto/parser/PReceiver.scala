package viper.silver.plugin.toto.parser

import viper.silver.ast.{Member, Position}
import viper.silver.parser.PSym.Colon
import viper.silver.parser._
import viper.silver.plugin.toto.{ComprehensionPlugin, DomainsGenerator}

case object PReceiverKeyword extends PKw("receiver") with PKeywordLang

case class PReceiver(keyword: PReserved[PReceiverKeyword.type], idndef: PIdnDef, override val formalArgs: Seq[PFormalArgDecl], body : Some[PFunInline])(val pos: (Position, Position))
  extends PExtender with PSingleMember with PCompComponentDecl {

  override def c: Colon = super.c
  override val componentName: String = "Receiver"

  val myBody: PFunInline = body.get

//  override def annotations: Seq[(String, Seq[String])] = Seq()
//
//  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach( a => t.check(a.typ))
      myBody.typecheckReceiver(t, n) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeDomainType(DomainsGenerator.recDKey,
          Seq(myBody.getArgs.head.typ))
      }
    }
    None
  }

  def pViperTranslation(posTuple: (Position, Position)): PBinExp = {
    val args1 = Seq(PCall(PIdnRef(idndef.name)(posTuple),
      PDelimited.impliedParenComma(formalArgs.map(a => PIdnUseExp(a.idndef.name)(posTuple))),
      Some(PReserved.implied(PSym.Colon), TypeHelper.Ref))(posTuple))
    val args2 = myBody.args.map(a => PIdnUseExp(a.idndef.name)(posTuple))
    val lhs = PCall(PIdnRef(DomainsGenerator.recApplyKey)(posTuple),
      PDelimited.impliedParenComma(args1 ++ args2),
      Some(PReserved.implied(PSym.Colon), TypeHelper.Ref))(posTuple)
    val rhs = myBody.body
    PBinExp(lhs, PReserved[PSymOp.EqEq.type], rhs)(posTuple)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // There is no expected type. This is a declaration.
    typecheck(t, n)
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, Some(DomainsGenerator.recApplyKey))
  }

  // Moved to trait
//  override def translateMemberSignature(t: Translator): Member = {
////    val pospos: Position = PDomain(null, null, null, null, null)(null, null)
//    Domain(name = genDomainName, functions = Seq(), axioms = Seq())(
//      pos = t.liftPos(this), info = t.toInfo(this.annotations, this)
//    )
//  }
}
