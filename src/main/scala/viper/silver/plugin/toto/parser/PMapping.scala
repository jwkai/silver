package viper.silver.plugin.toto.parser

import viper.silver.ast.{Member, Position}
import viper.silver.parser.PSym.Colon
import viper.silver.parser._
import viper.silver.plugin.toto.{ComprehensionPlugin, DomainsGenerator}

case object PMappingKeyword extends PKw("mapping") with PKeywordLang

case class PMapping(keyword: PReserved[PMappingKeyword.type], idndef: PIdnDef, override val formalArgs: Seq[PFormalArgDecl], body: Some[PFunInline])
                  (val pos: (Position, Position))
  extends PExtender with PSingleMember with PCompComponentDecl  {

  override val componentName: String = "Mapping"

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach(a => t.check(a.typ))
      body.get.typecheckMapping(t, n) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeDomainType(DomainsGenerator.mapDKey,
          Seq(body.get.getArgs.head.typ, body.get.body.typ))
      }
    }
    None
  }

  def pViperTranslation(posTuple: (Position, Position)): PBinExp = {
    val args1 = Seq(PCall(PIdnRef(idndef.name)(posTuple),
      PDelimited.impliedParenComma(formalArgs.map(a => PIdnUseExp(a.idndef.name)(posTuple))),
      Some(PReserved.implied(PSym.Colon), TypeHelper.Ref))(posTuple))
    val args2 = body.get.args.map(a => PIdnUseExp(a.idndef.name)(posTuple))
    val lhs = PCall(PIdnRef(DomainsGenerator.mapApplyKey)(posTuple),
      PDelimited.impliedParenComma(args1 ++ args2),
      Some(PReserved.implied(PSym.Colon), TypeHelper.Ref))(posTuple)
    val rhs = body.get.body
    PBinExp(lhs, PReserved.implied(PSymOp.EqEq), rhs)(posTuple)
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, Some(DomainsGenerator.mapApplyKey))
  }
}
