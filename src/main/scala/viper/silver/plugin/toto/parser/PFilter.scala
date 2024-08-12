package viper.silver.plugin.toto.parser

import viper.silver.ast.{Member, Position}
import viper.silver.parser.PSym.Colon
import viper.silver.parser._
import viper.silver.plugin.toto.ComprehensionPlugin

/**
 * Keywords used to define ADT's
 */
case object PFilterKeyword extends PKw("filter") with PKeywordLang

case class PFilter(keyword: PReserved[PFilterKeyword.type], idndef: PIdnDef, override val formalArgs: Seq[PFormalArgDecl], body: Some[PFunInline])
                  (val pos: (Position, Position))
  extends PExtender with PCompComponentDecl {

  override val componentName: String = "Filter"

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach(a => t.check(a.typ))
      body.get.typecheckFilter(t, n) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeSetType(body.get.getArgs.head.typ)
      }
    }
    None
  }

  def pViperTranslation(posTuple: (Position, Position)): PBinExp = {
    val elem = PIdnUseExp(body.get.args.head.idndef.name)(posTuple)
    val set = PCall(PIdnRef(idndef.name)(posTuple),
      PDelimited.impliedParenComma(formalArgs.map(a => PIdnUseExp(a.idndef.name)(posTuple))),
      Some(PReserved.implied(PSym.Colon), TypeHelper.Bool))(posTuple)

    val lhs = PBinExp(elem, PReserved.implied(PKwOp.In), set)(posTuple)
    val rhs = body.get.body
    PBinExp(lhs, PReserved.implied(PSymOp.EqEq), rhs)(posTuple)
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, None)
  }
}
