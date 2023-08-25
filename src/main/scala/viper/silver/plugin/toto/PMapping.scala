package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser._

case class PMapping(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: PFunInline)
                  (val pos: (Position, Position))
  extends PExtender with PAnyFunction with PCompComponentDecl  {

//  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)

//  var typToInfer: PType = null;
//
//  override def resultType(): PType = typToInfer;

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach(a => t.check(a.typ))
      body.typecheckMapping(t, n) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeDomainType(DomainsGenerator.mapDKey,
          Seq(body.args(0).typ, body.body.typ))
      }
    }
    None
  }


  def pViperTranslation(posTuple: (Position, Position)): PBinExp = {
    val args1 = Seq(PCall(PIdnUse(idndef.name)(posTuple),
      formalArgs.map(a => PIdnUse(a.idndef.name)(posTuple)))(posTuple))
    val args2 = body.args.map(a => PIdnUse(a.idndef.name)(posTuple))
    val lhs = PCall(PIdnUse(DomainsGenerator.mapEvalKey)(posTuple), args1 ++ args2)(posTuple)
    val rhs = body.body
    PBinExp(lhs, "==", rhs)(posTuple)
  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, Some(DomainsGenerator.mapEvalKey))
  }


}
