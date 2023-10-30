package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser._

case class PFilter(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: PFunInline)
                  (val pos: (Position, Position))
  extends PExtender with PAnyFunction with PCompComponentDecl {

  override val componentName: String = "Filter"


  //  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)

//  var typToInfer: PType = null;
//  override def resultType(): PType = typToInfer;

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach(a => t.check(a.typ))
      body.typecheckFilter(t, n) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeSetType(body.args(0).typ)
      }
    }
    None
  }

//  def pViperTranslation(posTuple: (Position, Position)): PBinExp = {
//    val elem = PIdnUse(body.args(0).idndef.name)(posTuple)
//    val set = PCall(PIdnUse(idndef.name)(posTuple),
//      formalArgs.map(a => PIdnUse(a.idndef.name)(posTuple)))(posTuple)
//
//    val lhs = PBinExp(elem, "in", set)(posTuple)
//    val rhs = body.body
//    PBinExp(lhs, "==", rhs)(posTuple)
//  }

  override def translateMember(t: Translator): Member = {
    translateMemberWithName(t, None)
  }

}
