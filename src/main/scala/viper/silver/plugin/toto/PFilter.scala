package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser._

case class PFilter(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: PFunInline)
                  (val pos: (Position, Position)) extends PExtender with PSingleMember {
  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)

  var typ : PType = null;

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach(a => t.check(a.typ))
      body.typecheckFilter(t, n) match {
        case out @ Some(_) => return out
        case None => typ = ComprehensionPlugin.makeSetType(body.args(0).typ)
      }
    }
    None
  }

  override def translateMember(t: Translator): Member = { ???
  }
  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)

  override def annotations: Seq[(String, Seq[String])] = Seq()
}
