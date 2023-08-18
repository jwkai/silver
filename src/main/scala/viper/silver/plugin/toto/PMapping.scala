package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser._

case class PMapping(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], fBody: PFunInline)
                  (val pos: (Position, Position)) extends PExtender with PSingleMember {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(fBody)

  var typ : PType = null;

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach(a => t.check(a.typ))
      fBody.typecheckMapping(t, n) match {
        case out @ Some(_) => return out
        case None => typ = ComprehensionPlugin.makeDomainType(DomainsGenerator.mapDKey,
          Seq(fBody.args(0).typ, fBody.body.typ))
      }
    }
    None
  }

  override def translateMember(t: Translator): Member = { ???
  }
  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)

  override def annotations: Seq[(String, Seq[String])] = Seq()


}
