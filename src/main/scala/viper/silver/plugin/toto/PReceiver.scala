package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser._

case class PReceiver(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body : PFunInline)
                                  (val pos: (Position, Position)) extends PExtender with PSingleMember {


  override def annotations: Seq[(String, Seq[String])] = Seq()

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(body)

  var typ: PType = null;

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      formalArgs.foreach( a => t.check(a.typ))
      body.typecheckReceiver(t, n)
      typ = ComprehensionPlugin.makeDomainType("Receiver", Seq(body.args(0).typ))
    }
    None
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // There is no expected type. This is a declaration.
    typecheck(t, n)
  }


  override def translateMember(t: Translator): Member = { ???
  }
  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)

}
