package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser.{PExp, _}

case class POperator(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], opUnit: PExp, opDef : PFunInline)
                    (val pos: (Position, Position))
  extends PExtender with PSingleMember {
  override val getSubnodes: Seq[PNode] = Seq(idndef)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  override def translateMember(t: Translator): Member = { ???
  }
  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)

  override def annotations: Seq[(String, Seq[String])] = Seq()
}
