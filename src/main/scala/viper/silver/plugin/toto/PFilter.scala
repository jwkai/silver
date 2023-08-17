package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser._

case class PFilter(idndef: PIdnDef)
                  (val pos: (Position, Position)) extends PExtender with PSingleMember {
  override val getSubnodes: Seq[PNode] = Seq(idndef)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  override def translateMember(t: Translator): Member = { ???
  }
  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)

  override def annotations: Seq[(String, Seq[String])] = Seq()
}
