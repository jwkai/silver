package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser.{NameAnalyser, PExp, PExtender, PFormalArgDecl, PGlobalDeclaration, PIdnDef, PMember, PNode, Translator, TypeChecker}

case class POperator(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body : PExp)
                    (val pos: (Position, Position)) extends PExtender with PMember with PGlobalDeclaration {
  override val getSubnodes: Seq[PNode] = Seq(idndef)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  override def translateMember(t: Translator): Member = { ???
  }
  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)

}
