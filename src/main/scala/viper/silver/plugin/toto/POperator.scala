package viper.silver.plugin.toto

import viper.silver.ast.{Member, Position}
import viper.silver.parser.{PExp, _}

case class POperator(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], opUnit: PExp, body : PFunInline)
                    (val pos: (Position, Position))
  extends PExtender with PAnyFunction with PCompComponentDecl {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs ++ Seq(opUnit, body)

  var typToInfer: PType = null;

  override def resultType(): PType = typToInfer;


  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this){
      formalArgs.foreach(a => t.check(a.typ))
      t.checkTopTyped(opUnit, None)
      body.typecheckOp(t, n, opUnit.typ) match {
        case out @ Some(_) => return out
        case None => typToInfer = ComprehensionPlugin.makeDomainType(DomainsGenerator.opDKey, Seq(opUnit.typ))
      }
    }
    None
  }

  override def translateMember(t: Translator): Member = { ???
  }
  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)

  override def annotations: Seq[(String, Seq[String])] = Seq()
}
