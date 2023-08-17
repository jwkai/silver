package viper.silver.plugin.toto

import viper.silver.ast.Position
import viper.silver.parser.{NameAnalyser, PExp, PExtender, PFormalArgDecl, PIntLit, PNode, PType, PTypeVar, TypeChecker, TypeHelper}

case class PFunInline(args: Seq[PFormalArgDecl], body: PExp)
                     (val pos : (Position, Position)) extends PExtender {


  override def getSubnodes(): Seq[PNode] = args ++ Seq(body)

  def typecheckReceiver(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // this calls t.checkTopTyped, which will call checkInternal, which calls the above typecheck
    if (args.length != 1) {
      return Some(Seq("Receiver body should have exactly one argument."))
    }
    args.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, Some(TypeHelper.Ref))
    None
  }


}
