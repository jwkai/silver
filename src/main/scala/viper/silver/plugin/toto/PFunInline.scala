package viper.silver.plugin.toto

import viper.silver.ast.Position
import viper.silver.parser._

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


  def typecheckOp(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    if (args.length != 2) {
      return Some(Seq("Operator body should have exactly two arguments."))
    }
    args.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, Some(expected))
    None
  }

  def typecheckFilter(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    if (args.length != 1) {
      return Some(Seq("Filter body should have exactly one argument."))
    }
    args.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, Some(TypeHelper.Bool))
    None
  }

  def typecheckMapping(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    if (args.length != 1) {
      return Some(Seq("Mapping body should have exactly one argument."))
    }
    args.foreach(a => t.check(a.typ))
    t.checkTopTyped(body, None)
    None
  }


}
