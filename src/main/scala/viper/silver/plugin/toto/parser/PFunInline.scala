package viper.silver.plugin.toto.parser

import viper.silver.ast.Position
import viper.silver.parser._

case object PFunInlineKeyword extends PKw("fun") with PKeywordLang

case class PFunInline(keyword: PReserved[PFunInlineKeyword.type], args: Seq[PFormalArgDecl], body: PExp)(val pos : (Position, Position)) extends PExtender with PPrettySubnodes {
  
  override def subnodes: Seq[PNode] = getArgs ++ Seq(body)

  def getArgs: Seq[PFormalArgDecl] = args

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