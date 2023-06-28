package viper.silver.plugin.toto;

import viper.silver.ast.{Exp, Position}
import viper.silver.parser.PExtender
import viper.silver.parser._;

case class PComprehension(op: PExp, unit: PExp, receiver: PExp, filter: PExp)(val pos: (Position, Position)) extends PExtender with PExp {
  override val getSubnodes: Seq[PNode] = Seq(op, unit, receiver, filter)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(op, None)
    None
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(op, None)
    None
  }


  val _typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = _typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution): Unit = ()

  override def translateExp(t: Translator): Exp =
    Comprehension(t.exp(op), t.exp(unit), t.exp(receiver), t.exp(filter))(t.liftPos(this))

}
