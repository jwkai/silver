package viper.silver.plugin.toto;

import viper.silver.ast.{Exp, Field, Position}
import viper.silver.parser.PExtender
import viper.silver.parser._

import scala.collection.immutable.{AbstractSeq, LinearSeq}
import scala.xml.NodeSeq;

case class PComprehension(op: PCall, unit: PExp, mappingFieldReceiver: PMappingFieldReceiver, filter: PExp)(val pos: (Position, Position)) extends PExtender with PExp {
  override val getSubnodes: Seq[PNode] = Seq(op, unit, mappingFieldReceiver, filter)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(unit, None)
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

  override def translateExp(t: Translator): Exp = {
    val translatedOp = t.exp(op)
    val translatedUnit = t.exp(unit)
    val translatedFilter = t.exp(filter)
    receiver match {
      case appliedMapping @ PCall(mapping, args, typeAnnotated) =>
        args.head match {
          case PFieldAccess(appliedReceiver, fieldIden) =>
            Comprehension(
              translatedOp,
              translatedUnit,
              Some(t.exp(appliedMapping.copy(args = args.tail)(appliedMapping.pos))),
              t.exp(fieldIden), t.exp(appliedReceiver), translatedFilter)(t.liftPos(this))
        }
      case PFieldAccess(appliedReceiver, fieldIden) =>
        Comprehension(translatedOp, translatedUnit, None,
          t.exp(fieldIden), t.exp(appliedReceiver),translatedFilter)(t.liftPos(this))
    }
  }

}
