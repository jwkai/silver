package viper.silver.plugin.toto;

import viper.silver.ast.{Exp, Field, NoPosition, Position}
import viper.silver.parser.PExtender
import viper.silver.parser._

import scala.collection.immutable.{AbstractSeq, LinearSeq}
import scala.xml.NodeSeq;

case class PComprehension(op: PCall, unit: PExp, mappingFieldReceiver: PMappingFieldReceiver, filter: PExp)(val pos: (Position, Position)) extends PExtender with PExp {
  override val getSubnodes: Seq[PNode] = Seq(op, unit, mappingFieldReceiver, filter)

//  override val typ =

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    var messagesOut : Seq[String] = Seq()
    t.checkTopTyped(filter, None)
//    PDomainType("Operator", Seq(PType))(pos)
    t.checkTopTyped(unit, None)
    val correctOpType = ComprehensionPlugin.makeDomainType("Operator", Seq(unit.typ))
    t.checkTopTyped(op, Some(correctOpType))
    val setType: PType = filter.typ match {
      case PSetType(e) => e
      case _ =>
        messagesOut = messagesOut :+ "Filter should of Set[...] type."
        return Some(messagesOut)
    }
    mappingFieldReceiver.typecheckComp(t, n, unit.typ, setType)
//    mappingFieldReceiver.receiver.typ match {
//      case PDomainType(domain, args) =>
//        if (domain.name == "Receiver")
//          ()
//        else
//          messagesOut = messagesOut :+ "Receiver expression not a receiver."
//      case _ =>
//        messagesOut = messagesOut :+ "Receiver expression not a receiver."
//    }
    this.typ = unit.typ
    None
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(this, Some(expected))
    None
  }


  val _typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = unit.typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution): Unit = unit.forceSubstitution(ts)

  override def translateExp(t: Translator): Exp = {
    t.exp(unit)
//    val translatedOp = t.exp(op)
//    val translatedUnit = t.exp(unit)
//    val translatedFilter = t.exp(filter)
//    receiver match {
//      case appliedMapping @ PCall(mapping, args, typeAnnotated) =>
//        args.head match {
//          case PFieldAccess(appliedReceiver, fieldIden) =>
//            Comprehension(
//              translatedOp,
//              translatedUnit,
//              Some(t.exp(appliedMapping.copy(args = args.tail)(appliedMapping.pos))),
//              t.exp(fieldIden), t.exp(appliedReceiver), translatedFilter)(t.liftPos(this))
//        }
//      case PFieldAccess(appliedReceiver, fieldIden) =>
//        Comprehension(translatedOp, translatedUnit, None,
//          t.exp(fieldIden), t.exp(appliedReceiver),translatedFilter)(t.liftPos(this))
//    }
  }

}
