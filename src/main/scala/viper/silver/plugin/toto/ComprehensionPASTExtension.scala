package viper.silver.plugin.toto;

import viper.silver.ast.{Exp, Field, NoPosition, Position}
import viper.silver.parser.PExtender
import viper.silver.parser._
import viper.silver.plugin.toto.PComprehension.getNewTypeVariable

import scala.collection.immutable.{AbstractSeq, LinearSeq}
import scala.xml.NodeSeq;

case class PComprehension(op: PCall, unit: PExp, mappingFieldReceiver: PMappingFieldReceiver, filter: PExp)(val pos: (Position, Position)) extends PExtender with PExp {
  override val getSubnodes: Seq[PNode] = Seq(op, unit, mappingFieldReceiver, filter)


  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    var messagesOut : Seq[String] = Seq()

    // Check type of filter, must be a Set
    t.checkTopTyped(filter, Some(PSetType(getNewTypeVariable("CompSet"))()))
    val setType: PType = filter.typ match {
      case PSetType(e) => e
      case _ =>
        messagesOut = messagesOut :+ "Filter should of Set[...] type."
        return Some(messagesOut)
    }

    // Check type of unit
    t.checkTopTyped(unit, None)

    // Check type of op, must be an Operator with unit as argument
    val correctOpType = ComprehensionPlugin.makeDomainType("Operator", Seq(unit.typ))
    t.checkTopTyped(op, Some(correctOpType))

    // Check type of mappingFieldReceiver
    mappingFieldReceiver.typecheckComp(t,  unit.typ, setType)

    // Set type of this node
    this.typ = unit.typ
    Some(messagesOut)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // this calls t.checkTopTyped, which will call checkInternal, which calls the above typecheck
    t.checkTopTyped(this, Some(expected))
    None
  }

  val _typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = unit.typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution): Unit = unit.forceSubstitution(ts)

  // Translate the parser node into an AST node
  override def translateExp(t: Translator): Exp = {
    val opTranslated = t.exp(op)
    val unitTranslated = t.exp(unit)
    val mappingFieldReceiverTranslated = mappingFieldReceiver.translateMember(t)
    val filterTranslated = t.exp(filter)
    opTranslated
//    Comprehension(opTranslated, unitTranslated, mappingFieldReceiverTranslated, filterTranslated)(pos)
  }

}

object PComprehension {
  private var counter = 0
  private def increment(): Int = {
    counter += 1;
    counter
  }

  private def getNewTypeVariable(name: String): PDomainType = {
    PTypeVar(s"$name#" + increment())
  }

}
