package viper.silver.plugin.hreduce.parser

import viper.silver.ast.{ErrTrafo, Exp, NoPosition, Position}
import viper.silver.parser._
import viper.silver.plugin.hreduce.parser.PReduce.getNewTypeVariable
import viper.silver.plugin.hreduce._
import viper.silver.plugin.hreduce.ast.{AReduceApply, AReduction3Tuple}
import viper.silver.verifier.errors

case object PReduceKeyword extends PKw("hreduce") with PKeywordLang

// First representation, the user input of reduction gets turned into this PAst Node
case class PReduce(keyword: PReserved[PReduceKeyword.type], opUnit: PCall, mappingFieldReceiver: PMappingFieldReceiver, filter: PExp)(val pos: (Position, Position)) extends PExtender with PExp {

  override val subnodes: Seq[PNode] = Seq(opUnit, mappingFieldReceiver, filter)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    var messagesOut : Seq[String] = Seq()

    // Check type of filter, must be a Set. Extract it out
    t.checkTopTyped(filter, Some(PSetType(PReserved.implied(PKw.Set),
      PGrouped.impliedBracket(getNewTypeVariable("HReduceSet")))(NoPosition, NoPosition)))
    val setType: PType = filter.typ match {
      case PSetType(_, bTyp) => bTyp.inner
      case _ =>
        messagesOut = messagesOut :+ "Filter should of Set[...] type."
        return Some(messagesOut)
    }

    // Check type of unit
//    t.checkTopTyped(unit, None)

    // Check type of op, must be an Operator with unit as argument
//    val correctOpType = ComprehensionPlugin.makeDomainType("Operator", Seq(unit.typ))
    t.checkTopTyped(opUnit, Some(HReducePlugin.makeDomainType("Operator", Seq(getNewTypeVariable("CompOp")))))

    // Look inside the operator type
    opUnit.typ match {
      case pd: PDomainType if pd.domain.name == DomainsGenerator.opDKey =>
        // Set the type of this PComprehension to the Operator unit's type
        typ = pd.typeArguments.head
      case _ =>
        messagesOut = messagesOut :+ "Operator should of Operator[_] type."
        return Some(messagesOut)
    }

    // Check type of mappingFieldReceiver. Receiver must take the element in the set
    // Mapping must be from type of field to type of the operator (typ).
    mappingFieldReceiver.typecheckComp(t, n, typ, setType)

    // Set type of this node
    Some(messagesOut)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // this calls t.checkTopTyped, which will call checkInternal, which calls the above typecheck
    t.checkTopTyped(this, Some(expected))
    None
  }

  val _typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = Seq()

  override def forceSubstitution(ts: PTypeSubstitution): Unit = ()

  // Translate the parser node into an AST node
  override def translateExp(t: Translator): Exp = {
    val opTranslated = t.exp(opUnit)
    val (mappingOut, fieldString, receiverTranslated) = mappingFieldReceiver.translateTo(t)
    val filterTranslated = t.exp(filter)
    val tuple = AReduction3Tuple(receiverTranslated, mappingOut, opTranslated)(t.liftPos(this))
    val reduceApply = AReduceApply(tuple, filterTranslated, fieldString)(t.liftPos(this))
    val errTFoldApply = ErrTrafo({
      case errors.PreconditionInAppFalse(offendingNode, reason, cached) =>
        ReduceErrors.ReduceApplyError(offendingNode, reduceApply, reason, cached)
    })
    AReduceApply(
      tuple.copy()(pos = t.liftPos(this), info = tuple.info, errT = errTFoldApply),
      filterTranslated.withMeta((t.liftPos(this), filterTranslated.info, errTFoldApply)),
      fieldString
    )(pos = t.liftPos(this), info = reduceApply.info, errT = errTFoldApply)
  }
}

object PReduce {
  type PReduceKeywordType = PReserved[PReduceKeyword.type]

  private var counter = 0
  private def increment(): Int = {
    counter += 1
    counter
  }

  private def getNewTypeVariable(name: String): PDomainType = {
    val freeName = s"$name" + PTypeVar.sep + increment()
    // new PTypeVar should be free
    assert(PTypeVar.isFreePTVName(freeName))
    PTypeVar(freeName)
  }
}
