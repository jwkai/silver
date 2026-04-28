package viper.silver.plugin.crimp.parser

import viper.silver.ast.{ErrTrafo, Exp, NoPosition, Position}
import viper.silver.parser.{NameAnalyser, PCall, PDomainType, PExp, PExtender, PFieldDecl, PGrouped, PIdnUse, PIntLit, PKeywordLang, PKw, PNode, POpApp, PReserved, PSetType, PType, PTypeRenaming, PTypeSubstitution, PTypeVar, PUnknown, Translator, TypeChecker, TypeHelper}
import viper.silver.plugin.crimp.ast.{CrimpApp, CrimpTriple, CrimpTripleWithId, CrimpTripleWithoutId}
import viper.silver.plugin.crimp.{CrimpPlugin, DomainsGenerator, ReduceErrors}
import viper.silver.plugin.crimp.parser.PCrimp.getNewTypeVariable
import viper.silver.verifier.errors

case object PCrimpKeyword extends PKw("crimp") with PKeywordLang


case class PCrimpInner(mapping: PCall, fieldID: PIdnUse, receiver: PCall)(val pos: (Position, Position))
  extends PExtender {

  override val subnodes: Iterator[PNode] = Iterator(mapping, fieldID, receiver)

  def typeSubstitutions: Seq[PTypeSubstitution] =
    mapping.signatures ++ receiver.signatures

  def typecheckComp(t: TypeChecker, n: NameAnalyser, typeUnit: PType, typeFilter: PType): Seq[String] = {
    val errorSeq: Seq[String] = Seq()

    val correctReceiverType = CrimpPlugin.makeDomainType("Receiver", Seq(typeFilter))
    t.checkTopTyped(receiver, Some(correctReceiverType))

    // find the field in the program
    val fields = n.globalDefinitions(fieldID.name)
    fields match {
      case Seq(field) =>
        field match {
          case decl: PFieldDecl =>
            // Mapping must be from field's type to operator's type
            val correctMappingType = CrimpPlugin.makeDomainType("Mapping", Seq(decl.typ, typeUnit))
            t.checkTopTyped(mapping, Some(correctMappingType))
          case _ => return errorSeq :+ "Reduce field not declared as a field."
        }
      case Seq() => return errorSeq :+ "Field not found."
      case _ => return errorSeq :+ "Field not resolvable (multiple definitions found)."
    }
    errorSeq
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    Some(Seq("Internal error: typecheck should only be called from PCrimp node."))
  }

  def translateTo(t: Translator): (Exp, String, Exp) = {
    val mappingOut = t.exp(mapping)
    val fieldOut = fieldID.name
    val receiverOut = t.exp(receiver)
    (mappingOut, fieldOut, receiverOut)
  }
}

// First representation, the user input of reduction gets turned into this PAst Node
case class PCrimp(keyword: PReserved[PCrimpKeyword.type], operator: PCall, mappingFieldReceiver: PCrimpInner, filter: PExp)(val pos: (Position, Position))
  extends PExtender with POpApp {

  override val subnodes: Iterator[PNode] = Iterator(operator, mappingFieldReceiver, filter)

  override def args: Seq[PExp] = Seq(filter)

  // Following fields are set during resolving, respectively in the typecheck method below
  var crimpTypeRenaming: Option[PTypeRenaming] = None
  var crimpSubstitution: Option[PTypeSubstitution] = None
  var _extraLocalTypeVariables: Set[PDomainType] = Set()

  override def extraLocalTypeVariables: Set[PDomainType] = _extraLocalTypeVariables

  override def forceSubstitution(ots: PTypeSubstitution): Unit = {
    val ts = crimpTypeRenaming match {
      case Some(ctr) =>
        val s3 = PTypeSubstitution(ctr.mm.map(kv => kv._1 -> (ots.get(kv._2) match {
          case Some(pt) => pt
          case None => PTypeSubstitution.defaultType
        })))
        assert(s3.m.keySet == ctr.mm.keySet)
        assert(s3.m.forall(_._2.isGround))
        crimpSubstitution = Some(s3)
        ctr.mm.values.foldLeft(ots)(
          (tss, s) => if (tss.contains(s)) tss else tss.add(s, PTypeSubstitution.defaultType).toOption.get)
      case _ => ots
    }
    super.forceSubstitution(ts)
  }
  
  override def signatures: List[PTypeSubstitution] = {
    assert(args.length == 1, s"PCrimp: Expected args to be of length 1 but was of length ${args.length}")
    crimpTypeRenaming match {
      case Some(typeRenaming) =>
        List(
          new PTypeSubstitution(
            Map(POpApp.pArg(0).domain.name -> filter.typ.substitute(typeRenaming),
              POpApp.pRes.domain.name -> operator.typ.substitute(typeRenaming))
        ))
      case None => List()
    }
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = PCrimp.typecheck(this)(t, n)

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // this calls t.checkTopTyped, which will call checkInternal, which calls the above typecheck
    t.checkTopTyped(this, Some(expected))
    None
  }

  // Translate the parser node into an AST node
  override def translateExp(t: Translator): Exp = {
    val opTranslated = t.exp(operator)
    val (mappingOut, fieldString, receiverTranslated) = mappingFieldReceiver.translateTo(t)
    val filterTranslated = t.exp(filter)
    val opMember = t.program.filterMembers {
      case p: POperator if p.idndef.name == operator.idnref.name => true
      case _ => false
    }.members.headOption
    val opHasID = opMember match {
      case Some(opm) => opm match {
        case _: POperator => true
        case _ => throw new Exception(s"User-declared operator ${operator.toString} has unexpected type.")
      }
      case None => throw new Exception(s"User-declared operator ${operator.toString} not found.")
    }
    val tuple = CrimpTriple(receiverTranslated, mappingOut, opTranslated, hasID = opHasID)(t.liftPos(this))
    val reduceApply = CrimpApp(tuple, filterTranslated, fieldString)(t.liftPos(this))
    val errTFoldApply = ErrTrafo({
      case errors.PreconditionInAppFalse(offendingNode, reason, cached) =>
        ReduceErrors.ReduceApplyError(offendingNode, reduceApply, reason, cached)
    })
    val liftedTuple = tuple match {
      case a : CrimpTripleWithId => a.copy()(pos = t.liftPos(this), info = tuple.info, errT = errTFoldApply)
      case a : CrimpTripleWithoutId => a.copy()(pos = t.liftPos(this), info = tuple.info, errT = errTFoldApply)
    }
    CrimpApp(
      liftedTuple,
      filterTranslated.withMeta((t.liftPos(this), filterTranslated.info, errTFoldApply)),
      fieldString
    )(pos = t.liftPos(this), info = reduceApply.info, errT = errTFoldApply)
  }
}

object PCrimp {
  type PCrimpKeywordType = PReserved[PCrimpKeyword.type]

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

  def typecheck(pc: PCrimp)(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    //    var messagesOut : Seq[String] = Seq()

    def getFreshTypeSubstitution(tvs: Seq[PDomainType]): PTypeRenaming =
      PTypeVar.freshTypeSubstitutionPTVs(tvs)

    // Checks that a substitution is fully reduced (idempotent)
    def refreshWith(ts: PTypeSubstitution, rts: PTypeRenaming): PTypeSubstitution = {
      require(ts.isFullyReduced)
      require(rts.isFullyReduced)
      new PTypeSubstitution(ts map (kv => rts.rename(kv._1) -> kv._2.substitute(rts)))
    }

    var extraReturnTypeConstraint: Option[PType] = None

    if (pc.typeSubstitutions.isEmpty) {
      pc.args.foreach(t.checkTopTyped(_, None))
      var nestedTypeError = !pc.args.forall(a => a.typ.isValidOrUndeclared)

      if (!nestedTypeError && pc.signatures.nonEmpty && pc.args.forall(_.typeSubstitutions.nonEmpty)) {
        val ltr = getFreshTypeSubstitution(pc.localScope.toList) //local type renaming - fresh versions
        val rlts = pc.signatures map (ts => refreshWith(ts, ltr)) //local substitutions refreshed
        assert(rlts.nonEmpty)
        val rrt: PDomainType = POpApp.pRes.substitute(ltr).asInstanceOf[PDomainType] // return type (which is a dummy type variable) replaced with fresh type
        val flat = pc.args.indices map (i => POpApp.pArg(i).substitute(ltr)) //fresh local argument types
        // the tuples below are: (fresh argument type, argument type as used in domain of substitutions, substitutions, the argument itself)
        pc.typeSubstitutions ++= t.unifySequenceWithSubstitutions(rlts, flat.indices.map(i => (pc.args(i).typ, flat(i), pc.args(i).typeSubsDistinct.toSeq, pc.args(i))) ++
          (
            extraReturnTypeConstraint match {
              case None => Nil
              case Some(t) => Seq((t, rrt, List(PTypeSubstitution.id), pc))
            }
            )
        ).getOrElse(Seq())
        val ts = pc.typeSubsDistinct
        if (ts.isEmpty)
          t.typeError(pc)
        pc.typ = if (ts.size == 1) rrt.substitute(ts.head) else rrt
      } else {
        pc.typeSubstitutions.clear()
        pc.typ = PUnknown()
      }
    }

    //    t.checkTopTyped(filter, Some(PSetType(PReserved.implied(PKw.Set),
    //      PGrouped.impliedBracket(getNewTypeVariable("CrimpSet")))(NoPosition, NoPosition)))
    //    val setType: PType = filter.typ match {
    //      case PSetType(_, bTyp) => bTyp.inner
    //      case _ =>
    //        messagesOut = messagesOut :+ "Filter should be of Set[_] type."
    //        return Some(messagesOut)
    //    }

    // Check type of unit
    //    t.checkTopTyped(unit, None)

    // Check type of op, must be an Operator with unit as argument
    //    val correctOpType = ComprehensionPlugin.makeDomainType("Operator", Seq(unit.typ))
    //    t.checkTopTyped(operator, Some(CrimpPlugin.makeDomainType("Operator", Seq(getNewTypeVariable("CompOp")))))

    // Look inside the operator type
    //    operator.typ match {
    //      case pd: PDomainType if pd.domain.name == DomainsGenerator.opDKey =>
    //        // Set the type of this PComprehension to the Operator unit's type
    //        typ = pd.typeArguments.head
    //      case _ =>
    //        messagesOut = messagesOut :+ "Operator should be of Operator[_] type."
    //        return Some(messagesOut)
    //    }

    // Check type of mappingFieldReceiver. Receiver must take the element in the set
    // Mapping must be from type of field to type of the operator (typ).
    //    mappingFieldReceiver.typecheckComp(t, n, typ, setType)

    // Set type of this node
    None
  }
}
