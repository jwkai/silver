package viper.silver.plugin.crimp.parser

import viper.silver.FastMessaging
import viper.silver.ast.{AnnotationInfo, ErrTrafo, Exp, NoInfo, Position}
import viper.silver.parser.{NameAnalyser, PAnnotatedExp, PCall, PDomainType, PExp, PExtender, PFieldDecl, PIdnUse, PKeywordLang, PKw, PMagicWandExp, PMethod, PNode, POpApp, PPackageWand, PProgram, PReserved, PSetType, PType, PTypeRenaming, PTypeSubstitution, PTypeVar, Translator, TypeChecker, TypeHelper}
import viper.silver.plugin.crimp.ast.{CrimpApp, CrimpTriple, CrimpTripleWithId, CrimpTripleWithoutId}
import viper.silver.plugin.crimp.{CrimpPlugin, DecompDepth, DomainsGenerator, ReduceErrors}
import viper.silver.plugin.standard.termination.PDecreasesClause
import viper.silver.verifier.errors

case object PCrimpKeyword extends PKw("crimp") with PKeywordLang


case class PCrimpInner(mapping: PExp, fieldID: PIdnUse, receiver: PExp)(val pos: (Position, Position))
  extends PExtender {

  override def subnodes: Iterator[PNode] = Iterator(mapping, fieldID, receiver)

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
case class PCrimp(keyword: PReserved[PCrimpKeyword.type], operator: PExp, mappingFieldReceiver: PCrimpInner, filter: PExp)(val pos: (Position, Position))
  extends PExtender with POpApp {

  override def subnodes: Iterator[PNode] = Iterator(operator, mappingFieldReceiver, filter)

  override def args: Seq[PExp] = Seq(filter)

  // Following fields are set during resolving, respectively in the typecheck method below
  var crimpTypeRenaming: Option[PTypeRenaming] = None
  var crimpSubstitution: Option[PTypeSubstitution] = None
  var _extraLocalTypeVariables: Set[PDomainType] = Set()

  override def extraLocalTypeVariables: Set[PDomainType] = _extraLocalTypeVariables

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    // fresh type variables should have been generated for components by PCrimp.typecheck
    typeSubstitutions.clear()
    typeSubstitutions += ts
    typ = typ.substitute(ts)
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
    val opName = operator match {
      case c: PComponentCall => c.idnref.name
      case c: PCall => c.idnref.name
      case _ => operator.pretty
    }
    val opMember = t.program.extensions.collectFirst {
      case p: POperator if p.idndef.name == opName => p
    }
    val opHasID = opMember match {
      case Some(opm) => opm match {
        case p: POperator => p.opUnit.isDefined
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
    // A `@decompDepth("N")` annotation of this crimp expression is kept as the CrimpApp's info for the lowering (the
    // Translator does not pass an extension expression's annotations on).
    val depthInfo = PCrimp.decompDepthAnnotation(this).flatMap(_.toOption) match {
      case Some(depth) => AnnotationInfo(Map(DecompDepth.key -> Seq(depth.toString)))
      case None => NoInfo
    }
    CrimpApp(
      liftedTuple,
      filterTranslated.withMeta((t.liftPos(this), filterTranslated.info, errTFoldApply)),
      fieldString
    )(pos = t.liftPos(this), info = depthInfo, errT = errTFoldApply)
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

  /** Same as TypeChecker.checkTopTyped(exp, Some(pattern)), but the expected type permits free type variables.
   * Here, pattern can have unknown type; prevents "found incompatible type `Set[Int]`, expected `Set[CrimpSet#1]` "*/
  def checkTopTypedPattern(t: TypeChecker, exp: PExp, pattern: PType): Unit = {
    t.checkInternal(exp)
    if (exp.typ.isValidOrUndeclared && exp.typeSubstitutions.nonEmpty) {
      val etss = exp.typeSubstitutions.flatMap(_.add(exp.typ, pattern).toOption)
      var error = true
      if (etss.nonEmpty) {
        val ts = t.selectAndGroundTypeSubstitution(exp, etss)
        exp.forceSubstitution(ts)
        error = !TypeHelper.isSubtype(exp.typ, pattern.substitute(ts))
      }
      if (error) {
        val reportedActual =
          if (exp.typ.isGround) exp.typ
          else exp.typ.substitute(t.selectAndGroundTypeSubstitution(exp, exp.typeSubstitutions))
        t.messages ++= FastMessaging.message(exp,
          s"found incompatible type `${reportedActual.pretty}`, expected `${pattern.pretty}`")
      }
    }
  }
  
  def typecheck(pc: PCrimp)(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {

    def getFreshTypeSubstitution(tvs: Seq[PDomainType]): PTypeRenaming =
      PTypeVar.freshTypeSubstitutionPTVs(tvs)

    // Checks that a substitution is fully reduced (idempotent)
    def refreshWith(ts: PTypeSubstitution, rts: PTypeRenaming): PTypeSubstitution = {
      require(ts.isFullyReduced)
      require(rts.isFullyReduced)
      new PTypeSubstitution(ts map (kv => rts.rename(kv._1) -> kv._2.substitute(rts)))
    }

    if (pc.typeSubstitutions.nonEmpty) return None // already checked
    unsupportedPosition(pc).foreach(msg => return Some(Seq(msg)))
    decompDepthAnnotation(pc).foreach(_.left.foreach(message => return Some(Seq(message))))
    var messagesOut : Seq[String] = Seq()

    // Check type of filter, must be a Set. Extract it out
    checkTopTypedPattern(t, pc.filter, CrimpPlugin.makeSetType(getNewTypeVariable("CrimpSet")))
    val setType: PType = pc.filter.typ match {
      case PSetType(_, bTyp) => bTyp.inner
      case ft if !ft.isValidOrUndeclared => return Some(messagesOut)
      case _ =>
        messagesOut = messagesOut :+ "Filter should of Set[...] type."
        return Some(messagesOut)
    }

    // Check type of operator, must be an Operator with unit as argument
    checkTopTypedPattern(t, pc.operator, CrimpPlugin.makeDomainType(DomainsGenerator.opDKey,
      Seq(getNewTypeVariable("CrimpOp"))))

    // Look inside the operator type
    pc.operator.typ match {
      case pd: PDomainType if pd.domain.name == DomainsGenerator.opDKey =>
        // Set the type of this PCrimp to the Operator unit's type
        pc.typ = pd.typeArguments.head
      case ot if !ot.isValidOrUndeclared => return Some(messagesOut)
      case _ =>
        messagesOut = messagesOut :+ "Operator should of Operator[_] type."
        return Some(messagesOut)
    }
    
    // Check type of mappingFieldReceiver. Receiver must take the element in the set
    // Mapping must be from type of field to type of the operator (typ).
    messagesOut ++= pc.mappingFieldReceiver.typecheckComp(t, n, pc.typ, setType)

    // Set type of this node, and pass ground type to expression context via identity substitution
    if (messagesOut.isEmpty && pc.typ.isGround) pc.typeSubstitutions += PTypeSubstitution.id
    if (messagesOut.isEmpty) None else Some(messagesOut)
  }

  /** The `@decompDepth("N")` annotation of `pc` (`@decompDepth("N") (crimp[..][..](..))`, also among other annotations
   * of the same expression), if any. */
  def decompDepthAnnotation(pc: PCrimp): Option[Either[String, Int]] = {
    val annotations = Iterator.iterate(pc.getParent)(_.flatMap(_.getParent)).map(_.orNull)
      .takeWhile(_.isInstanceOf[PAnnotatedExp]).map(_.asInstanceOf[PAnnotatedExp].annotation).toSeq
    DecompDepth.of(annotations.map(a => a.key.str -> a.values.inner.toSeq.map(_.str)))
  }

  /** The error for a crimp in a position that is not supported.
   * A crimp is only supported in a method's body or pre- and post-conditions (including loop invariants),
   * and cannot be nested or occur in crimp component (receiver, mapping, operator) bodies, function bodies or domains.
   * Magic wands are also rejected: Viper evaluates a wand's LHS and RHS relative to the state where it is applied,
   * and the hypothetical state of a package proof script; we do not determine crimp heap indices for these states.
   * A decreases clause (of a method, loop or function) of a termination measure is rejected; this is a standard plugin.
   * TODO: some of embeddings may be supported in future work, but this requires care. */
  private def unsupportedPosition(pc: PCrimp): Option[String] = {
    val ancestors = Iterator.iterate(pc.getParent)(_.flatMap(_.getParent)).takeWhile(_.isDefined).map(_.get).toSeq
    if (!ancestors.lastOption.exists(_.isInstanceOf[PProgram])) None // no parent links: position unknown
    else if (ancestors.exists(_.isInstanceOf[PCrimp]))
      Some("Crimp inside another crimp is not supported.")
    else if (ancestors.exists(_.isInstanceOf[PMagicWandExp]))
      Some("Crimp inside a magic wand is not supported.")
    else if (ancestors.exists(_.isInstanceOf[PPackageWand]))
      Some("Crimp in a package proof script is not supported.")
    else if (ancestors.exists(_.isInstanceOf[PDecreasesClause]))
      Some("Crimp in a decreases clause is not supported.")
    else if (!ancestors.exists(_.isInstanceOf[PMethod]))
      Some("Crimp outside a method is not supported.")
    else None
  }
}
