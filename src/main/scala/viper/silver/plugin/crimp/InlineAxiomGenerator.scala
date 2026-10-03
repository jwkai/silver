package viper.silver.plugin.crimp

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.plugin.crimp.ast.{CrHeap, CrimpApp, CrimpDecl, HeapKey, CrHeapMap, crHeapInfo}
import viper.silver.plugin.crimp.util.AxiomHelper
import viper.silver.verifier.{AbstractError, ConsistencyError, errors}
import viper.silver.verifier.errors.{ExhaleFailed, IfFailed, InhaleFailed, WhileFailed}

import scala.collection.mutable

/** Generates the inline heap axioms of one method and tags each of its statements with the crimp-heap indices at which
  * the crimps in it are evaluated (crHeapInfo).
  *
  * Crimp-heap indices are per method and per receiver (a receiver instance together with a field, HeapKey). All
  * indices are 0 on entry to the method. A command advances the receivers over the fields in its conservative field
  * footprint (AxiomHelper.footprintFields / modifiedFields) and no others; numbers are allocated per field, so all
  * receivers over one field advance together (CrHeapMap). A command that advances nothing gets no axioms. */
class InlineAxiomGenerator(program: Program, methodName: String, fuelIsTwo: Boolean,
                           reportError: AbstractError => Unit) {

  val method: Method = program.findMethod(methodName)
  val helper = new AxiomHelper(program, fuelIsTwo)

  // The receivers of the method, their fields and the crimp declarations it uses
  private var receivers: Set[HeapKey] = Set()
  private var receiverFields: Set[String] = Set()
  var crimpDeclsUsed: Set[CrimpDecl] = Set()

  // The current indices and, per field of, the next unused index number. Numbers are never reused within the method.
  private var current: CrHeapMap = CrHeapMap(Map())
  private val nextIndex: mutable.Map[String, Int] = mutable.Map()
  // Per field, the index after its last advance by anything but an exhale. An inhale links it with its new index too,
  // so that a call (exhale, then inhale) links the state before the call with the state after it.
  private val lastHeld: mutable.Map[String, CrHeap] = mutable.Map()
  // The indices at each user label and at each call's _methodLabel.
  private val labelCrHeaps: mutable.Map[String, CrHeapMap] = mutable.Map()

  private var uniqueIDMethodOut = 0
  private var uniqueIDMethodArg = 0
  private var uniqueLabelMethod = 0
  // Viper label names only; no crimp-heap index is ever derived from them.
  private var uniqueLabelPre = 0

  private def getUniqueIDMethodOut: String = {
    uniqueIDMethodOut += 1
    s"$uniqueIDMethodOut"
  }

  private def getUniqueIDMethodArg: String = {
    uniqueIDMethodArg += 1
    s"$uniqueIDMethodArg"
  }

  // get unique method label
  private def getUniqueLabelMethod: Label = {
    uniqueLabelMethod += 1
    Label(s"${helper.methodLabelPrefix}l$uniqueLabelMethod", Seq())()
  }

  // A fresh label placed immediately before an advancing command: old[..] of it is the state the command starts from.
  private def freshPreLabel(): Label = {
    uniqueLabelPre += 1
    Label(s"${helper.labelPrefix}_pre$uniqueLabelPre", Seq())()
  }

  def initReceivers(converted: Method): Unit = {
    val applies = converted.deepCollect { case ra: CrimpApp => ra }
    receivers = applies.map(_.heapKey).toSet
    receiverFields = receivers.map(_.field)
    crimpDeclsUsed = applies.map(_.crimpFunctionDeclaration).toSet
    nextIndex.clear()
    receiverFields.foreach(f => nextIndex(f) = 1)
    current = getOldCrHeap
    lastHeld.clear()
    receiverFields.foreach(f => lastHeld(f) = CrHeap(0))
    labelCrHeaps.clear()
  }

  def getFuelExp: Exp = {
    helper.fuelDefaultExp
  }

  def getCurrentCrHeap: CrHeapMap = current

  // The indices of the method's pre-state: 0 for every receiver.
  def getOldCrHeap: CrHeapMap = CrHeapMap.of(receivers, CrHeap(0))

  // The indices recorded at label `name` (a user label or a call's _methodLabel), for old[name](..).
  def getCrHeapFromUserLabel(name: String, pos: Position): CrHeapMap =
    labelCrHeaps.getOrElse(name, {
      reportError(ConsistencyError(s"crimp: old[$name](..) contains a crimp, but label $name is not declared " +
        s"before it in method $methodName", pos))
      current
    })

  // Moves every receiver over a field in `fields` to a fresh index; returns the indices before the move.
  private def advance(fields: Set[String]): CrHeapMap = {
    val before = current
    fields.intersect(receiverFields).toSeq.sorted.foreach { f =>
      current = current.withField(f, CrHeap(nextIndex(f)))
      lastHeld(f) = CrHeap(nextIndex(f))
      nextIndex(f) += 1
    }
    before
  }

  // `inhale extLink(o, n)` for each field in `fields` whose index moved from o in `from` to n in `to` (and, with `extra`,
  // for further pairs): the extensionality axiom is triggered only on the index pairs linked this way
  private def extLinks(from: CrHeapMap, to: CrHeapMap, fields: Iterable[String],
                       extra: Seq[(CrHeap, CrHeap)] = Seq()): Seq[Stmt] = {
    val pairs = fields.toSeq.sorted.map(f => (from.ofField(f), to.ofField(f))) ++ extra
    pairs.distinct.filter { case (o, n) => o != n }.map { case (o, n) => Inhale(helper.extLinkApply(o.toExp, n.toExp))() }
  }

  // The crimp declarations over `field`, in a fixed order.
  private def declsOver(field: String): Seq[CrimpDecl] =
    crimpDeclsUsed.toSeq.filter(_.fieldName == field).sortBy(_.key)

  private def tagged[S <: Stmt](s: S, rh: CrHeapMap): S =
    s.withMeta(s.pos, MakeInfoPair(s.info, crHeapInfo(rh)), s.errT)

  /** Lowers the body of the method: generates the axioms for the commands that change field locations and tags every
    * statement with the indices at which its crimps are evaluated. Must follow initReceivers. */
  def lowerBody(body: Seqn): Seqn = lowerSeqn(body)

  /** For a method without a body: its postconditions are evaluated at fresh indices (they are not related to the
    * precondition's). */
  def lowerMissingBody(): Unit = advance(receiverFields)

  private def lowerSeqn(s: Seqn): Seqn =
    Seqn(s.ss.map(lowerStmt), s.scopedSeqnDeclarations)(s.pos, s.info, s.errT)

  // A statement that reads a receiver field under old(..) (or old[L](..)) relates the state after it with the method's
  // entry state (or the state at L), e.g. `inhale forall i :: .. loc(a,i).f == old(loc(a,i).f)` after an exhale, and
  // the extensionality axiom must be available for that pair of indices, too: it gets a link after the statement.
  // Compound statements are handled through their parts.
  private def lowerStmt(s: Stmt): Stmt = s match {
    case _: Seqn | _: If | _: While => lowerStmtCore(s)
    case _ =>
      val out = lowerStmtCore(s)
      val emitted = out.deepCollect { case Inhale(d: DomainFuncApp) if d.funcname == DomainsGenerator.extLinkKey => d.args }.toSet
      val links = oldLinks(s).filterNot { case Inhale(d: DomainFuncApp) => emitted.contains(d.args); case _ => false }
      if (links.isEmpty) out else Seqn(out +: links, Seq())(s.pos)
  }

  private def fieldsReadIn(e: Node): Seq[String] =
    e.deepCollect { case fa: FieldAccess => fa.field.name; case ra: CrimpApp => ra.heapKey.field }
      .filter(receiverFields.contains).distinct

  private def oldLinks(s: Stmt): Seq[Stmt] = {
    val toEntry = s.deepCollect { case o: Old => o.exp }.flatMap(fieldsReadIn).distinct
      .map(f => (CrHeap(0), current.ofField(f)))
    val toLabel = s.deepCollect { case lo: LabelledOld => lo }.flatMap(lo => labelCrHeaps.get(lo.oldLabel) match {
      case Some(rh) => fieldsReadIn(lo.exp).map(f => (rh.ofField(f), current.ofField(f)))
      case None => Seq()
    })
    extLinks(current, current, Seq(), (toEntry ++ toLabel).filter { case (o, n) => o.crh < n.crh })
  }

  private def lowerStmtCore(s: Stmt): Stmt = s match {
    case sq: Seqn => lowerSeqn(sq)
    case i: If => ifCrHeapJoin(i)
    case w: While => whileCrHeapFlattenInvariants(w)
    case fa: FieldAssign => generateHeapWriteAxioms(fa)
    case e: Exhale if !helper.checkIfPure(e) => generateExhaleAxioms(e)
    case i: Inhale if !helper.checkIfPure(i) => generateInhaleAxioms(i, i.exp)
    // Every Assume becomes an Inhale before verification (CrimpPlugin.beforeVerify).
    case a: Assume if !helper.checkIfPure(a) => generateInhaleAxioms(a, a.exp)
    case n: NewStmt => generateInhaleAxioms(n, n)
    case l: Label =>
      labelCrHeaps.put(l.name, current)
      tagged(l, current)
    // Commands that may change field locations but get no linking axioms: they only advance.
    case a: Apply => advanceUnlinked(a, helper.footprintFields(a.exp))
    case p: Package => advanceUnlinked(p, helper.footprintFields(p.wand) ++ helper.modifiedFields(p.proofScript))
    case q: Quasihavoc => advanceUnlinked(q, helper.footprintFields(q.exp))
    case q: Quasihavocall => advanceUnlinked(q, helper.footprintFields(q.exp))
    case mc: MethodCall => advanceUnlinked(mc, helper.modifiedFields(mc))
    case g: Goto =>
      reportError(ConsistencyError(s"crimp: goto is not supported in method $methodName, which evaluates crimps", g.pos))
      tagged(g, current)
    case e: ExtensionStmt => advanceUnlinked(e, receiverFields)
    // Local assignments and declarations, labels, assert, fold, unfold, pure inhale/exhale/assume: nothing changes.
    case other => generateHeapReadAxioms(other, current)
  }

  // The command's crimps are evaluated at the indices before it; afterwards the receivers over `fields` are at
  // fresh indices that no axiom relates to the earlier ones.
  private def advanceUnlinked[S <: Stmt](s: S, fields: Set[String]): S = {
    val t = tagged(s, current)
    advance(fields)
    t
  }

  // The condition is evaluated at the indices before the if, and both branches start from them. A receiver that some
  // branch advanced (by any command, a write included) gets a fresh join index after the if; nextIndex is shared by the
  // branches, so the number is fresh after both. The other receivers keep their index and get no join axioms.
  // The read axioms of the condition's field reads are inlined immediately before the if, at the indices before it. 
  private def ifCrHeapJoin(i: If): Stmt = {
    val crHeapOrig = current
    val lastHeldOrig = lastHeld.clone()
    val condReads = generateCondReadAxioms(i.cond, crHeapOrig,
      ErrTrafo({ case InhaleFailed(_, reason, cached) => IfFailed(i.cond, reason, cached) }))
    val thnAxs = lowerSeqn(i.thn)
    val crHeapThn = current
    current = crHeapOrig
    lastHeld.clear(); lastHeld ++= lastHeldOrig
    val elsAxs = lowerSeqn(i.els)
    val crHeapEls = current
    val joinFields = receiverFields.filter(f =>
      crHeapThn.ofField(f) != crHeapOrig.ofField(f) || crHeapEls.ofField(f) != crHeapOrig.ofField(f))
    current = crHeapOrig
    advance(joinFields)
    val crHeapJoin = current
    val ifJoinThn = Seqn(
      thnAxs.ss ++ makeIfJoinAxioms(crHeapThn, crHeapJoin, joinFields),
      thnAxs.scopedSeqnDeclarations
    )(thnAxs.pos, thnAxs.info, thnAxs.errT)
    val ifJoinEls = Seqn(
      elsAxs.ss ++ makeIfJoinAxioms(crHeapEls, crHeapJoin, joinFields),
      elsAxs.scopedSeqnDeclarations
    )(elsAxs.pos, elsAxs.info, elsAxs.errT)
    val ifOut = i.copy(
      thn = ifJoinThn,
      els = ifJoinEls
    )(i.pos, MakeInfoPair(i.info, crHeapInfo(crHeapOrig)), i.errT)
    if (condReads.isEmpty) ifOut
    else Seqn(condReads :+ ifOut, Seq())(i.pos, MakeInfoPair(i.info, crHeapInfo(crHeapOrig)), i.errT)
  }

  private def makeIfJoinAxioms(rhCurrMap: CrHeapMap, rhNextMap: CrHeapMap, joinFields: Set[String]): Seq[Stmt] = {
    def ffAxs(rh: CrHeap, rhNext: CrHeap, crimpADecl: CrimpDecl): Seq[Stmt] = {
      // Extract the crimp Domain type
      val crimpDType = crimpADecl.crimpDType(program)
      val crimpIdxType = crimpADecl.crimpType._1
      val crimpHasID = crimpADecl.hasID

      // Create domain-typed vars for quantification
      val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
      val forallVarR = LocalVarDecl("__r", crimpDType)()
      val forallVarFS = LocalVarDecl("__fs", SetType(crimpIdxType))()
      val forallVarIdx = LocalVarDecl("__i", crimpIdxType)()
      val fidGuard = helper.fieldIDGuard(forallVarR.localVar, crimpADecl.fieldName)(crimpHasID)

      val currCrimpTerm = helper.crimpApply(forallVarF.localVar, rh.toExp, forallVarR.localVar, forallVarFS.localVar)(crimpHasID)
      val nextCrimpTerm = helper.crimpApply(forallVarF.localVar, rhNext.toExp, forallVarR.localVar, forallVarFS.localVar)(crimpHasID)
      val eqCrimp = Assume(
        Forall(
          Seq(forallVarF, forallVarR, forallVarFS),
          // Also triggered on the join side, so that terms created after the join (e.g. postconditions) reach the branch.
          Seq(Trigger(Seq(currCrimpTerm))(), Trigger(Seq(nextCrimpTerm))()),
          Implies(fidGuard, EqCmp(currCrimpTerm, nextCrimpTerm)())()
        )()
      )()

      val currCrHeapElemTerm = helper.crHeapElemApplyTo(
        rh.toExp,
        forallVarR.localVar,
        forallVarIdx.localVar
      )(crimpHasID)
      val nextCrHeapElemTerm = helper.crHeapElemApplyTo(
        rhNext.toExp,
        forallVarR.localVar,
        forallVarIdx.localVar
      )(crimpHasID)
      val eqCrHeapElem = Assume(
        Forall(
          Seq(forallVarR, forallVarIdx),
          Seq(Trigger(Seq(currCrHeapElemTerm))(), Trigger(Seq(nextCrHeapElemTerm))()),
          Implies(fidGuard, EqCmp(currCrHeapElemTerm, nextCrHeapElemTerm)())()
        )()
      )()

      Seq(eqCrimp, eqCrHeapElem)
    }

    extLinks(rhCurrMap, rhNextMap, joinFields) ++ joinFields.toSeq.sorted.flatMap(f =>
      declsOver(f).flatMap(crimpDecl => ffAxs(rhCurrMap.ofField(f), rhNextMap.ofField(f), crimpDecl)))
  }

  // Symbolic state (crHeap) is not well-defined at entry.
  // We manually convert the invariant conjuncts containing crimp terms (they must be pure):
  //   - Add Assert prior to the while statement, and at the end of the while body.
  //   - Add Assume at the start of the while body and immediately after the while statement.
  private def whileCrHeapFlattenInvariants(w: While): Seqn = {
    val condErrT = ErrTrafo({ case InhaleFailed(_, reason, cached) => WhileFailed(w.cond, reason, cached) })
    // Split each invariant into its top-level conjuncts; those with a crimp are taken out of the loop's invariants.
    val splitInvs = w.invs.map(inv => (inv, conjuncts(inv).partition(hasCrimp)))
    val invsWithCrimp = splitInvs.flatMap(_._2._1)
    val invsWithoutCrimp = splitInvs.flatMap {
      case (inv, (Seq(), _)) => Some(inv)
      case (_, (_, Seq())) => None
      case (inv, (_, rest)) => Some(rest.reduceRight[Exp]((a, b) => And(a, b)(inv.pos, inv.info, inv.errT)))
    }
    invsWithCrimp.filterNot(Expressions.isPure).foreach(c =>
      reportError(ConsistencyError("crimp: a loop invariant that contains a crimp must be pure", c.pos)))

    def foldInvsAssert(rh: CrHeapMap) = invsWithCrimp.foldLeft[Seq[Stmt]](Seq())((ss, inv) =>
      ss :+ Assert(inv)(w.pos, MakeInfoPair(w.info, crHeapInfo(rh)), w.errT))
    def foldInvsAssume(rh: CrHeapMap) = invsWithCrimp.foldLeft[Seq[Stmt]](Seq())((ss, inv) =>
      ss :+ Assume(inv)(w.pos, MakeInfoPair(w.info, crHeapInfo(rh)), w.errT))

    val loopFields = w.invs.flatMap(helper.footprintFields).toSet ++ helper.modifiedFields(w.body)
    val crHeapOrig = advance(loopFields)
    val crHeapOnEntry = current
    val wBodyRec: Seqn = lowerSeqn(w.body)
    val crHeapEnd = current
    // Every field the body advances must be one the loop head advanced (the loop keeps the others across the back edge).
    val escaped = receiverFields.filter(f => !loopFields.contains(f) && crHeapEnd.ofField(f) != crHeapOnEntry.ofField(f))
    if (escaped.nonEmpty)
      reportError(ConsistencyError(s"crimp: internal error: a loop body in method $methodName advances the " +
        s"indices of field(s) ${escaped.toSeq.sorted.mkString(", ")} outside the loop's footprint", w.pos))
    val exitCond: Seq[Stmt] =
      if (hasCrimp(w.cond))
        Seq(Assume(Not(w.cond)(w.cond.pos, w.cond.info, w.cond.errT))(w.pos, MakeInfoPair(w.info, crHeapInfo(crHeapEnd)), w.errT))
      else Seq()
    Seqn(
      foldInvsAssert(crHeapOrig) ++
        Seq(
          w.copy(
            body = Seqn(
              foldInvsAssume(crHeapOnEntry) ++
              generateCondReadAxioms(w.cond, crHeapOnEntry, condErrT) ++
              wBodyRec.ss ++
              foldInvsAssert(crHeapEnd),
              wBodyRec.scopedSeqnDeclarations
            )(wBodyRec.pos, wBodyRec.info, wBodyRec.errT),
            invs = invsWithoutCrimp
          )(w.pos, MakeInfoPair(w.info, crHeapInfo(crHeapOnEntry)), w.errT)
        ) ++
        foldInvsAssume(crHeapEnd) ++
        exitCond ++
        generateCondReadAxioms(w.cond, crHeapEnd, condErrT),
      Seq()
    )(w.pos, MakeInfoPair(w.info, crHeapInfo(crHeapOrig)), w.errT)
  }

  /** The field reads of a condition, each with the guard under which Viper evaluates it]
   * TODO: reads under a quantifier or let, inside unfolding/applying, inside old(..)/old[L](..) (another state), and
    * the locations of perm(..), forperm and accessibility predicates, which are not reads. */
  private def guardedReads(e: Exp, guard: Seq[Exp]): Seq[(Seq[Exp], FieldAccess)] = e match {
    case And(l, r) => guardedReads(l, guard) ++ guardedReads(r, guard :+ l)
    case Or(l, r) => guardedReads(l, guard) ++ guardedReads(r, guard :+ Not(l)(l.pos))
    case Implies(l, r) => guardedReads(l, guard) ++ guardedReads(r, guard :+ l)
    case CondExp(c, t, f) =>
      guardedReads(c, guard) ++ guardedReads(t, guard :+ c) ++ guardedReads(f, guard :+ Not(c)(c.pos))
    case _: QuantifiedExp | _: Let | _: Unfolding | _: Applying | _: Old | _: LabelledOld | _: CurrentPerm |
         _: ForPerm | _: AccessPredicate => Seq()
    case fa: FieldAccess => guardedReads(fa.rcv, guard) :+ ((guard, fa))
    case _ => e.subnodes.collect { case se: Exp => se }.flatMap(guardedReads(_, guard))
  }

  /** The read axioms (generateHeapReadAxiomPerCrimp) of the field reads of an if or loop condition, at indices `crh`. 
    * The axioms of a read are guarded by its conditions, so that they are well-defined */
  private def generateCondReadAxioms(cond: Exp, crh: CrHeapMap, errT: ErrorTrafo): Seq[Stmt] = {
    val reads = guardedReads(cond, Seq()).filter { case (_, r) => declsOver(r.field.name).nonEmpty }
    val axioms = reads.groupBy(_._2).toSeq.sortBy(_._1.toString).flatMap { case (read, occurrences) =>
      val guard: Option[Exp] =
        if (occurrences.exists(_._1.isEmpty)) None
        else Some(occurrences.map(_._1.reduceLeft[Exp](And(_, _)())).distinct.reduceLeft[Exp](Or(_, _)()))
      declsOver(read.field.name).flatMap(rd => generateHeapReadAxiomPerCrimp(rd, read.rcv, crh.ofField(rd.fieldName)))
        .map {
          case a: Assume => Assume(guard.fold(a.exp)(g => Implies(g, a.exp)()))(cond.pos, a.info, errT)
          case s => s
        }
    }
    if (axioms.isEmpty) Seq() else Seq(tagged(Seqn(axioms, Seq())(), crh))
  }

  private def conjuncts(e: Exp): Seq[Exp] = e match {
    case And(l, r) => conjuncts(l) ++ conjuncts(r)
    case _ => Seq(e)
  }

  private def hasCrimp(n: Node): Boolean = InlineAxiomGenerator.hasCrimp(n)

  def convertMethodToInhaleExhale(methodCall: MethodCall): Seqn = {
    //    val methodCall = mc.copy()(mc.pos, mc.info, mc.errT)
    // Get method declaration
    val oldLabel = getUniqueLabelMethod
    val methodDecl = program.findMethod(methodCall.methodName)
    //    val methodDecl = md.copy()(mc.pos, mc.info, mc.errT)

    // LocalVarsDecls for temporary return values
    val returnDecls = methodDecl.formalReturns.map(r =>
      LocalVarDecl(r.name ++ "_out_" ++ getUniqueIDMethodOut, r.typ)(r.pos, r.info, r.errT)
    )

    // LocalVars for temporary return values
    val returnDeclVars = methodDecl.formalReturns.zip(returnDecls).map{
      case (old, newVar) => newVar.localVar.copy()(old.pos, old.info, old.errT + NodeTrafo(old.localVar))
    }
    // val returnDeclVars = returnDecls.map(td => td.localVar)

    // Viper evaluates a call's arguments once, in the state before the call. An argument other than a local variable or
    // a literal (a field read, a function application, a crimp, old(..), ...) is therefore assigned to a fresh local
    // before the call's label, and the specification is instantiated with that local
    val argBindings = methodDecl.formalArgs.zip(methodCall.args).map {
      case (_, a@(_: LocalVar | _: Literal)) => (a, None)
      case (formal, a) =>
        val decl = LocalVarDecl(formal.name ++ "_arg_" ++ getUniqueIDMethodArg, formal.typ)(a.pos, a.info, a.errT)
        val assign = LocalVarAssign(decl.localVar, a)(a.pos, NoInfo, ErrTrafo({
          case errors.AssignmentFailed(_, reason, cached) => errors.CallFailed(methodCall, reason, cached)
        }))
        (decl.localVar, Some((decl, assign)))
    }
    val argValues = argBindings.map(_._1)
    val argDecls = argBindings.flatMap(_._2.map(_._1))
    val argAssigns = argBindings.flatMap(_._2.map(_._2))

    // Replace precondition and postcondition variables with actual arguments and return values. The values only
    // contain local variables; a bound variable of the specification with one of their names is renamed.
    val values = argValues ++ returnDeclVars
    val valueNames = values.flatMap(_.deepCollect { case l: LocalVar => l.name }).toSet
    val newPres = methodDecl.pres.map(p => Expressions.instantiateVariables(p,
      methodDecl.formalArgs ++ methodDecl.formalReturns,
      values,
      valueNames
    ))
    val newPost = methodDecl.posts.map(p => Expressions.instantiateVariables(p,
      methodDecl.formalArgs ++ methodDecl.formalReturns,
      values,
      valueNames
    ))

    // Create one exhale of all preconditions and one inhale of all postconditions, as Viper's call does: all their
    // crimps are evaluated in the state before the call and in the state after it, respectively.
    val exhales = if (newPres.isEmpty) Seq() else Seq(Exhale(helper.foldConj(newPres))(methodCall.pos, NoInfo,
      ErrTrafo({
        case ExhaleFailed(_, reason, cached) =>
          errors.PreconditionInCallFalse(methodCall, reason, cached)
      })
    ))

    // Todo, remove the inhale failure, and make the error disappear (Carbon)
    // For silicon this is correct
    var inhales = if (newPost.isEmpty) Seq() else Seq(Inhale(helper.foldConj(newPost))(methodCall.pos, NoInfo,
      ErrTrafo({
        case InhaleFailed(_, reason, cached) =>
          errors.CallFailed(methodCall, reason, cached)
      }))
    )

    // change all old to the correct label
    inhales = inhales.map(inhale => inhale.transform({
      case old: Old => LabelledOld(old.exp, oldLabel.name)(old.pos, old.info, old.errT)
    }))

    // Assign targets with temporary return values
    val assigns = methodCall.targets.zip(returnDeclVars).map(
      t => AbstractAssign(t._1, t._2)(t._1.pos, t._1.info, t._1.errT)
    )
    Seqn(
      argAssigns ++ Seq(oldLabel) ++ exhales ++ inhales ++ assigns,
      argDecls ++ returnDecls
    )(methodCall.pos, methodCall.info, methodCall.errT)
  }

  // Exhale of an assertion whose footprint contains fields of receivers: a label names the state before the exhale;
  // the receivers over those fields advance, linked by lostP and the exhale axioms of each of their declarations.
  // Viper evaluates the exhaled assertion in the state before the exhale: its crimps are at the indices before it.
  def generateExhaleAxioms(e: Exhale): Stmt = {
    val fields = helper.footprintFields(e.exp).intersect(receiverFields)
    if (fields.isEmpty) return tagged(e, current)
    val preLabel = freshPreLabel()
    val lastHeldPre = fields.map(f => f -> lastHeld(f)).toMap
    val crHeapPre = advance(fields)
    val crHeapPost = current
    lastHeld ++= lastHeldPre
    val links = extLinks(crHeapPre, crHeapPost, fields)
    val declaredLost = mutable.Map[String, LocalVarDecl]()
    val exhaleAxioms = fields.toSeq.sorted.flatMap(f => declsOver(f).map(crimpDecl =>
      generateExhaleAxiomsPerCrimp(crimpDecl, declaredLost, crHeapPre.ofField(f), crHeapPost.ofField(f), preLabel.name)))
    val allLostVars = exhaleAxioms.flatMap(e => e.scopedSeqnDeclarations)
    val allExhaleAxioms = exhaleAxioms.flatMap(e => e.ss)
    val infoPair = MakeInfoPair(e.info, crHeapInfo(crHeapPre))
    Seqn(preLabel +: e +: (links ++ allExhaleAxioms), allLostVars)(e.pos, infoPair, e.errT)
  }

  // Inhale (and assume, and allocation, which inhales the new object's fields) of an assertion whose footprint contains
  // fields of receivers: as for exhale, with gainedP and the inhale axioms. The inhaled assertion describes the state
  // after the inhale: its crimps are at the indices after it.
  def generateInhaleAxioms(i: Stmt, footprintOf: Node): Stmt = {
    val footprint = footprintOf match {
      case n: NewStmt => n.fields.map(_.name).toSet
      case e => helper.footprintFields(e)
    }
    val fields = footprint.intersect(receiverFields)
    if (fields.isEmpty) return tagged(i, current)
    val preLabel = freshPreLabel()
    val lastHeldPre = fields.map(f => f -> lastHeld(f)).toMap
    val crHeapPre = advance(fields)
    val crHeapPost = current
    val links = extLinks(crHeapPre, crHeapPost, fields,
      fields.toSeq.sorted.map(f => (lastHeldPre(f), crHeapPost.ofField(f))))
    val declaredGained = mutable.Map[String, LocalVarDecl]()
    val inhaleAxioms = fields.toSeq.sorted.flatMap(f => declsOver(f).map(crimpDecl =>
      generateInhaleAxiomsPerCrimp(crimpDecl, declaredGained, crHeapPre.ofField(f), crHeapPost.ofField(f), preLabel.name)))
    val allGainedVars = inhaleAxioms.flatMap(i => i.scopedSeqnDeclarations)
    val allInhaleAxioms = inhaleAxioms.flatMap(i => i.ss)
    val infoPair = MakeInfoPair(i.info, crHeapInfo(if (i.isInstanceOf[NewStmt]) crHeapPre else crHeapPost))
    i match {
      case _: NewStmt =>
        Seqn(Seq(preLabel, i, Seqn(links ++ allInhaleAxioms, allGainedVars)(i.pos)), Seq())(i.pos, infoPair, i.errT)
      case _ =>
        Seqn(preLabel +: i +: (links ++ allInhaleAxioms), allGainedVars)(i.pos, infoPair, i.errT)
    }
  }

  // A write to a field without receivers advances nothing, otherwise the receivers over the field advance
  def generateHeapWriteAxioms(writeStmt: FieldAssign): Stmt = {
    val field = writeStmt.lhs.field.name
    if (!receiverFields.contains(field)) return tagged(writeStmt, current)
    val crHeapPre = advance(Set(field))
    val crHeapPost = current
    val out = declsOver(field).flatMap(crimpDecl =>
      generateHeapWriteAxiomPerCrimp(crimpDecl, writeStmt.lhs.rcv, writeStmt.rhs,
        crHeapPre.ofField(field), crHeapPost.ofField(field)))
    val infoPair = MakeInfoPair(writeStmt.info, crHeapInfo(crHeapPre))
    Seqn((extLinks(crHeapPre, crHeapPost, Seq(field)) ++ out) :+ writeStmt, Seq())(writeStmt.pos, infoPair, writeStmt.errT)
  }

  def generateHeapReadAxioms(readStmt: Stmt, crHeap: CrHeapMap): Stmt = {
    var accLHS = Set[FieldAccess]()
    val relevantPart: Node = readStmt match {
      case w: While =>
        w.copy(body = Seqn(Seq(), Seq())())(w.pos, w.info, w.errT)
      case i: If =>
        i.copy(thn = Seqn(Seq(), Seq())(), els = Seqn(Seq(), Seq())())(i.pos, i.info, i.errT)
      case out@Seqn(_, _) =>
        return out
      case a: FieldAssign =>
        accLHS = accLHS + a.lhs
        a.rhs
      case _ => readStmt
    }

    // These reads cannot contained quantified vars
    val allQuantifiedVars = relevantPart.deepCollect({
      case qe: QuantifiedExp => qe.variables
    }).flatten

    // TODO: remove stuff in accessibility predicate TOO!!
    val ignoreAcc = relevantPart.deepCollect({
      case acc: FieldAccessPredicate => acc.loc
    })

    val allReads = relevantPart.deepCollect({
      case fieldAccess: FieldAccess => fieldAccess
    })

    // Filters things in ignoreAcc, using reference equality, then convert to Set
//    var reads = allReads.filterNot(r => ignoreAcc.exists(p => p eq r)).toSet
    var reads = allReads.filterNot(r => allQuantifiedVars.exists(p =>  r.contains(p.localVar))).toSet
    reads = reads -- accLHS // remove all reads with quantified var

    val readStmtWcrHeap = tagged(readStmt, crHeap)

    if (reads.isEmpty) {
      return readStmtWcrHeap
    }

    val crimpAndFields = reads.toSeq.sortBy(_.toString).flatMap(r => declsOver(r.field.name).map(rd => (rd, r)))
    val out = crimpAndFields.flatMap(crimpAndField =>
      generateHeapReadAxiomPerCrimp(crimpAndField._1, crimpAndField._2.rcv, crHeap.ofField(crimpAndField._1.fieldName))
    )
    Seqn(readStmtWcrHeap +: out, Seq())(readStmtWcrHeap.pos, readStmtWcrHeap.info, readStmtWcrHeap.errT)
  }

  // Write axioms for one declaration over the written field, from index crhOld (before) to crhNew (after):
  //   - decomposition of each crimp at the witness index, and framing of the rest of the filter;
  //     the witness has the location's old value before the write and the written value after it
  //   - every held index whose location is not the written one keeps its value.
  private def generateHeapWriteAxiomPerCrimp(crimpADecl: CrimpDecl, writeTo: Exp, writeExp: Exp,
                                             crhOld: CrHeap, crhNew: CrHeap): Seq[Stmt] = {
    val field = program.findField(crimpADecl.fieldName)
    // Extract the crimp Domain type
    val crimpDType = crimpADecl.crimpDType(program)
    val recvDType = crimpADecl.crimpDRecvType(program)
    val crimpIdxType = crimpADecl.crimpType._1
    val crimpHasID = crimpADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )

    // Crimp var declaration
    val forallVarR = LocalVarDecl("__r", crimpDType)()
    val crimpVar = forallVarR.localVar
    // Every axiom below quantifies over crimps __r; it is about field `field` only.
    val fidGuard = helper.fieldIDGuard(crimpVar, field.name)(crimpHasID)

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(crimpIdxType))()
    var filterVar = forallVarFS.localVar

    val frGood = helper.filterReceiverGood(filterVar, crimpVar)(crimpHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, crimpVar)(crimpHasID)
    val fAccess = helper.forallFilterHaveSomeAccess(filterVar, crimpVar, field.name, None)(crimpHasID)

    val receiverApp = helper.getReceiverApply(crimpVar)(crimpHasID)

    val triggerOld = Trigger(Seq(helper.crimpApply(sFuel, crhOld.toExp, crimpVar, filterVar)(crimpHasID)))()
    val triggerNew = Trigger(Seq(helper.crimpApply(sFuel, crhNew.toExp, crimpVar, filterVar)(crimpHasID)))()

    // The witness of __fs at the written location: the index of __fs that reaches it, if there is one
    val witness = helper.preimgElemApply(crimpVar, filterVar, writeTo)(crimpHasID)
    val witnessInFs = helper.witnessReaches(witness, filterVar, crimpVar, writeTo)(crimpHasID)

    val triggerDeleteKeyOld = helper.trigDelKeyApply(sFuel, crhOld.toExp, crimpVar, filterVar, witness)(crimpHasID)
    val triggerDeleteKeyNew = helper.trigDelKeyApply(sFuel, crhNew.toExp, crimpVar, filterVar, witness)(crimpHasID)

    val setDeleteFSWitness = helper.applyDomainFunc(
      DomainsGenerator.setDeleteKey,
      Seq(filterVar, ExplicitSet(Seq(witness))()),
      recvDType.typVarsMap
    )

    val framingEq = EqCmp(
      helper.crimpApply(fuelVar, crhOld.toExp, crimpVar, setDeleteFSWitness)(crimpHasID),
      helper.crimpApply(fuelVar, crhNew.toExp, crimpVar, setDeleteFSWitness)(crimpHasID)
    )()

    val witnessLookup = helper.foldedConjImplies(
      Seq(helper.permNonZeroCmp(witness, crimpVar, field.name)(crimpHasID)),
      Seq(
        EqCmp(
          helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, witness)(crimpHasID),
          helper.mapApplyTo(crimpVar, FieldAccess(writeTo, field)())(crimpHasID)
        )(),
        EqCmp(
          helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, witness)(crimpHasID),
          helper.mapApplyTo(crimpVar, writeExp)(crimpHasID)
        )()
      )
    )

    val crimpFraming = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerOld, triggerNew),
        helper.foldedConjImplies(
          Seq(fidGuard, frGoodOrInj, fAccess),
          Seq(frGood, triggerDeleteKeyOld, triggerDeleteKeyNew, framingEq, Implies(witnessInFs, witnessLookup)())
        )
      )()
    )()

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", crimpIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      recvDType.typVarsMap
    )
    val notWritten = NeCmp(receiverAppIdx, writeTo)()

    val lookupUnmodified = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Implies(fidGuard, Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID)))(),
            Trigger(Seq(helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, idxVar)(crimpHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(notWritten, helper.permNonZeroCmp(idxVar, crimpVar, field.name)(crimpHasID)),
            Seq(
              notWritten,
              EqCmp(
                helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID),
                helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID)
              )(),
              EqCmp(
                helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, idxVar)(crimpHasID),
                helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID)
              )()
            ),
          )
        )())()
      )()
    )()

    Seq(crimpFraming, lookupUnmodified)
  }

  // Read axioms for one declaration over the read field, at index crh:
  //   - decomposition of each crimp at the witness index; it has the location's value;
  //   - every held index has the value of its location.
  private def generateHeapReadAxiomPerCrimp(crimpADecl: CrimpDecl, readFrom: Exp, crh: CrHeap) : Seq[Stmt] = {
    val field = program.findField(crimpADecl.fieldName)

    // Extract the crimp Domain type
    val crimpDType = crimpADecl.crimpDType(program)
    val recvDType = crimpADecl.crimpDRecvType(program)
    val crimpIdxType = crimpADecl.crimpType._1
    val crimpHasID = crimpADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )

    // Crimp var declaration
    val forallVarR = LocalVarDecl("__r", crimpDType)()
    val crimpVar = forallVarR.localVar
    // Every axiom below quantifies over crimps __r; it is about field `field` only.
    val fidGuard = helper.fieldIDGuard(crimpVar, field.name)(crimpHasID)

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(crimpIdxType))()
    val filterVar = forallVarFS.localVar

    val fRGood = helper.filterReceiverGood(filterVar, crimpVar)(crimpHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, crimpVar)(crimpHasID)
    val fAccess = helper.forallFilterHaveSomeAccess(filterVar, crimpVar, field.name, None)(crimpHasID)

    val receiverApp = helper.getReceiverApply(crimpVar)(crimpHasID)
    val trigger = Trigger(Seq(helper.crimpApply(sFuel, crh.toExp, crimpVar, filterVar)(crimpHasID)))()

    // The witness of __fs at the read location: the index of __fs that reaches it, if there is one
    val witness = helper.preimgElemApply(crimpVar, filterVar, readFrom)(crimpHasID)
    val witnessInFs = helper.witnessReaches(witness, filterVar, crimpVar, readFrom)(crimpHasID)

    val triggerDeleteKey = helper.trigDelKeyApply(sFuel, crh.toExp, crimpVar, filterVar, witness)(crimpHasID)
    val witnessLookup = helper.foldedConjImplies(
      Seq(helper.permNonZeroCmp(witness, crimpVar, field.name)(crimpHasID)),
      Seq(
        EqCmp(
          helper.crHeapElemApplyTo(crh.toExp, crimpVar, witness)(crimpHasID),
          helper.mapApplyTo(crimpVar, FieldAccess(readFrom, field)())(crimpHasID)
        )()
      )
    )

    val crimpDelKey = Assume(
        Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(trigger),
        helper.foldedConjImplies(
          Seq(fidGuard, frGoodOrInj, fAccess),
          Seq(fRGood, triggerDeleteKey, Implies(witnessInFs, witnessLookup)())
        )
      )()
    )()

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", crimpIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      recvDType.typVarsMap
    )

    val lookupUnread = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Implies(fidGuard, Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.crHeapElemApplyTo(crh.toExp, crimpVar, idxVar)(crimpHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(helper.permNonZeroCmp(idxVar, crimpVar, field.name)(crimpHasID)),
            Seq(
              EqCmp(
                helper.crHeapElemApplyTo(crh.toExp, crimpVar, idxVar)(crimpHasID),
                helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID)
              )()
            ),
          )
        )())()
      )()
    )()

    Seq(crimpDelKey, lookupUnread)
  }

  // Exhale axioms for one declaration over an exhaled field, from index crhOld to crhNew
  private def generateExhaleAxiomsPerCrimp(crimpADecl: CrimpDecl, declaredLosts: mutable.Map[String, LocalVarDecl],
                                            crhOld: CrHeap,crhNew: CrHeap, oldLabel: String): Seqn = {
    val field = program.findField(crimpADecl.fieldName)

    // Find if lostP already defined for this field
    val alreadyDeclaredLost = declaredLosts.get(field.name)
    alreadyDeclaredLost match {
      // If already defined, just generate exhale axiom
      case Some(declared) =>
        val mainAxiom = mainExhaleAxioms(crimpADecl, declared.localVar, crhOld,crhNew, oldLabel)
        Seqn(mainAxiom, Seq())()
      //  If not defined, generate lostP and exhale axiom
      case None =>
        val declareLost = LocalVarDecl(s"lostP_${field.name}_p$uniqueLabelPre", SetType(Ref))()
        // Add this to the map
        declaredLosts.put(field.name, declareLost)
        //Forall(variables: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
        val forallVars = LocalVarDecl("__pElem", Ref)()
        val forallTriggers = Trigger(Seq(AnySetContains(forallVars.localVar, declareLost.localVar)()))()
        //var lostP_val : Set[Ref]
        //  assume forall iP : Ref:: {iP in lostP_val}
        //    iP in lostP_val <==> (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        //perm(iP.val)
        val insidePerm = CurrentPerm(FieldAccess(forallVars.localVar, field)())()
        val oldExp = LabelledOld(insidePerm, oldLabel)()
        // (perm(iP.val) != write)
        val permNotWrite = EqCmp(insidePerm, NoPerm()())()
        // old[l0](perm(iP.val) == write)
        val permOldWrite = GtCmp(oldExp, NoPerm()())()
        // (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        val permsConj = And(permNotWrite, permOldWrite)()
        // iP in lostP_val <==> (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        val forallBody = EqCmp(AnySetContains(forallVars.localVar, declareLost.localVar)(), permsConj)()
        // forall iP : Ref:: {iP in lostP_val} ...
        val lostAxiom = Assume(Forall(Seq(forallVars), Seq(forallTriggers), forallBody)())()
        val mainAxioms = mainExhaleAxioms(crimpADecl, declareLost.localVar, crhOld,crhNew, oldLabel)

        Seqn(lostAxiom +: mainAxioms, Seq(declareLost))()
    }
  }

  private def mainExhaleAxioms(crimpADecl: CrimpDecl, lostPVal: LocalVar,
                               crhOld: CrHeap,crhNew: CrHeap, oldLabel: String): Seq[Stmt] = {
    val field = program.findField(crimpADecl.fieldName)

    // Extract the crimp Domain type
    val crimpDType = crimpADecl.crimpDType(program)
    val recvDType = crimpADecl.crimpDRecvType(program)
    val crimpIdxType = crimpADecl.crimpType._1
    val crimpHasID = crimpADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )


    // Crimp var declaration
    val forallVarR = LocalVarDecl("__r", crimpDType)()
    val crimpVar = forallVarR.localVar
    // Every axiom below quantifies over crimps __r; it is about field `field` only.
    val fidGuard = helper.fieldIDGuard(crimpVar, field.name)(crimpHasID)

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(crimpIdxType))()
    val filterVar = forallVarFS.localVar

    val triggerOld = Trigger(Seq(helper.crimpApply(sFuel, crhOld.toExp, crimpVar, filterVar)(crimpHasID)))()
    val triggerNew = Trigger(Seq(helper.crimpApply(sFuel,crhNew.toExp, crimpVar, filterVar)(crimpHasID)))()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(filterVar, crimpVar)(crimpHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, crimpVar)(crimpHasID)
    // Have access to the big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      crimpVar, field.name, Some(oldLabel))(crimpHasID)
    // filterNotLost: __fs without the index footprint of the lost locations (the preimage of lostP)
    val filterNotLostApplied = helper.subsetNotInRefs(filterVar, crimpVar, lostPVal)(crimpHasID)
    // Have access to the remaining filter in new state
    val forallNewStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotLostApplied,
      crimpVar, field.name, None)(crimpHasID)
    // Have access to big filter in new
    val forallNewHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      crimpVar, field.name, None)(crimpHasID)

    // ---------------Making the RHS---------------
    val triggerDeleteBlockOld = helper.trigDelBlockApply(
      sFuel,
      crhOld.toExp,
      crimpVar,
      filterVar,
      filterNotLostApplied
    )(crimpHasID)

    val dummyApplyNew = helper.crimpDummyApply(fuelVar,crhNew.toExp, crimpVar, filterNotLostApplied)(crimpHasID)

    val decompFramingEq = EqCmp(
      helper.crimpApply(fuelVar, crhOld.toExp, crimpVar, filterNotLostApplied)(crimpHasID),
      helper.crimpApply(fuelVar,crhNew.toExp, crimpVar, filterNotLostApplied)(crimpHasID)
    )()

    val crimpDecompOld = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerOld),
        helper.foldedConjImplies(
          Seq(fidGuard, frGoodOrInj, forallOldHasPerm, forallNewStillHasPerm),
          Seq(frGood, triggerDeleteBlockOld, dummyApplyNew, decompFramingEq)
        )
      )()
    )()

    val fsPropSubsetNotLost = And(
      Not(EqCmp(filterVar, EmptySet(crimpIdxType)())())(),
      AnySetSubset(filterVar, filterNotLostApplied)()
    )()
    val dummyApplyOld = helper.crimpDummyApply(fuelVar, crhOld.toExp, crimpVar, filterVar)(crimpHasID)
    val newFramingEq = EqCmp(
      helper.crimpApply(fuelVar, crhOld.toExp, crimpVar, filterVar)(crimpHasID),
      helper.crimpApply(fuelVar,crhNew.toExp, crimpVar, filterVar)(crimpHasID)
    )()

    val crimpFramingNew = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerNew),
        helper.foldedConjImplies(
          Seq(fidGuard, frGoodOrInj, forallOldHasPerm, forallNewHasPerm, fsPropSubsetNotLost),
          Seq(frGood, dummyApplyOld, newFramingEq)
        )
      )()
    )()

    val receiverApp = helper.getReceiverApply(crimpVar)(crimpHasID)

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", crimpIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      recvDType.typVarsMap
    )


    val idxNotInRefs = helper.applyDomainFunc(
      DomainsGenerator.idxNotInRefsKey,
      Seq(idxVar, receiverApp, lostPVal),
      recvDType.typVarsMap
    )

    val lookupInOldState = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Implies(fidGuard, Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, crimpVar, field.name)(crimpHasID),
                oldLabel
              )()
            ),
            Seq(
              EqCmp(
                helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID),
                LabelledOld(
                  helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID),
                  oldLabel
                )()
              )()
            ),
          )
        )())()
      )()
    )()

    val lookupUnmodified = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Implies(fidGuard, Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID)))(),
            Trigger(Seq(helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, idxVar)(crimpHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(idxNotInRefs, helper.permNonZeroCmp(idxVar, crimpVar, field.name)(crimpHasID)),
            Seq(
              idxNotInRefs,
              EqCmp(
                helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID),
                helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID)
              )(),
              EqCmp(
                helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, idxVar)(crimpHasID),
                helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID)
              )()
            ),
          )
        )())()
      )()
    )()

    Seq(crimpDecompOld, crimpFramingNew, lookupInOldState, lookupUnmodified)
  }

  // Inhale axioms for one declaration over an inhaled field, from index crhOld to crhNew
  private def generateInhaleAxiomsPerCrimp(crimpADecl: CrimpDecl, declaredGains: mutable.Map[String, LocalVarDecl],
                                            crhOld: CrHeap,crhNew: CrHeap, oldLabel: String): Seqn = {
    val field = program.findField(crimpADecl.fieldName)

    // Find if gainedP already defined for this field
    val alreadyDeclaredGained = declaredGains.get(field.name)
    alreadyDeclaredGained match {
      // If already defined, just generate inhale axioms
      case Some(declared) =>
        val mainAxiom = mainInhaleAxioms(crimpADecl, declared.localVar, crhOld,crhNew, oldLabel)
        Seqn(mainAxiom, Seq())()
      //  If not defined, generate gainedP and inhale axioms
      case None =>
        val declareGained = LocalVarDecl(s"gainedP_${field.name}_p$uniqueLabelPre", SetType(Ref))()
        // Add this to the map
        declaredGains.put(field.name, declareGained)
        //Forall(variables: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
        val forallVars = LocalVarDecl("__pElem", Ref)()
        val forallTriggers = Trigger(Seq(AnySetContains(forallVars.localVar, declareGained.localVar)()))()
        //var gainedP_Val : Set[Ref]
        //  assume forall iP : Ref:: {iP in lostP_val}
        //    iP in gainedP_Val <==> (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        //perm(iP.val)
        val insidePerm = CurrentPerm(FieldAccess(forallVars.localVar, field)())()
        val oldExp = LabelledOld(insidePerm, oldLabel)()
        // (perm(iP.val) == write)
        val permWrite = GtCmp(insidePerm, NoPerm()())()
        // old[l0](perm(iP.val) != write)
        val permOldNotWrite = EqCmp(oldExp, NoPerm()())()
        // (perm(iP.val) == write) && old[l0](perm(iP.val) != write)
        val permsConj = And(permWrite, permOldNotWrite)()
        // iP in lostP_val <==> (perm(iP.val) == write) && old[l0](perm(iP.val) != write)
        val forallBody = EqCmp(AnySetContains(forallVars.localVar, declareGained.localVar)(), permsConj)()
        // forall iP : Ref:: {iP in lostP_val} ...
        val lostAxiom = Assume(Forall(Seq(forallVars), Seq(forallTriggers), forallBody)())()
        val mainAxioms = mainInhaleAxioms(crimpADecl, declareGained.localVar, crhOld,crhNew, oldLabel)

        Seqn(lostAxiom +: mainAxioms, Seq(declareGained))()
    }
  }

  private def mainInhaleAxioms(crimpADecl: CrimpDecl, gainedPVal: LocalVar,
                               crhOld: CrHeap, crhNew: CrHeap, oldLabel: String): Seq[Stmt] = {
    val field = program.findField(crimpADecl.fieldName)

    // Extract the crimp Domain type
    val crimpDType = crimpADecl.crimpDType(program)
    val recvDType = crimpADecl.crimpDRecvType(program)
    val crimpIdxType = crimpADecl.crimpType._1
    val crimpHasID = crimpADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )

//    val forallVarRH = LocalVarDecl("__exrh", Int)()

    // Crimp var declaration
    val forallVarR = LocalVarDecl("__r", crimpDType)()
    val crimpVar = forallVarR.localVar
    // Every axiom below quantifies over crimps __r; it is about field `field` only.
    val fidGuard = helper.fieldIDGuard(crimpVar, field.name)(crimpHasID)

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(crimpIdxType))()
    val filterVar = forallVarFS.localVar
//    val forallVarExFS = LocalVarDecl("__exfs", SetType(crimpIdxType))()

    val triggerOld = Trigger(Seq(helper.crimpApply(sFuel, crhOld.toExp, crimpVar, filterVar)(crimpHasID)))()
    val triggerNew = Trigger(Seq(helper.crimpApply(sFuel, crhNew.toExp, crimpVar, filterVar)(crimpHasID)))()

    val receiverApp = helper.getReceiverApply(crimpVar)(crimpHasID)

    // filterNotGained: __fs without the index footprint of the gained locations (the preimage of gainedP)
    val filterNotGainedApplied = helper.applyDomainFunc(
      DomainsGenerator.subsetNotInRefsKey,
      Seq(forallVarFS.localVar, receiverApp, gainedPVal),
      recvDType.typVarsMap
    )

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(filterVar, crimpVar)(crimpHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, crimpVar)(crimpHasID)
    // Have access to the big filter in new
    val forallNewHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      crimpVar, field.name, None)(crimpHasID)
    // Have access to the remaining filter in old state
    val forallOldStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotGainedApplied,
      crimpVar, field.name, Some(oldLabel))(crimpHasID)
    // Have access to big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      crimpVar, field.name, Some(oldLabel))(crimpHasID)

    // ---------------Making the RHS---------------
    val triggerDeleteBlockNew = helper.trigDelBlockApply(
      sFuel,
      crhNew.toExp,
      crimpVar,
      filterVar,
      filterNotGainedApplied
    )(crimpHasID)

    val dummyApplyOld = helper.crimpDummyApply(fuelVar, crhOld.toExp, crimpVar, filterNotGainedApplied)(crimpHasID)

    val decompFramingEq = EqCmp(
      helper.crimpApply(fuelVar, crhOld.toExp, crimpVar, filterNotGainedApplied)(crimpHasID),
      helper.crimpApply(fuelVar, crhNew.toExp, crimpVar, filterNotGainedApplied)(crimpHasID)
    )()

    val crimpDecompNew = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerNew),
        helper.foldedConjImplies(
          Seq(fidGuard, frGoodOrInj, forallNewHasPerm, forallOldStillHasPerm),
          Seq(frGood, triggerDeleteBlockNew, dummyApplyOld, decompFramingEq)
        )
      )()
    )()

    val fsPropSubsetNotGained = And(
      Not(EqCmp(filterVar, EmptySet(crimpIdxType)())())(),
      AnySetSubset(filterVar, filterNotGainedApplied)()
    )()
    val dummyApplyNew = helper.crimpDummyApply(fuelVar, crhNew.toExp, crimpVar, filterVar)(crimpHasID)
    val oldFramingEq = EqCmp(
      helper.crimpApply(fuelVar, crhOld.toExp, crimpVar, filterVar)(crimpHasID),
      helper.crimpApply(fuelVar, crhNew.toExp, crimpVar, filterVar)(crimpHasID)
    )()

    val crimpFramingOld = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerOld),
        helper.foldedConjImplies(
          Seq(fidGuard, frGoodOrInj, forallOldHasPerm, forallNewHasPerm, fsPropSubsetNotGained),
          Seq(frGood, dummyApplyNew, oldFramingEq)
        )
      )()
    )()

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", crimpIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      recvDType.typVarsMap
    )


    val lookupInOldState = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Implies(fidGuard, Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, crimpVar, field.name)(crimpHasID),
                oldLabel
              )()
            ),
            Seq(
              EqCmp(
                helper.crHeapElemApplyTo(crhOld.toExp, crimpVar, idxVar)(crimpHasID),
                LabelledOld(
                  helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID),
                  oldLabel
                )()
              )(),
              EqCmp(
                helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, idxVar)(crimpHasID),
                LabelledOld(
                  helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID),
                  oldLabel
                )()
              )()
            ),
          )
        )())()
      )()
    )()

    val lookupInNewState = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Implies(fidGuard, Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, idxVar)(crimpHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(helper.permNonZeroCmp(idxVar, crimpVar, field.name)(crimpHasID)),
            Seq(
              EqCmp(
                helper.crHeapElemApplyTo(crhNew.toExp, crimpVar, idxVar)(crimpHasID),
                helper.mapApplyTo(crimpVar, FieldAccess(receiverAppIdx, field)())(crimpHasID)
              )()
            ),
          )
        )())()
      )()
    )()

    Seq(crimpDecompNew, crimpFramingOld, lookupInOldState, lookupInNewState)
  }


}

object InlineAxiomGenerator {
  def hasCrimp(n: Node): Boolean = n.existsDefined { case _: CrimpApp => }

  def needsLowering(program: Program, m: Method): Boolean =
    hasCrimp(m) || m.body.exists(_.existsDefined {
      case mc: MethodCall if {
        val callee = program.findMethod(mc.methodName)
        (callee.pres ++ callee.posts).exists(hasCrimp)
      } =>
    })
}
