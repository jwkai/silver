package viper.silver.plugin.hreduce

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.plugin.hreduce.ast.{AReduceApply, AReduceDecl, ARHeap, rHeapInfo}
import viper.silver.plugin.hreduce.util.AxiomHelper
import viper.silver.verifier.errors
import viper.silver.verifier.errors.{ExhaleFailed, InhaleFailed}

import scala.collection.mutable

// TODOS: 1. Count how many inhales to find how many Lost vars we need to declare
// 2. track which Lost Var is related to which inhale

class InlineAxiomGenerator(program: Program, methodName: String) {

  val method: Method = program.findMethod(methodName)
  val helper = new AxiomHelper(program)

  //  val fieldMapToInt = program.fields.zipWithIndex.map(f => (f._1, f._2)).toMap

  val reduceDeclsUsed: Set[AReduceDecl] = {
    method.deepCollect({
      case ca: AReduceApply => ca.reduceFunctionDeclaration
    }).toSet
  }

  private var currentLabelNum = 0
  private var uniqueIDMethodOut = 0
  private var uniqueLabelMethod = 0
  private val userLabelToLabelNum: mutable.Map[String, Int] = mutable.Map()
  //  private var uniqueIDLost = 0

  private def getUniqueIDMethodOut: String = {
    uniqueIDMethodOut += 1
    s"$uniqueIDMethodOut"
  }

  // get unique method label
  private def getUniqueLabelMethod: Label = {
    uniqueLabelMethod += 1
    Label(s"${helper.methodLabelPrefix}l$uniqueLabelMethod", Seq())()
  }

  private def getCurrentLabel: Label = {
    Label(s"${helper.labelPrefix}l$currentLabelNum", Seq())()
  }

  def getCurrentRHeap: ARHeap = {
    ARHeap(currentLabelNum)
  }

  def mapUserLabelToCurrentARHeap(name: String): Option[Int] = {
    userLabelToLabelNum.put(name, currentLabelNum)
  }

  def getARHeapFromUserLabel(name: String): ARHeap = {
    val rHeapLabelNum = userLabelToLabelNum.get(name) match {
      case Some(i) => i
      case None => throw new Exception(s"User-defined label $name not found during fold heap mapping")
    }
    ARHeap(rHeapLabelNum)
  }

  def getOldLabel: Label = {
    Label(s"${helper.labelPrefix}l0", Seq())()
  }

  def getOldRHeap: ARHeap = {
    ARHeap(0)
  }

  private def getLabNumForLost: String = {
    s"l$currentLabelNum"
  }

  private def labelIncrement() : Unit = {
    currentLabelNum += 1
  }

  private def getLastLabel: Label = {
    Label(s"${helper.labelPrefix}l${currentLabelNum-1}", Seq())()
  }

  private def getLastRHeap: ARHeap = {
    ARHeap(currentLabelNum-1)
  }

  // Add axioms for exhales, inhales and heap writes, tracking rHeap insertions
  def addAxiomsToBody(): PartialFunction[Node, Node] = {
    case e: Exhale =>
      if (!helper.checkIfPure(e)) {
        val fields = helper.extractFieldAcc(e)
        generateExhaleAxioms(e, fields)
      } else {
        e.withMeta(e.pos, MakeInfoPair(e.info, rHeapInfo(getCurrentRHeap)), e.errT)
      }
    case i: Inhale =>
      if (!helper.checkIfPure(i)) {
        val fields = helper.extractFieldAcc(i)
        generateInhaleAxioms(i, fields)
      } else {
        i.withMeta(i.pos, MakeInfoPair(i.info, rHeapInfo(getCurrentRHeap)), i.errT)
      }
    case fa: FieldAssign =>
      generateHeapWriteAxioms(fa)
    case l@Label(name, _) =>
      mapUserLabelToCurrentARHeap(name)
      l
    case a: Assert =>
      a.withMeta(a.pos, MakeInfoPair(a.info, rHeapInfo(getCurrentRHeap)), a.errT)
    case a: Assume =>
      a.withMeta(a.pos, MakeInfoPair(a.info, rHeapInfo(getCurrentRHeap)), a.errT)
    case i: If =>
      ifRHeapJoin(i)
    case w: While =>
      whileRHeapFlattenInvariants(w)
  }

  // Add axioms to each branch, "join" branches with next rHeap and triggers
  private def ifRHeapJoin(i: If): Seqn = {
    val rHeapOrig = getCurrentRHeap
    val thnAxs = i.thn.transform(addAxiomsToBody())
    val rHeapThn = getCurrentRHeap
    val elsAxs = i.els.transform(addAxiomsToBody())
    val rHeapEls = getCurrentRHeap
    val ifJoinAx = makeIfJoinAxiom(rHeapThn, rHeapEls)
    Seqn(
      i.copy(
        thn = thnAxs,
        els = elsAxs
      )(i.pos, MakeInfoPair(i.info, rHeapInfo(rHeapOrig)), i.errT)
      +:
      ifJoinAx,
      Seq()
    )(i.pos, MakeInfoPair(i.info, rHeapInfo(rHeapOrig)), i.errT)
  }

  private def makeIfJoinAxiom(rh1: ARHeap, rh2: ARHeap): Seq[Stmt] = {
    labelIncrement()
    val rhJoin = getCurrentRHeap
    val reduceDom = program.findDomain(DomainsGenerator.reduceDKey)
    // Extract the reduce Domain type
    val reduceDType = DomainType(reduceDom, (reduceDom.typVars zip reduceDom.typVars).toMap)
    val reduceIdxType = reduceDom.typVars.head

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()

    // Use primed version so that any "yielded" terms are automatically advanced
    val currReduceTerm1 = helper.reduceApplyPrime(rh1.toExp, reduceVar, forallVarFS.localVar)
    val currReduceTerm2 = helper.reduceApplyPrime(rh2.toExp, reduceVar, forallVarFS.localVar)
    val nextReduceTerm = helper.reduceApply(rhJoin.toExp, reduceVar, forallVarFS.localVar)
    val triggerR1 = Trigger(Seq(currReduceTerm1))()
    val triggerR2 = Trigger(Seq(currReduceTerm2))()

    val eqReduce = Assume(
      Forall(
        Seq(forallVarR, forallVarFS),
        Seq(triggerR1, triggerR2),
        And(
          EqCmp(currReduceTerm1, nextReduceTerm)(),
          EqCmp(currReduceTerm2, nextReduceTerm)(),
        )()
      )()
    )()

    // Use primed version so that any "yielded" terms are automatically advanced
    val currRHeapElemTerm1 = helper.rHeapElemApplyTo(rh1.toExp, reduceVar, forallVarFS.localVar)
    val currRHeapElemTerm2 = helper.rHeapElemApplyTo(rh2.toExp, reduceVar, forallVarFS.localVar)
    val nextRHeapElemTerm = helper.rHeapElemApplyTo(rhJoin.toExp, reduceVar, forallVarFS.localVar)
    val triggerRH1 = Trigger(Seq(currReduceTerm1))()
    val triggerRH2 = Trigger(Seq(currReduceTerm2))()

    val eqRHeapElem = Assume(
      Forall(
        Seq(forallVarR, forallVarFS),
        Seq(triggerRH1, triggerRH2),
        And(
          EqCmp(currRHeapElemTerm1, nextRHeapElemTerm)(),
          EqCmp(currRHeapElemTerm2, nextRHeapElemTerm)(),
        )()
      )()
    )()

    Seq(eqReduce, eqRHeapElem)
  }

  // Symbolic state (rHeap) is not well-defined at entry.
  // We manually convert any invariants containing hreduce terms:
  //   - Add Assert (in old rHeap) prior to the while statement,
  //     and (in current rHeap) the end of the while body.
  //   - Add Assume (in current rHeap) at start of while body
  //     and immediately after the while statement.
  private def whileRHeapFlattenInvariants(w: While): Seqn = {
    val (invsWithReduce, invsWithoutReduce) = w.invs.partition(_.contains[AReduceApply])

    def foldInvsAssert(rh: ARHeap) = invsWithReduce.foldLeft[Seq[Stmt]](Seq())((ss, inv) =>
      ss :+ Assert(inv)(w.pos, MakeInfoPair(w.info, rHeapInfo(rh)), w.errT))
    def foldInvsAssume(rh: ARHeap) = invsWithReduce.foldLeft[Seq[Stmt]](Seq())((ss, inv) =>
      ss :+ Assume(inv)(w.pos, MakeInfoPair(w.info, rHeapInfo(rh)), w.errT))

    val rHeapOrig = getCurrentRHeap
//    val labelOrig = getCurrentLabel
    labelIncrement()
    val rHeapOnEntry = getCurrentRHeap
    val labelOnEntry = getCurrentLabel
    val wBodyRec: Seqn = w.body.transform(addAxiomsToBody())
    Seqn(
      foldInvsAssert(rHeapOrig) ++
        Seq(
          w.copy(
            body = Seqn(
              Seq(labelOnEntry) ++
              foldInvsAssume(rHeapOnEntry) ++
              wBodyRec.ss ++
              foldInvsAssert(getCurrentRHeap),
              wBodyRec.scopedSeqnDeclarations
            )(wBodyRec.pos, wBodyRec.info, wBodyRec.errT),
            invs = invsWithoutReduce
          )(w.pos, MakeInfoPair(w.info, rHeapInfo(rHeapOrig)), w.errT)
        ) ++
        foldInvsAssume(getCurrentRHeap),
      Seq()
    )(w.pos, MakeInfoPair(w.info, rHeapInfo(rHeapOrig)), w.errT)
  }

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

    // Replace precondition and postcondition variables with actual arguments and return values
    val newPres = methodDecl.pres.map(p => Expressions.instantiateVariables(p,
      methodDecl.formalArgs ++ methodDecl.formalReturns,
      methodCall.args ++ returnDeclVars,
      Set()
    ))
    val newPost = methodDecl.posts.map(p => Expressions.instantiateVariables(p,
      methodDecl.formalArgs ++ methodDecl.formalReturns,
      methodCall.args ++ returnDeclVars,
      Set()
    ))

    // Create inhales and exhales
    val exhales = newPres.map(p => Exhale(p)(p.pos, p.info,
      p.errT + ErrTrafo({
        case ExhaleFailed(_, reason, cached) =>
          errors.PreconditionInCallFalse(methodCall, reason, cached)
      })
    ))

    // Todo, remove the inhale failure, and make the error disappear (Carbon)
    // For silicon this is correct
    var inhales = newPost.map(p => Inhale(p)(p.pos, p.info,
      p.errT + ErrTrafo({
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
      Seq(oldLabel) ++ exhales.reverse ++ inhales ++ assigns,
      returnDecls
    )(methodCall.pos, methodCall.info, methodCall.errT)
  }

  def generateExhaleAxioms(e: Exhale, relevantField: Set[Field]): Seqn = {
    labelIncrement()
    val declaredFieldVars = mutable.Set[LocalVarDecl]()
    val relevantReduceDecls = reduceDeclsUsed.toSeq.filter(reduceDecl =>
      relevantField.contains(reduceDecl.findFieldInProgram(program)))
    val exhaleAxioms = relevantReduceDecls.map(reduceDecl => generateExhaleAxiomsPerReduce(reduceDecl, declaredFieldVars))
    val allLostVars = exhaleAxioms.flatMap(e => e.scopedSeqnDeclarations)
    val allExhaleAxioms = exhaleAxioms.flatMap(e => e.ss)
    val infoPair = MakeInfoPair(e.info, rHeapInfo(getCurrentRHeap))
    Seqn(e +: getCurrentLabel +: allExhaleAxioms, allLostVars)(e.pos, infoPair, e.errT)
  }

  def generateInhaleAxioms(i: Inhale, relevantField: Set[Field]): Seqn = {
    labelIncrement()
    val declaredFieldVars = mutable.Set[LocalVarDecl]()
    val relevantReduceDecls = reduceDeclsUsed.toSeq.filter(reduceDecl =>
      relevantField.contains(reduceDecl.findFieldInProgram(program)))
    val inhaleAxioms = relevantReduceDecls.map(reduceDecl => generateInhaleAxiomsPerReduce(reduceDecl, declaredFieldVars))
    val allLostVars = inhaleAxioms.flatMap(i => i.scopedSeqnDeclarations)
    val allInhaleAxioms = inhaleAxioms.flatMap(i => i.ss)
    val infoPair = MakeInfoPair(i.info, rHeapInfo(getCurrentRHeap))
    Seqn(i +: getCurrentLabel +: allInhaleAxioms, allLostVars)(i.pos, infoPair, i.errT)
  }

  def generateHeapWriteAxioms(writeStmt: Stmt): Seqn = {
    labelIncrement()
    val writes = writeStmt.deepCollect({
      case fieldAssign: FieldAssign =>
        fieldAssign
    }).toSet
    val reductionsAndFields = writes.flatMap(w =>
      reduceDeclsUsed.filter(cd => cd.findFieldInProgram(program) == w.lhs.field).zipAll(Seq(),null,w)
    ).toSeq
    val out = reductionsAndFields.flatMap(reduceAndField =>
      generateHeapWriteAxiomPerReduce(reduceAndField._1, reduceAndField._2.lhs.rcv, reduceAndField._2.rhs)
    )

    val infoPair = MakeInfoPair(writeStmt.info, rHeapInfo(getCurrentRHeap))
    Seqn(out :+ writeStmt :+ getCurrentLabel, Seq())(writeStmt.pos, infoPair, writeStmt.errT)
  }

//    def generateHeapReadAxioms(readStmt: Stmt): Stmt = {
//      var accLHS = Set[FieldAccess]()
//      val relevantPart: Node = readStmt match {
//        case w : While =>
//          w.copy(body = Seqn(Seq(), Seq())())(w.pos, w.info, w.errT)
//        case i : If =>
//          i.copy(thn = Seqn(Seq(), Seq())(), els = Seqn(Seq(), Seq())())(i.pos, i.info, i.errT)
//        case out@ Seqn(_, _) =>
//          return out
//        // Do this to ignore LHS in case of a heap write tgt with heap read. Could cause redundancy.
//        case a: FieldAssign =>
//          accLHS = accLHS + a.lhs
//          a.rhs
//        case generated: Assume =>
//          return generated
//        case _ => readStmt
//      }
//
//      // These reads cannot contained quantified vars
//      val allQuantifiedVars = relevantPart.deepCollect({
//        case qe: QuantifiedExp => qe.variables
//      }).flatten
//
//      // TODO: remove stuff in accessibility predicate TOO!!
//      val ignoreAcc = relevantPart.deepCollect({
//        case acc: FieldAccessPredicate => acc.loc
//      })
//
//      val allReads = relevantPart.deepCollect({
//        case fieldAccess: FieldAccess => fieldAccess
//      })
//
//      // Filters things in ignoreAcc, using reference equality, then convert to Set
//      var reads = allReads.filterNot(r => ignoreAcc.exists(p => p eq r)).toSet
//      reads = reads.filterNot(r => allQuantifiedVars.exists(p =>  r.contains(p.localVar)))
//      reads = reads -- accLHS // remove all reads with quantified var
//
//      if (reads.isEmpty) {
//        return readStmt
//      }
//
//      val reduceAndFields = reads.flatMap(r =>
//        reduceDeclsUsed.filter(rd => rd.findFieldInProgram(program) == r.field).zipAll(Seq(), null, r)
//      ).toSeq
//      val out = reduceAndFields.flatMap(reduceAndField =>
//        generateHeapReadAxiomPerReduce(reduceAndField._1, reduceAndField._2.rcv)
//      )
//      Seqn(out :+ readStmt, Seq())(readStmt.pos, readStmt.info, readStmt.errT)
//    }

  private def generateHeapWriteAxiomPerReduce(reduceADecl: AReduceDecl, writeTo: Exp, writeExp: Exp): Seq[Stmt] = {
    val field = program.findField(reduceADecl.fieldName)
    // Extract the reduce Domain type
    val reduceDType = reduceADecl.reduceDType(program)
    val recvDType = reduceADecl.reduceDRecvType(program)
    val reduceIdxType = reduceADecl.reduceType._1

    // rHeap declarations
    val rhOld = getLastRHeap
    val rhNew = getCurrentRHeap

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()

    val frGood = helper.filterReceiverGood(forallVarFS.localVar, reduceVar)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(forallVarFS.localVar, reduceVar)
    val fAccess = helper.forallFilterHaveSomeAccess(forallVarFS.localVar, reduceVar, field.name, None)

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.reduceGetRecvKey,
      Seq(reduceVar),
      reduceDType.typVarsMap
    )

    val trigger1 = Trigger(Seq(helper.reduceApply(rhOld.toExp, reduceVar, forallVarFS.localVar)))()

    val invRecvApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, writeTo),
      recvDType.typVarsMap
    )

    val triggerDeleteKeyNew = helper.applyDomainFunc(
      DomainsGenerator.trigDelKey1Key,
      Seq(helper.reduceApply(rhNew.toExp, reduceVar, forallVarFS.localVar), invRecvApp),
      reduceDType.typVarsMap
    )
    val triggerDeleteKeyOld = helper.applyDomainFunc(
      DomainsGenerator.trigDelKey1Key,
      Seq(helper.reduceApply(rhOld.toExp, reduceVar, forallVarFS.localVar), invRecvApp),
      reduceDType.typVarsMap
    )

    val setDeleteFSInv = helper.applyDomainFunc(
      DomainsGenerator.setDeleteKey,
      Seq(forallVarFS.localVar, ExplicitSet(Seq(invRecvApp))()),
      recvDType.typVarsMap
    )

    val framingEq = EqCmp(
      helper.applyDomainFunc(
        DomainsGenerator.reduceApplyPrimeKey,
        Seq(rhOld.toExp, reduceVar, setDeleteFSInv),
        reduceDType.typVarsMap
      ),
      helper.applyDomainFunc(
        DomainsGenerator.reduceApplyPrimeKey,
        Seq(rhNew.toExp, reduceVar, setDeleteFSInv),
        reduceDType.typVarsMap
      )
    )()

    val reduceFraming = Assume(
      Forall(
        Seq(forallVarR, forallVarFS),
        Seq(trigger1),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, fAccess),
          Seq(frGood, triggerDeleteKeyOld, triggerDeleteKeyNew, framingEq),
        )
      )()
    )()

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", reduceIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      recvDType.typVarsMap
    )

    val lookupUnmodified = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, idxVar)))(),
            Trigger(Seq(helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(NeCmp(idxVar, invRecvApp)(), helper.permNonZeroCmp(idxVar, reduceVar, field.name)),
            Seq(
              NeCmp(idxVar, invRecvApp)(),
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, idxVar),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())
              )(),
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, idxVar),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())
              )()
            ),
          )
        )()
      )()
    )()

    val lookupModified = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        helper.foldedConjImplies(
          Seq(helper.permNonZeroCmp(invRecvApp, reduceVar, field.name)),
          Seq(
            EqCmp(
              helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, invRecvApp),
              helper.mapApplyTo(reduceVar, FieldAccess(writeTo, field)())
            )(),
            EqCmp(
              helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, invRecvApp),
              helper.mapApplyTo(reduceVar, writeExp)
            )()
          )
        )
      )()
    )()

    Seq(reduceFraming, lookupUnmodified, lookupModified)
  }

//    private def generateHeapReadAxiomPerReduce(reduceADecl: AReduceDecl, readFrom: Exp) : Seq[Stmt] = {
//      val field = program.findField(reduceADecl.fieldName)
//
//      // Extract the reduce Domain type
//      val reduceDType = reduceADecl.reduceDType(program)
//      val recvDType = reduceADecl.reduceDRecvType(program)
//      val reduceIdxType = reduceADecl.reduceType._1
//
//      // Reduce var declaration
//      val forallVarR = LocalVarDecl("__r", reduceDType)()
//      val reduceVar = forallVarR.localVar
//
//      // rHeap declaration
//      val rh = getCurrentRHeap
//
//      // Filter Var declaration
//      val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()
//      val fRGood = helper.filterReceiverGood(forallVarFS.localVar, reduceVar)
//      val fAccess = helper.forallFilterHaveSomeAccess(forallVarFS.localVar, reduceVar, field.name, None)
//
//      val receiverApp = helper.applyDomainFunc(
//        DomainsGenerator.reduceGetRecvKey,
//        Seq(reduceVar),
//        reduceDType.typVarsMap
//      )
//
//      val trigger = Trigger(Seq(helper.reduceApply(rh, reduceVar, forallVarFS.localVar)))()
//
//      val invRecvApp = helper.applyDomainFunc(
//        DomainsGenerator.recInvKey,
//        Seq(receiverApp, readFrom),
//        recvDType.typVarsMap
//      )
//
//      val triggerDeleteKey = helper.applyDomainFunc(
//        DomainsGenerator.trigDelKey1Key,
//        Seq(helper.reduceApply(rh, reduceVar, forallVarFS.localVar), invRecvApp),
//        reduceDType.typVarsMap)
//
//      val outForall = Forall(
//        Seq(forallVarR, forallVarFS),
//        Seq(trigger),
//        helper.foldedConjImplies(Seq(fRGood, fAccess), Seq(fRGood, triggerDeleteKey))
//      )()
//
//      Seq(Assume(outForall)())
//    }

  private def generateExhaleAxiomsPerReduce(reduceADecl: AReduceDecl, declaredLosts: mutable.Set[LocalVarDecl]): Seqn = {
    val field = program.findField(reduceADecl.fieldName)

    // Find if lostP already defined for this field
    // Ignoring the label number because using the `contains` check
    val alreadyDeclaredLost = declaredLosts.find(l => l.name.contains(s"lostP_${field.name}"))
    alreadyDeclaredLost match {
      // If already defined, just generate exhale axiom
      case Some(declared) =>
        val mainAxiom = mainExhaleAxioms(reduceADecl, declared.localVar)
        Seqn(mainAxiom, Seq())()
      //  If not defined, generate lostP and exhale axiom
      case None =>
        val declareLost = LocalVarDecl(s"lostP_${field.name}_$getLabNumForLost", SetType(Ref))()
        // Add this to the set
        declaredLosts.add(declareLost)
        //Forall(variables: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
        val forallVars = LocalVarDecl("__pElem", Ref)()
        val forallTriggers = Trigger(Seq(AnySetContains(forallVars.localVar, declareLost.localVar)()))()
        //var lostP_val : Set[Ref]
        //  assume forall iP : Ref:: {iP in lostP_val}
        //    iP in lostP_val <==> (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        //perm(iP.val)
        val insidePerm = CurrentPerm(FieldAccess(forallVars.localVar, field)())()
        val oldExp = LabelledOld(insidePerm, getLastLabel.name)()
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
        val mainAxioms = mainExhaleAxioms(reduceADecl, declareLost.localVar)

        Seqn(lostAxiom +: mainAxioms, Seq(declareLost))()
    }
  }

  private def mainExhaleAxioms(reduceADecl: AReduceDecl, lostPVal: LocalVar): Seq[Stmt] = {
    val field = program.findField(reduceADecl.fieldName)

    // Extract the reduce Domain type
    val reduceDType = reduceADecl.reduceDType(program)
    val recvDType = reduceADecl.reduceDRecvType(program)
    val reduceIdxType = reduceADecl.reduceType._1

    // rHeap declarations
    val rhOld = getLastRHeap
    val rhNew = getCurrentRHeap

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()

    val trigger = Trigger(Seq(helper.reduceApply(rhOld.toExp, reduceVar, forallVarFS.localVar)))()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(forallVarFS.localVar, reduceVar)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(forallVarFS.localVar, reduceVar)
    // Have access to the big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(forallVarFS.localVar,
      reduceVar, field.name, Some(getLastLabel.name))
    // filterNotLost
    val filterNotLostApplied = helper.subsetNotInRefs(forallVarFS.localVar, reduceVar, lostPVal)
    // Have access to the remaining filter in new state
    val forallNewStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotLostApplied,
      reduceVar, field.name, None)

    // ---------------Making the RHS---------------
    val triggerDeleteBlockOld = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.reduceApply(rhOld.toExp, reduceVar, forallVarFS.localVar), filterNotLostApplied),
      reduceDType.typVarsMap
    )
    val dummyApplyNew = helper.applyDomainFunc(
      DomainsGenerator.reduceApplyDummyKey,
      Seq(helper.reduceApply(rhNew.toExp, reduceVar, filterNotLostApplied)),
      reduceDType.typVarsMap
    )
    val framingEq = EqCmp(
      helper.applyDomainFunc(
        DomainsGenerator.reduceApplyPrimeKey,
        Seq(rhOld.toExp, reduceVar, filterNotLostApplied),
        reduceDType.typVarsMap
      ),
      helper.applyDomainFunc(
        DomainsGenerator.reduceApplyPrimeKey,
        Seq(rhNew.toExp, reduceVar, filterNotLostApplied),
        reduceDType.typVarsMap
      )
    )()
    val exhaleCF = helper.applyDomainFunc(
      DomainsGenerator.exhaleReduceSetKey,
      Seq(
        rhOld.toExp,
        reduceVar,
        forallVarFS.localVar,
        IntLit(AReduceDecl.getFieldInt(field.name))()
      ),
      reduceDType.typVarsMap
    )

    val reduceFraming = Assume(
      Forall(
        Seq(forallVarR, forallVarFS),
        Seq(trigger),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallOldHasPerm, forallNewStillHasPerm),
          Seq(frGood, triggerDeleteBlockOld, dummyApplyNew, framingEq, exhaleCF)
        )
      )()
    )()

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.reduceGetRecvKey,
      Seq(reduceVar),
      reduceDType.typVarsMap
    )

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", reduceIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      recvDType.typVarsMap
    )

    val invRecvIndApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, receiverAppIdx),
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
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, reduceVar, field.name),
                getLastLabel.name
              )()
            ),
            Seq(
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, invRecvIndApp),
                LabelledOld(
                  helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)()),
                  getLastLabel.name
                )()
              )()
            ),
          )
        )()
      )()
    )()

    val lookupUnmodified = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, idxVar)))(),
            Trigger(Seq(helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(idxNotInRefs, helper.permNonZeroCmp(idxVar, reduceVar, field.name)),
            Seq(
              idxNotInRefs,
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, invRecvIndApp),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())
              )(),
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, invRecvIndApp),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())
              )()
            ),
          )
        )()
      )()
    )()

    Seq(reduceFraming, lookupInOldState, lookupUnmodified)
  }

  private def generateInhaleAxiomsPerReduce(reduceADecl: AReduceDecl, declaredGains: mutable.Set[LocalVarDecl]): Seqn = {
    val field = program.findField(reduceADecl.fieldName)

    // Find if newP already defined for this field
    // Ignoring the label number because using the `contains` check
    val alreadyDeclaredGained = declaredGains.find(l => l.name.contains(s"gainedP_${field.name}"))
    alreadyDeclaredGained match {
      // If already defined, just generate inhale axioms
      case Some(declared) =>
        val mainAxiom = mainInhaleAxioms(reduceADecl, declared.localVar)
        Seqn(mainAxiom, Seq())()
      //  If not defined, generate gainedP and inhale axioms
      case None =>
        val declareGained = LocalVarDecl(s"gainedP_${field.name}_$getLabNumForLost", SetType(Ref))()
        // Add this to the set
        declaredGains.add(declareGained)
        //Forall(variables: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
        val forallVars = LocalVarDecl("__pElem", Ref)()
        val forallTriggers = Trigger(Seq(AnySetContains(forallVars.localVar, declareGained.localVar)()))()
        //var gainedP_Val : Set[Ref]
        //  assume forall iP : Ref:: {iP in lostP_val}
        //    iP in gainedP_Val <==> (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        //perm(iP.val)
        val insidePerm = CurrentPerm(FieldAccess(forallVars.localVar, field)())()
        val oldExp = LabelledOld(insidePerm, getLastLabel.name)()
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
        val mainAxioms = mainInhaleAxioms(reduceADecl, declareGained.localVar)

        Seqn(lostAxiom +: mainAxioms, Seq(declareGained))()
    }
  }

  private def mainInhaleAxioms(reduceADecl: AReduceDecl, gainedPVal: LocalVar): Seq[Stmt] = {
    val field = program.findField(reduceADecl.fieldName)

    // Extract the reduce Domain type
    val reduceDType = reduceADecl.reduceDType(program)
    val recvDType = reduceADecl.reduceDRecvType(program)
    val reduceIdxType = reduceADecl.reduceType._1

    // rHeap declarations
    val rhOld = getLastRHeap
    val rhNew = getCurrentRHeap
    val forallVarRH = LocalVarDecl("__exrh", Int)()

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()
    val forallVarExFS = LocalVarDecl("__exfs", SetType(reduceIdxType))()

    val triggerOld = Trigger(Seq(helper.reduceApply(rhOld.toExp, reduceVar, forallVarFS.localVar)))()
    val triggerNew = Trigger(Seq(helper.reduceApply(rhNew.toExp, reduceVar, forallVarFS.localVar)))()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(forallVarFS.localVar, reduceVar)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(forallVarFS.localVar, reduceVar)
    // Have access to the big filter in new
    val forallCurrHasPerm = helper.forallFilterHaveSomeAccess(forallVarFS.localVar,
      reduceVar, field.name, None)

    // ---------------Making the RHS---------------
    val framingEq = EqCmp(
      helper.applyDomainFunc(
        DomainsGenerator.reduceApplyPrimeKey,
        Seq(rhOld.toExp, reduceVar, forallVarFS.localVar),
        reduceDType.typVarsMap
      ),
      helper.applyDomainFunc(
        DomainsGenerator.reduceApplyKey,
        Seq(rhNew.toExp, reduceVar, forallVarFS.localVar),
        reduceDType.typVarsMap
      )
    )()

    val reduceFraming = Assume(
      Forall(
        Seq(forallVarR, forallVarFS),
        Seq(triggerOld),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallCurrHasPerm),
          Seq(frGood, framingEq)
        )
      )()
    )()

    val triggerDeleteBlockNew = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.reduceApply(rhNew.toExp, reduceVar, forallVarExFS.localVar), forallVarFS.localVar),
      reduceDType.typVarsMap
    )

    val triggerDeleteBlockExFS = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.reduceApply(forallVarRH.localVar, reduceVar, forallVarExFS.localVar), forallVarFS.localVar),
      reduceDType.typVarsMap
    )

    val setDelExFSFS = helper.applyDomainFunc(
      DomainsGenerator.setDeleteKey,
      Seq(forallVarExFS.localVar, forallVarFS.localVar),
      recvDType.typVarsMap
    )

    val triggerExtOldExFS = helper.applyDomainFunc(
      DomainsGenerator.trigExtKey,
      Seq(
        helper.applyDomainFunc(
          DomainsGenerator.reduceApplyPrimeKey,
          Seq(rhNew.toExp, reduceVar, setDelExFSFS),
          reduceDType.typVarsMap
        ),
        helper.applyDomainFunc(
          DomainsGenerator.reduceApplyPrimeKey,
          Seq(forallVarRH.localVar, reduceVar, setDelExFSFS),
          reduceDType.typVarsMap
        )
      ),
      reduceDType.typVarsMap
    )

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.reduceGetRecvKey,
      Seq(reduceVar),
      reduceDType.typVarsMap
    )

    val subsetNotInRefsGained = helper.applyDomainFunc(
      DomainsGenerator.subsetNotInRefsKey,
      Seq(forallVarFS.localVar, receiverApp, gainedPVal),
      recvDType.typVarsMap
    )

    val triggerDeleteBlockNotGained = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.reduceApply(rhNew.toExp, reduceVar, forallVarFS.localVar), subsetNotInRefsGained),
      reduceDType.typVarsMap
    )

    val dummyApplyOldNotGained = helper.applyDomainFunc(
      DomainsGenerator.reduceApplyDummyKey,
      Seq(helper.reduceApply(rhOld.toExp, reduceVar, subsetNotInRefsGained)),
      reduceDType.typVarsMap
    )

    val forallVarIdxHasPerm = helper.forallFilterHaveSomeAccess(
      forallVarFS.localVar,
      reduceVar,
      field.name,
      None
    )

    //    val forallVarFieldId = LocalVarDecl("__id", Int)()

    //    val getFieldIdEq = EqCmp(
    //      helper.applyDomainFunc(
    //        DomainsGenerator.getFieldIDKey,
    //        Seq(forallVarR.localVar),
    //        reduceDType.typVarsMap
    //      ),
    //      IntLit(AReduceDecl.getFieldInt(field.name))()
    //    )()

    val exhaleCF = helper.applyDomainFunc(
      DomainsGenerator.exhaleReduceSetKey,
      Seq(
        forallVarRH.localVar,
        reduceVar,
        forallVarExFS.localVar,
        IntLit(AReduceDecl.getFieldInt(field.name))()
      ),
      reduceDType.typVarsMap
    )

    val blockDecompOverPrevExhales = Assume(
      Forall(
        Seq(forallVarRH, forallVarR, forallVarFS, forallVarExFS),
        Seq(
          Trigger(Seq(
            helper.reduceApply(rhOld.toExp, reduceVar, forallVarFS.localVar),
            exhaleCF
          ))()
        ),
        helper.foldedConjImplies(
          Seq(
            //            getFieldIdEq,
            LtCmp(forallVarRH.localVar, rhOld.toExp)(),
            frGoodOrInj,
            AnySetSubset(forallVarFS.localVar, forallVarExFS.localVar)(),
            forallVarIdxHasPerm
          ),
          Seq(
            //            getFieldIdEq,
            frGood,
            AnySetSubset(forallVarFS.localVar, forallVarExFS.localVar)(),
            triggerDeleteBlockNew,
            triggerDeleteBlockExFS,
            triggerExtOldExFS
          ),
        )
      )()
    )()

    val blockDecompOverGainedPerms = Assume(
      Forall(
        Seq(forallVarR, forallVarFS),
        Seq(triggerNew),
        helper.foldedConjImplies(
          Seq(
            frGoodOrInj,
            forallVarIdxHasPerm
          ),
          Seq(
            frGood,
            triggerDeleteBlockNotGained,
            dummyApplyOldNotGained
          ),
        )
      )()
    )()

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", reduceIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      recvDType.typVarsMap
    )

    val invRecvIndApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, receiverAppIdx),
      recvDType.typVarsMap
    )

    val lookupInOldState = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, reduceVar, field.name),
                getLastLabel.name
              )()
            ),
            Seq(
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhOld.toExp, invRecvIndApp),
                LabelledOld(
                  helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)()),
                  getLastLabel.name
                )()
              )(),
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, invRecvIndApp),
                LabelledOld(
                  helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)()),
                  getLastLabel.name
                )()
              )()
            ),
          )
        )()
      )()
    )()

    val lookupInNewState = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(helper.permNonZeroCmp(idxVar, reduceVar, field.name)),
            Seq(
              EqCmp(
                helper.rHeapElemApplyTo(reduceVar, rhNew.toExp, invRecvIndApp),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())
              )()
            ),
          )
        )()
      )()
    )()

    Seq(reduceFraming, blockDecompOverPrevExhales, blockDecompOverGainedPerms, lookupInOldState, lookupInNewState)
  }


}
