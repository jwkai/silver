package viper.silver.plugin.hreduce

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.plugin.hreduce.ast.{ARHeap, AReduceApply, AReduceDecl, rHeapInfo}
import viper.silver.plugin.hreduce.util.AxiomHelper
import viper.silver.verifier.errors
import viper.silver.verifier.errors.{ExhaleFailed, InhaleFailed}

import scala.collection.mutable

// TODOS: 1. Count how many inhales to find how many Lost vars we need to declare
// 2. track which Lost Var is related to which inhale

class InlineAxiomGenerator(program: Program, methodName: String, fuelIsTwo: Boolean) {

  val method: Method = program.findMethod(methodName)
  val helper = new AxiomHelper(program, fuelIsTwo)

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

  def getFuelExp: Exp = {
    helper.fuelDefaultExp
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
    case e: Exhale if !helper.checkIfPure(e) =>
      val fields = helper.extractFieldAcc(e)
      generateExhaleAxioms(e, fields)
    case i: Inhale if !helper.checkIfPure(i) =>
      val fields = helper.extractFieldAcc(i)
      generateInhaleAxioms(i, fields)
    case fa: FieldAssign =>
      generateHeapWriteAxioms(fa)
    case l@Label(name, _) =>
      mapUserLabelToCurrentARHeap(name)
      l
//    case a: Assert =>
//      a.withMeta(a.pos, MakeInfoPair(a.info, rHeapInfo(getCurrentRHeap)), a.errT)
//    case a: Assume =>
//      a.withMeta(a.pos, MakeInfoPair(a.info, rHeapInfo(getCurrentRHeap)), a.errT)
    case i: If =>
      ifRHeapJoin(i)
    case w: While =>
      whileRHeapFlattenInvariants(w)
    case s: Stmt if !s.isInstanceOf[Seqn] && !s.isInstanceOf[If] && !s.isInstanceOf[While] =>
      generateHeapReadAxioms(s, getCurrentRHeap)
//      s.withMeta(s.pos, MakeInfoPair(s.info, rHeapInfo(getCurrentRHeap)), s.errT)
  }

  private def overwriteRHeap(rh: ARHeap): PartialFunction[Node, Node] = {
    case ra: AReduceApply =>
      ra.rHeap = Some(rh)
      ra
  }

  // Overwrites the ARHeap info for any old(...) expressions (used in while bodies)
  private def overwriteOldRHeap(rh: ARHeap): PartialFunction[Node, Node] = {
    case old@Old(e) =>
      old.copy(exp = e.transform(overwriteRHeap(rh)))(old.pos, old.info, old.errT)
  }

  // Add axioms to each branch, "join" branches with next rHeap and triggers
  private def ifRHeapJoin(i: If): If = {
    val rHeapOrig = getCurrentRHeap
    val cndFields = helper.extractFieldAcc(i.cond)
    val thnFields = helper.extractFieldAcc(i.thn)
    val thnAxs = i.thn.transform(addAxiomsToBody())
    val rHeapThn = getCurrentRHeap
    val elsFields = helper.extractFieldAcc(i.els)
    val elsAxs = i.els.transform(addAxiomsToBody())
    val rHeapEls = if (i.els == EmptyStmt) rHeapOrig else getCurrentRHeap
    val relevantFields = cndFields ++ thnFields ++ elsFields
    labelIncrement()
    val ifJoinAxsThn = makeIfJoinAxioms(rHeapThn, getCurrentRHeap, relevantFields)
    val ifJoinThn = Seqn(
      thnAxs.ss ++ ifJoinAxsThn,
      thnAxs.scopedSeqnDeclarations
    )(thnAxs.pos, thnAxs.info, thnAxs.errT)
    val ifJoinAxsEls = makeIfJoinAxioms(rHeapEls, getCurrentRHeap, relevantFields)
    val ifJoinEls = Seqn(
      elsAxs.ss ++ ifJoinAxsEls,
      elsAxs.scopedSeqnDeclarations
    )(elsAxs.pos, elsAxs.info, elsAxs.errT)
    i.copy(
      thn = ifJoinThn,
      els = ifJoinEls
    )(i.pos, MakeInfoPair(i.info, rHeapInfo(rHeapOrig)), i.errT)
  }

  private def makeIfJoinAxioms(rhCurr: ARHeap, rhNext: ARHeap, relevantField: Set[Field]): Seq[Stmt] = {
    def ffAxs(rh: ARHeap, reduceADecl: AReduceDecl): Seq[Stmt] = {
      // Extract the reduce Domain type
      val reduceDType = reduceADecl.reduceDType(program)
      val reduceIdxType = reduceADecl.reduceType._1
      val reduceHasID = reduceADecl.hasID

      // Create domain-typed vars for quantification
      val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
      val forallVarR = LocalVarDecl("__r", reduceDType)()
      val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()
      val forallVarIdx = LocalVarDecl("__i", reduceIdxType)()

      val currReduceTerm = helper.reduceApply(forallVarF.localVar, rh.toExp, forallVarR.localVar, forallVarFS.localVar)(reduceHasID)
      val nextReduceTerm = helper.reduceApply(forallVarF.localVar, rhNext.toExp, forallVarR.localVar, forallVarFS.localVar)(reduceHasID)
      val eqReduce = Assume(
        Forall(
          Seq(forallVarF, forallVarR, forallVarFS),
          Seq(Trigger(Seq(currReduceTerm))()),
          EqCmp(currReduceTerm, nextReduceTerm)()
        )()
      )()

//      // Add primed version so that any "yielded" terms are automatically advanced
//      val currReducePrimeTerm = helper.reducePrimeApply(rh.toExp, forallVarR.localVar, forallVarFS.localVar)(reduceHasID)
//      val nextReducePrimeTerm = helper.reducePrimeApply(rhNext.toExp, forallVarR.localVar, forallVarFS.localVar)(reduceHasID)
//      val eqReducePrime = Assume(
//        Forall(
//          Seq(forallVarR, forallVarFS),
//          Seq(Trigger(Seq(currReducePrimeTerm))()),
//          EqCmp(currReducePrimeTerm, nextReducePrimeTerm)()
//        )()
//      )()

      val currRHeapElemTerm = helper.rHeapElemApplyTo(
        rh.toExp,
        forallVarR.localVar,
        forallVarIdx.localVar
      )(reduceHasID)
      val nextRHeapElemTerm = helper.rHeapElemApplyTo(
        rhNext.toExp,
        forallVarR.localVar,
        forallVarIdx.localVar
      )(reduceHasID)
      val eqRHeapElem = Assume(
        Forall(
          Seq(forallVarR, forallVarIdx),
          Seq(Trigger(Seq(currRHeapElemTerm))()),
          EqCmp(currRHeapElemTerm, nextRHeapElemTerm)()
        )()
      )()

      Seq(eqReduce, eqRHeapElem)
    }

    val relevantReduceDecls = reduceDeclsUsed.toSeq.filter(reduceDecl =>
      relevantField.contains(reduceDecl.findFieldInProgram(program)))

    relevantReduceDecls.flatMap(reduceDecl => ffAxs(rhCurr, reduceDecl))
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
    val wBodyRec: Seqn = w.body.transform(addAxiomsToBody()).transform(overwriteOldRHeap(rHeapOnEntry))
    Seqn(
      foldInvsAssert(rHeapOrig) ++
        Seq(
          w.copy(
            body = Seqn(
              Seq(labelOnEntry) ++
              foldInvsAssume(rHeapOnEntry) ++
              wBodyRec.ss.map(s => {
                s.info.getUniqueInfo[rHeapInfo] match {
                  case Some(_) => s
                  case None => s.withMeta(s.pos, MakeInfoPair(s.info, rHeapInfo(getCurrentRHeap)), s.errT)
                }
              }) ++
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

  def generateHeapReadAxioms(readStmt: Stmt, rHeap: ARHeap): Stmt = {
    var accLHS = Set[FieldAccess]()
    val relevantPart: Node = readStmt match {
      case w: While =>
        w.copy(body = Seqn(Seq(), Seq())())(w.pos, w.info, w.errT)
      case i: If =>
        i.copy(thn = Seqn(Seq(), Seq())(), els = Seqn(Seq(), Seq())())(i.pos, i.info, i.errT)
      case out@Seqn(_, _) =>
        return out
      // Do this to ignore LHS in case of a heap write tgt with heap read. Could cause redundancy.
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

    val readStmtWrHeap = readStmt.withMeta(readStmt.pos, MakeInfoPair(readStmt.info, rHeapInfo(getCurrentRHeap)), readStmt.errT)

    if (reads.isEmpty) {
      return readStmtWrHeap
    }

    val reduceAndFields = reads.flatMap(r =>
      reduceDeclsUsed.filter(rd => rd.findFieldInProgram(program) == r.field).zipAll(Seq(), null, r)
    ).toSeq
    val out = reduceAndFields.flatMap(reduceAndField =>
      generateHeapReadAxiomPerReduce(reduceAndField._1, reduceAndField._2.rcv, rHeap)
    )
    Seqn(readStmtWrHeap +: out, Seq())(readStmtWrHeap.pos, readStmtWrHeap.info, readStmtWrHeap.errT)
  }

  private def generateHeapWriteAxiomPerReduce(reduceADecl: AReduceDecl, writeTo: Exp, writeExp: Exp): Seq[Stmt] = {
    val field = program.findField(reduceADecl.fieldName)
    // Extract the reduce Domain type
    val reduceDType = reduceADecl.reduceDType(program)
    val recvDType = reduceADecl.reduceDRecvType(program)
    val reduceIdxType = reduceADecl.reduceType._1
    val reduceHasID = reduceADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )

    // rHeap declarations
    val rhOld = getLastRHeap
    val rhNew = getCurrentRHeap

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()
    var filterVar = forallVarFS.localVar

    val frGood = helper.filterReceiverGood(filterVar, reduceVar)(reduceHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, reduceVar)(reduceHasID)
    val fAccess = helper.forallFilterHaveSomeAccess(filterVar, reduceVar, field.name, None)(reduceHasID)

    val receiverApp = helper.getReceiverApply(reduceVar)(reduceHasID)

    val triggerOld = Trigger(Seq(helper.reduceApply(sFuel, rhOld.toExp, reduceVar, filterVar)(reduceHasID)))()
    val triggerNew = Trigger(Seq(helper.reduceApply(sFuel, rhNew.toExp, reduceVar, filterVar)(reduceHasID)))()

    val invRecvApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, writeTo),
      recvDType.typVarsMap
    )

    val triggerDeleteKeyNew = helper.trigDelKeyApply(sFuel, rhNew.toExp, reduceVar, filterVar, invRecvApp)(reduceHasID)
    val triggerDeleteKeyOld = helper.trigDelKeyApply(sFuel, rhOld.toExp, reduceVar, filterVar, invRecvApp)(reduceHasID)

    val setDeleteFSInv = helper.applyDomainFunc(
      DomainsGenerator.setDeleteKey,
      Seq(forallVarFS.localVar, ExplicitSet(Seq(invRecvApp))()),
      recvDType.typVarsMap
    )

    val framingEq = EqCmp(
      helper.reduceApply(fuelVar, rhOld.toExp, reduceVar, setDeleteFSInv)(reduceHasID),
      helper.reduceApply(fuelVar, rhNew.toExp, reduceVar, setDeleteFSInv)(reduceHasID)
    )()

    val reduceFraming = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerOld, triggerNew),
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
            Trigger(Seq(helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, idxVar)(reduceHasID)))(),
            Trigger(Seq(helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, idxVar)(reduceHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(NeCmp(idxVar, invRecvApp)(), helper.permNonZeroCmp(idxVar, reduceVar, field.name)(reduceHasID)),
            Seq(
              NeCmp(idxVar, invRecvApp)(),
              EqCmp(
                helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, idxVar)(reduceHasID),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID)
              )(),
              EqCmp(
                helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, idxVar)(reduceHasID),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID)
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
          Seq(helper.permNonZeroCmp(invRecvApp, reduceVar, field.name)(reduceHasID)),
          Seq(
            EqCmp(
              helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, invRecvApp)(reduceHasID),
              helper.mapApplyTo(reduceVar, FieldAccess(writeTo, field)())(reduceHasID)
            )(),
            EqCmp(
              helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, invRecvApp)(reduceHasID),
              helper.mapApplyTo(reduceVar, writeExp)(reduceHasID)
            )()
          )
        )
      )()
    )()

    Seq(reduceFraming, lookupUnmodified, lookupModified)
  }

  private def generateHeapReadAxiomPerReduce(reduceADecl: AReduceDecl, readFrom: Exp, rh: ARHeap) : Seq[Stmt] = {
    val field = program.findField(reduceADecl.fieldName)

    // Extract the reduce Domain type
    val reduceDType = reduceADecl.reduceDType(program)
    val recvDType = reduceADecl.reduceDRecvType(program)
    val reduceIdxType = reduceADecl.reduceType._1
    val reduceHasID = reduceADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()
    val filterVar = forallVarFS.localVar

    val fRGood = helper.filterReceiverGood(filterVar, reduceVar)(reduceHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, reduceVar)(reduceHasID)
    val fAccess = helper.forallFilterHaveSomeAccess(filterVar, reduceVar, field.name, None)(reduceHasID)

    val receiverApp = helper.getReceiverApply(reduceVar)(reduceHasID)
    val trigger = Trigger(Seq(helper.reduceApply(sFuel, rh.toExp, reduceVar, filterVar)(reduceHasID)))()

    val invRecvApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, readFrom),
      recvDType.typVarsMap
    )

    val triggerDeleteKey = helper.trigDelKeyApply(sFuel, rh.toExp, reduceVar, filterVar, invRecvApp)(reduceHasID)

    val reduceDelKey = Assume(
        Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(trigger),
        helper.foldedConjImplies(Seq(frGoodOrInj, fAccess), Seq(fRGood, triggerDeleteKey))
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

    val lookupUnread = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.rHeapElemApplyTo(rh.toExp, reduceVar, idxVar)(reduceHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(helper.permNonZeroCmp(idxVar, reduceVar, field.name)(reduceHasID)),
            Seq(
              EqCmp(
                helper.rHeapElemApplyTo(rh.toExp, reduceVar, idxVar)(reduceHasID),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID)
              )()
            ),
          )
        )()
      )()
    )()

    val lookupRead = Assume(
      Forall(
        Seq(forallVarR),
        Seq(Trigger(Seq(receiverApp))()),
        helper.foldedConjImplies(
          Seq(helper.permNonZeroCmp(invRecvApp, reduceVar, field.name)(reduceHasID)),
          Seq(
            EqCmp(
              helper.rHeapElemApplyTo(rh.toExp, reduceVar, invRecvApp)(reduceHasID),
              helper.mapApplyTo(reduceVar, FieldAccess(readFrom, field)())(reduceHasID)
            )()
          )
        )
      )()
    )()

    Seq(reduceDelKey, lookupUnread, lookupRead)
  }

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
    val reduceHasID = reduceADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )

    // rHeap declarations
    val rhOld = getLastRHeap
    val rhNew = getCurrentRHeap

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()
    val filterVar = forallVarFS.localVar

    val triggerOld = Trigger(Seq(helper.reduceApply(sFuel, rhOld.toExp, reduceVar, filterVar)(reduceHasID)))()
    val triggerNew = Trigger(Seq(helper.reduceApply(sFuel, rhNew.toExp, reduceVar, filterVar)(reduceHasID)))()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(filterVar, reduceVar)(reduceHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, reduceVar)(reduceHasID)
    // Have access to the big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      reduceVar, field.name, Some(getLastLabel.name))(reduceHasID)
    // filterNotLost
    val filterNotLostApplied = helper.subsetNotInRefs(filterVar, reduceVar, lostPVal)(reduceHasID)
    // Have access to the remaining filter in new state
    val forallNewStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotLostApplied,
      reduceVar, field.name, None)(reduceHasID)
    // Have access to big filter in new
    val forallNewHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      reduceVar, field.name, None)(reduceHasID)

    // ---------------Making the RHS---------------
    val triggerDeleteBlockOld = helper.trigDelBlockApply(
      sFuel,
      rhOld.toExp,
      reduceVar,
      filterVar,
      filterNotLostApplied
    )(reduceHasID)

    val dummyApplyNew = helper.reduceDummyApply(fuelVar, rhNew.toExp, reduceVar, filterNotLostApplied)(reduceHasID)

    val decompFramingEq = EqCmp(
      helper.reduceApply(fuelVar, rhOld.toExp, reduceVar, filterNotLostApplied)(reduceHasID),
      helper.reduceApply(fuelVar, rhNew.toExp, reduceVar, filterNotLostApplied)(reduceHasID)
    )()

    val reduceDecompOld = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerOld),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallOldHasPerm, forallNewStillHasPerm),
          Seq(frGood, triggerDeleteBlockOld, dummyApplyNew, decompFramingEq)
        )
      )()
    )()

    val fsPropSubsetNotLost = And(
      Not(EqCmp(filterVar, EmptySet(reduceIdxType)())())(),
      AnySetSubset(filterVar, filterNotLostApplied)()
    )()
    val dummyApplyOld = helper.reduceDummyApply(fuelVar, rhOld.toExp, reduceVar, filterVar)(reduceHasID)
    val newFramingEq = EqCmp(
      helper.reduceApply(fuelVar, rhOld.toExp, reduceVar, filterVar)(reduceHasID),
      helper.reduceApply(fuelVar, rhNew.toExp, reduceVar, filterVar)(reduceHasID)
    )()

    val reduceFramingNew = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerNew),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallOldHasPerm, forallNewHasPerm, fsPropSubsetNotLost),
          Seq(frGood, dummyApplyOld, newFramingEq)
        )
      )()
    )()

    val receiverApp = helper.getReceiverApply(reduceVar)(reduceHasID)

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
            Trigger(Seq(helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, idxVar)(reduceHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, reduceVar, field.name)(reduceHasID),
                getLastLabel.name
              )()
            ),
            Seq(
              EqCmp(
                helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, invRecvIndApp)(reduceHasID),
                LabelledOld(
                  helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID),
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
            Trigger(Seq(helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, idxVar)(reduceHasID)))(),
            Trigger(Seq(helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, idxVar)(reduceHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(idxNotInRefs, helper.permNonZeroCmp(idxVar, reduceVar, field.name)(reduceHasID)),
            Seq(
              idxNotInRefs,
              EqCmp(
                helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, invRecvIndApp)(reduceHasID),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID)
              )(),
              EqCmp(
                helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, invRecvIndApp)(reduceHasID),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID)
              )()
            ),
          )
        )()
      )()
    )()

    Seq(reduceDecompOld, reduceFramingNew, lookupInOldState, lookupUnmodified)
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
    val reduceHasID = reduceADecl.hasID

    // fuel declarations
    val forallVarF = LocalVarDecl("__f", helper.fuelDomainType)()
    val fuelVar = forallVarF.localVar
    val sFuel = helper.applyDomainFunc(
      DomainsGenerator.fuelSKey,
      Seq(fuelVar),
      helper.fuelDomainType.typVarsMap
    )

    // rHeap declarations
    val rhOld = getLastRHeap
    val rhNew = getCurrentRHeap
//    val forallVarRH = LocalVarDecl("__exrh", Int)()

    // Reduce var declaration
    val forallVarR = LocalVarDecl("__r", reduceDType)()
    val reduceVar = forallVarR.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(reduceIdxType))()
    val filterVar = forallVarFS.localVar
//    val forallVarExFS = LocalVarDecl("__exfs", SetType(reduceIdxType))()

    val triggerOld = Trigger(Seq(helper.reduceApply(sFuel, rhOld.toExp, reduceVar, filterVar)(reduceHasID)))()
    val triggerNew = Trigger(Seq(helper.reduceApply(sFuel, rhNew.toExp, reduceVar, filterVar)(reduceHasID)))()

    val receiverApp = helper.getReceiverApply(reduceVar)(reduceHasID)

    // filterNotGained
    val filterNotGainedApplied = helper.applyDomainFunc(
      DomainsGenerator.subsetNotInRefsKey,
      Seq(forallVarFS.localVar, receiverApp, gainedPVal),
      recvDType.typVarsMap
    )

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(filterVar, reduceVar)(reduceHasID)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(filterVar, reduceVar)(reduceHasID)
    // Have access to the big filter in new
    val forallNewHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      reduceVar, field.name, None)(reduceHasID)
    // Have access to the remaining filter in old state
    val forallOldStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotGainedApplied,
      reduceVar, field.name, Some(getLastLabel.name))(reduceHasID)
    // Have access to big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(filterVar,
      reduceVar, field.name, Some(getLastLabel.name))(reduceHasID)

    // ---------------Making the RHS---------------
    val triggerDeleteBlockNew = helper.trigDelBlockApply(
      sFuel,
      rhNew.toExp,
      reduceVar,
      filterVar,
      filterNotGainedApplied
    )(reduceHasID)

    val dummyApplyOld = helper.reduceDummyApply(fuelVar, rhOld.toExp, reduceVar, filterNotGainedApplied)(reduceHasID)

    val decompFramingEq = EqCmp(
      helper.reduceApply(fuelVar, rhOld.toExp, reduceVar, filterNotGainedApplied)(reduceHasID),
      helper.reduceApply(fuelVar, rhNew.toExp, reduceVar, filterNotGainedApplied)(reduceHasID)
    )()

    val reduceDecompNew = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerNew),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallNewHasPerm, forallOldStillHasPerm),
          Seq(frGood, triggerDeleteBlockNew, dummyApplyOld, decompFramingEq)
        )
      )()
    )()

    val fsPropSubsetNotGained = And(
      Not(EqCmp(filterVar, EmptySet(reduceIdxType)())())(),
      AnySetSubset(filterVar, filterNotGainedApplied)()
    )()
    val dummyApplyNew = helper.reduceDummyApply(fuelVar, rhNew.toExp, reduceVar, filterVar)(reduceHasID)
    val oldFramingEq = EqCmp(
      helper.reduceApply(fuelVar, rhOld.toExp, reduceVar, filterVar)(reduceHasID),
      helper.reduceApply(fuelVar, rhNew.toExp, reduceVar, filterVar)(reduceHasID)
    )()

    val reduceFramingOld = Assume(
      Forall(
        Seq(forallVarF, forallVarR, forallVarFS),
        Seq(triggerOld),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallOldHasPerm, forallNewHasPerm, fsPropSubsetNotGained),
          Seq(frGood, dummyApplyNew, oldFramingEq)
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
            Trigger(Seq(helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, idxVar)(reduceHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, reduceVar, field.name)(reduceHasID),
                getLastLabel.name
              )()
            ),
            Seq(
              EqCmp(
                helper.rHeapElemApplyTo(rhOld.toExp, reduceVar, invRecvIndApp)(reduceHasID),
                LabelledOld(
                  helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID),
                  getLastLabel.name
                )()
              )(),
              EqCmp(
                helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, invRecvIndApp)(reduceHasID),
                LabelledOld(
                  helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID),
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
            Trigger(Seq(helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, idxVar)(reduceHasID)))()
          ),
          helper.foldedConjImplies(
            Seq(helper.permNonZeroCmp(idxVar, reduceVar, field.name)(reduceHasID)),
            Seq(
              EqCmp(
                helper.rHeapElemApplyTo(rhNew.toExp, reduceVar, invRecvIndApp)(reduceHasID),
                helper.mapApplyTo(reduceVar, FieldAccess(receiverAppIdx, field)())(reduceHasID)
              )()
            ),
          )
        )()
      )()
    )()

    Seq(reduceDecompNew, reduceFramingOld, lookupInOldState, lookupInNewState)
  }


}
