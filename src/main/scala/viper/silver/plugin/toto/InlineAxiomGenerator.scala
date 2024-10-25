package viper.silver.plugin.toto

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.plugin.toto.ast.{ACompApply, ACompDecl, AComprehension3Tuple, AFHeap}
import viper.silver.plugin.toto.util.AxiomHelper
import viper.silver.verifier.errors
import viper.silver.verifier.errors.{ExhaleFailed, InhaleFailed}

import scala.collection.mutable

// TODOS: 1. Count how many inhales to find how many Lost vars we need to declare
// 2. track which Lost Var is related to which inhale

class InlineAxiomGenerator(program: Program, methodName: String) {

  val method: Method = program.findMethod(methodName)
  val helper = new AxiomHelper(program)

  //  val fieldMapToInt = program.fields.zipWithIndex.map(f => (f._1, f._2)).toMap

  val compDeclsUsed: Set[ACompDecl] = {
    method.deepCollect({
      case ca: ACompApply => ca.compFunctionDeclaration
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

  def mapUserLabelToCurrentAFHeap(name: String): Option[Int] = {
    userLabelToLabelNum.put(name, currentLabelNum)
  }

  def getAFHeapFromUserLabel(name: String): AFHeap = {
    val fHeapLabelNum = userLabelToLabelNum.get(name) match {
      case Some(i) => i
      case None => throw new Exception(s"User-defined label $name not found during fold heap mapping")
    }
    AFHeap(s"${helper.fHeapPrefix}$fHeapLabelNum", fHeapLabelNum)
  }

  def getOldLabel: Label = {
    Label(s"${helper.labelPrefix}l0", Seq())()
  }

  def getOldfHeap: AFHeap = {
    AFHeap(s"${helper.fHeapPrefix}0", 0)
  }

  def getCurrentfHeap: AFHeap = {
    AFHeap(s"${helper.fHeapPrefix}$currentLabelNum", currentLabelNum)
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

  private def getLastfHeap: AFHeap = {
    AFHeap(s"${helper.fHeapPrefix}${currentLabelNum-1}", currentLabelNum-1)
  }

  def fHeapDecls: Seq[(LocalVarDecl,Stmt)] = {
    Seq.range(0, currentLabelNum + 1).flatMap(fhNum => {
      val fhDecl = LocalVarDecl(
        s"${helper.fHeapPrefix}$fhNum",
        AFHeap.getType
      )()
      Seq[(LocalVarDecl,Stmt)](
        (fhDecl,
          Assume(EqCmp(
            helper.applyDomainFunc(
              DomainsGenerator.fHeapIdxKey,
              Seq(fhDecl.localVar),
              Map()
            ),
            IntLit(fhNum)()
          )())())
      )
    })
  }

  def getFHApply(comp: AComprehension3Tuple, filter: Exp, fieldName: String): Exp = {
    helper.applyFunc(AxiomHelper.tupleFieldToString(comp.tripleType, fieldName),
      Seq(comp.toViper(program), filter))
  }

  def convertMethodToInhaleExhale(methodCall: MethodCall): Seqn = {
    // Get method declaration
    val oldLabel = getUniqueLabelMethod
    val methodDecl = program.findMethod(methodCall.methodName)

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
    val relevantCompDecls = compDeclsUsed.toSeq.filter(compDecl =>
      relevantField.contains(compDecl.findFieldInProgram(program)))
    val exhaleAxioms = relevantCompDecls.map(compDecl => generateExhaleAxiomsPerComp(compDecl, declaredFieldVars))
    val allFHAxioms = relevantCompDecls.map(generateFHAssumptions)
    val allLostVars = exhaleAxioms.flatMap(e => e.scopedSeqnDeclarations)
    val allExhaleAxioms = exhaleAxioms.flatMap(e => e.ss)
    val newss = allFHAxioms.map(_._1) :+ e :+ getCurrentLabel :++ allFHAxioms.map(_._2) :++ allExhaleAxioms

    Seqn(newss, allLostVars)(e.pos, e.info, e.errT)
  }

  def generateInhaleAxioms(i: Inhale, relevantField: Set[Field]): Seqn = {
    labelIncrement()
    val declaredFieldVars = mutable.Set[LocalVarDecl]()
    val relevantCompDecls = compDeclsUsed.toSeq.filter(compDecl =>
      relevantField.contains(compDecl.findFieldInProgram(program)))
    val inhaleAxioms = relevantCompDecls.map(compDecl => generateInhaleAxiomsPerComp(compDecl, declaredFieldVars))
    val allFHAxioms = relevantCompDecls.map(generateFHAssumptions)
    val allLostVars = inhaleAxioms.flatMap(i => i.scopedSeqnDeclarations)
    val allInhaleAxioms = inhaleAxioms.flatMap(i => i.ss)
    val newss = allFHAxioms.map(_._1) :+ i :+ getCurrentLabel :++ allFHAxioms.map(_._2) :++ allInhaleAxioms

    Seqn(newss, allLostVars)(i.pos, i.info, i.errT)
  }

  def generateHeapWriteAxioms(writeStmt: Stmt): Seqn = {
    labelIncrement()
    val writes = writeStmt.deepCollect({
      case fieldAssign: FieldAssign =>
        fieldAssign
    }).toSet
    val compsAndFields = writes.flatMap(w =>
      compDeclsUsed.filter(cd => cd.findFieldInProgram(program) == w.lhs.field).zipAll(Seq(),null,w)
    ).toSeq
    val out = compsAndFields.flatMap(compAndField =>
      generateHeapWriteAxiomPerComp(compAndField._1, compAndField._2.lhs.rcv, compAndField._2.rhs)
    )
    val allFHAxioms = compsAndFields.map(_._1).map(generateFHAssumptions)
    val newss = out :++ allFHAxioms.map(_._1) :+ writeStmt :+ getCurrentLabel :++ allFHAxioms.map(_._2)

    Seqn(newss, Seq())(writeStmt.pos, writeStmt.info, writeStmt.errT)
  }

  //  def generateHeapReadAxioms(readStmt: Stmt): Stmt = {
  //    var accLHS = Set[FieldAccess]()
  //    val relevantPart: Node = readStmt match {
  //      case w : While =>
  //        w.copy(body = Seqn(Seq(), Seq())())(w.pos, w.info, w.errT)
  //      case i : If =>
  //        i.copy(thn = Seqn(Seq(), Seq())(), els = Seqn(Seq(), Seq())())(i.pos, i.info, i.errT)
  //      case out@ Seqn(_, _) =>
  //        return out
  //      // Do this to ignore LHS in case of a heap write tgt with heap read. Could cause redundancy.
  //      case a: FieldAssign =>
  //        accLHS = accLHS + a.lhs
  //        a.rhs
  //      case generated: Assume =>
  //        return generated
  //      case _ => readStmt
  //    }
  //
  //    // These reads cannot contained quantified vars
  //    val allQuantifiedVars = relevantPart.deepCollect({
  //      case qe: QuantifiedExp => qe.variables
  //    }).flatten
  //
  //    // TODO: remove stuff in accessibility predicate TOO!!
  //    val ignoreAcc = relevantPart.deepCollect({
  //      case acc: FieldAccessPredicate => acc.loc
  //    })
  //
  //    val allReads = relevantPart.deepCollect({
  //      case fieldAccess: FieldAccess => fieldAccess
  //    })
  //
  //    // Filters things in ignoreAcc, using reference equality, then convert to Set
  //    var reads = allReads.filterNot(r => ignoreAcc.exists(p => p eq r)).toSet
  //    reads = reads.filterNot(r => allQuantifiedVars.exists(p =>  r.contains(p.localVar)))
  //    reads = reads -- accLHS // remove all reads with quantified var
  //
  //    if (reads.isEmpty) {
  //      return readStmt
  //    }
  //
  //    val compAndFields = reads.flatMap(r =>
  //      compDeclsUsed.filter(cd => cd.findFieldInProgram(program) == r.field).zipAll(Seq(), null, r)
  //    ).toSeq
  //    val out = compAndFields.flatMap(compAndField =>
  //      generateHeapReadAxiomPerComp(compAndField._1, compAndField._2.rcv)
  //    )
  //    Seqn(out :+ readStmt, Seq())(readStmt.pos, readStmt.info, readStmt.errT)
  //  }

  private def generateFHAssumptions(compADecl: ACompDecl): (Stmt, Stmt) = {
    // Extract the comp Domain type
    val compDType = compADecl.compDType(program)
    val compIdxType = compADecl.compType._1

    // fHeap declarations
    val fhOld = getLastfHeap
    val fhNew = getCurrentfHeap

    // Comp var declaration
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(compIdxType))()

    val fhApply = helper.applyFunc(AxiomHelper.tupleFieldToString(compADecl.compType, compADecl.fieldName),
      Seq(compVar, forallVarFS.localVar))

    val trigger = Trigger(Seq(fhApply))()

    def genFHAssume(fh: AFHeap): Assume = {
      Assume(
        Forall(
          Seq(forallVarC, forallVarFS),
          Seq(trigger),
          EqCmp(fhApply, fh.toLocalVar)()
        )()
      )()
    }

    (genFHAssume(fhOld), genFHAssume(fhNew))
  }

  private def generateHeapWriteAxiomPerComp(compADecl: ACompDecl, writeTo: Exp, writeExp: Exp): Seq[Stmt] = {
    val field = program.findField(compADecl.fieldName)
    // Extract the comp Domain type
    val compDType = compADecl.compDType(program)
    val compIdxType = compADecl.compType._1

    // fHeap declarations
    val fhOld = getLastfHeap
    val fhNew = getCurrentfHeap

    // Comp var declaration
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(compIdxType))()

    val frGood = helper.filterReceiverGood(forallVarFS.localVar, compVar)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(forallVarFS.localVar, compVar)
    val fAccess = helper.forallFilterHaveSomeAccess(forallVarFS.localVar, compVar, field.name, None)

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.compGetRecvKey,
      Seq(compVar),
      compDType.typVarsMap
    )

    val trigger1 = Trigger(Seq(helper.compApply(fhOld.toLocalVar, compVar, forallVarFS.localVar)))()

    val invRecvApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, writeTo),
      compDType.typVarsMap
    )

    val triggerDeleteKeyNew = helper.applyDomainFunc(
      DomainsGenerator.trigDelKey1Key,
      Seq(helper.compApply(fhNew.toLocalVar, compVar, forallVarFS.localVar), invRecvApp),
      compDType.typVarsMap
    )
    val triggerDeleteKeyOld = helper.applyDomainFunc(
      DomainsGenerator.trigDelKey1Key,
      Seq(helper.compApply(fhOld.toLocalVar, compVar, forallVarFS.localVar), invRecvApp),
      compDType.typVarsMap
    )

    val setDeleteFSInv = helper.applyDomainFunc(
      DomainsGenerator.setDeleteKey,
      Seq(forallVarFS.localVar, ExplicitSet(Seq(invRecvApp))()),
      compDType.typVarsMap
    )

    val framingEq = EqCmp(
      helper.applyDomainFunc(
        DomainsGenerator.compApplyPrimeKey,
        Seq(fhOld.toLocalVar, compVar, setDeleteFSInv),
        compDType.typVarsMap
      ),
      helper.applyDomainFunc(
        DomainsGenerator.compApplyPrimeKey,
        Seq(fhNew.toLocalVar, compVar, setDeleteFSInv),
        compDType.typVarsMap
      )
    )()

    val compFraming = Assume(
      Forall(
        Seq(forallVarC, forallVarFS),
        Seq(trigger1),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, fAccess),
          Seq(frGood, triggerDeleteKeyNew, triggerDeleteKeyOld, framingEq),
        )
      )()
    )()

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", compIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      compDType.typVarsMap
    )

    val lookupUnmodified = Assume(
      Forall(
        Seq(forallVarC),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.fHeapElemApplyTo(compVar, fhOld, idxVar)))(),
            Trigger(Seq(helper.fHeapElemApplyTo(compVar, fhNew, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(NeCmp(idxVar, invRecvApp)(), helper.permNonZeroCmp(idxVar, compVar, field.name)),
            Seq(
              NeCmp(idxVar, invRecvApp)(),
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhOld, idxVar),
                helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)())
              )(),
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhNew, idxVar),
                helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)())
              )()
            ),
          )
        )()
      )()
    )()

    val lookupModified = Assume(
      Forall(
        Seq(forallVarC),
        Seq(Trigger(Seq(receiverApp))()),
        helper.foldedConjImplies(
          Seq(helper.permNonZeroCmp(invRecvApp, compVar, field.name)),
          Seq(
            EqCmp(
              helper.fHeapElemApplyTo(compVar, fhOld, invRecvApp),
              helper.mapApplyTo(compVar, FieldAccess(writeTo, field)())
            )(),
            EqCmp(
              helper.fHeapElemApplyTo(compVar, fhNew, invRecvApp),
              helper.mapApplyTo(compVar, writeExp)
            )()
          )
        )
      )()
    )()

    Seq(compFraming, lookupUnmodified, lookupModified)
  }

  //  private def generateHeapReadAxiomPerComp(compADecl:  ACompDecl, readFrom: Exp) : Seq[Stmt] = {
  //    val field = program.findField(compADecl.fieldName)
  //
  //    // Extract the comp Domain type
  //    val compDType = compADecl.compDType(program)
  //    val compIdxType = compADecl.compType._1
  //
  //    // Comp var declaration
  //    val forallVarC = LocalVarDecl("__c", compDType)()
  //    val compVar = forallVarC.localVar
  //
  //    // fHeap declaration
  //    val fh = getCurrentfHeap
  //
  //    // Filter Var declaration
  //    val forallVarFS = LocalVarDecl("__fs", SetType(compIdxType))()
  //    val fRGood = helper.filterReceiverGood(forallVarFS.localVar, compVar)
  //    val fAccess = helper.forallFilterHaveSomeAccess(forallVarFS.localVar, compVar, field.name, None)
  //
  //    val receiverApp = helper.applyDomainFunc(
  //      DomainsGenerator.compGetRecvKey,
  //      Seq(compVar),
  //      compDType.typVarsMap
  //    )
  //
  //    val trigger = Trigger(Seq(helper.compApply(fh, compVar, forallVarFS.localVar)))()
  //
  //    val invRecvApp = helper.applyDomainFunc(
  //      DomainsGenerator.recInvKey,
  //      Seq(receiverApp, readFrom),
  //      compDType.typVarsMap
  //    )
  //
  //    val triggerDeleteKey = helper.applyDomainFunc(
  //      DomainsGenerator.trigDelKey1Key,
  //      Seq(helper.compApply(fh, compVar, forallVarFS.localVar), invRecvApp),
  //      compDType.typVarsMap)
  //
  //    val outForall = Forall(
  //      Seq(forallVarC, forallVarFS),
  //      Seq(trigger),
  //      helper.foldedConjImplies(Seq(fRGood, fAccess), Seq(fRGood, triggerDeleteKey))
  //    )()
  //
  //    Seq(Assume(outForall)())
  //  }

  private def generateExhaleAxiomsPerComp(compADecl: ACompDecl, declaredLosts: mutable.Set[LocalVarDecl]): Seqn = {
    val field = program.findField(compADecl.fieldName)

    // Find if lostP already defined for this field
    // Ignoring the label number because using the `contains` check
    val alreadyDeclaredLost = declaredLosts.find(l => l.name.contains(s"lostP_${field.name}"))
    alreadyDeclaredLost match {
      // If already defined, just generate exhale axiom
      case Some(declared) =>
        val mainAxiom = mainExhaleAxioms(compADecl, declared.localVar)
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
        val mainAxioms = mainExhaleAxioms(compADecl, declareLost.localVar)

        Seqn(lostAxiom +: mainAxioms, Seq(declareLost))()
    }
  }

  private def mainExhaleAxioms(compADecl: ACompDecl, lostPVal: LocalVar): Seq[Stmt] = {
    val field = program.findField(compADecl.fieldName)

    // Extract the comp Domain type
    val compDType = compADecl.compDType(program)
    val compIdxType = compADecl.compType._1

    // fHeap declarations
    val fhOld = getLastfHeap
    val fhNew = getCurrentfHeap

    // Comp var declaration
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(compIdxType))()

    val trigger = Trigger(Seq(helper.compApply(fhOld.toLocalVar, compVar, forallVarFS.localVar)))()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(forallVarFS.localVar, compVar)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(forallVarFS.localVar, compVar)
    // Have access to the big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(forallVarFS.localVar,
      compVar, field.name, Some(getLastLabel.name))
    // filterNotLost
    val filterNotLostApplied = helper.subsetNotInRefs(forallVarFS.localVar, compVar, lostPVal)
    // Have access to the remaining filter in new state
    val forallNewStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotLostApplied,
      compVar, field.name, None)

    // ---------------Making the RHS---------------
    val triggerDeleteBlockOld = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.compApply(fhOld.toLocalVar, compVar, forallVarFS.localVar), filterNotLostApplied),
      compDType.typVarsMap
    )
    val dummyApplyNew = helper.applyDomainFunc(
      DomainsGenerator.compApplyDummyKey,
      Seq(helper.compApply(fhNew.toLocalVar, compVar, filterNotLostApplied)),
      compDType.typVarsMap
    )
    val framingEq = EqCmp(
      helper.applyDomainFunc(
        DomainsGenerator.compApplyPrimeKey,
        Seq(fhOld.toLocalVar, compVar, filterNotLostApplied),
        compDType.typVarsMap
      ),
      helper.applyDomainFunc(
        DomainsGenerator.compApplyPrimeKey,
        Seq(fhNew.toLocalVar, compVar, filterNotLostApplied),
        compDType.typVarsMap
      )
    )()
    val exhaleCF = helper.applyDomainFunc(
      DomainsGenerator.exhaleFoldSetKey,
      Seq(
        fhOld.toLocalVar,
        compVar,
        forallVarFS.localVar,
        IntLit(ACompDecl.getFieldInt(field.name))()
      ),
      compDType.typVarsMap
    )

    val compFraming = Assume(
      Forall(
        Seq(forallVarC, forallVarFS),
        Seq(trigger),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallOldHasPerm, forallNewStillHasPerm),
          Seq(frGood, triggerDeleteBlockOld, dummyApplyNew, framingEq, exhaleCF)
        )
      )()
    )()

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.compGetRecvKey,
      Seq(compVar),
      compDType.typVarsMap
    )

    // Index var declaration
    val forallVarIdx = LocalVarDecl("__ind", compIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      compDType.typVarsMap
    )

    val invRecvIndApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, receiverAppIdx),
      compDType.typVarsMap
    )

    val idxNotInRefs = helper.applyDomainFunc(
      DomainsGenerator.idxNotInRefsKey,
      Seq(idxVar, receiverApp, lostPVal),
      compDType.typVarsMap
    )

    val lookupInOldState = Assume(
      Forall(
        Seq(forallVarC),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.fHeapElemApplyTo(compVar, fhOld, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, compVar, field.name),
                getLastLabel.name
              )()
            ),
            Seq(
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhOld, invRecvIndApp),
                LabelledOld(
                  helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)()),
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
        Seq(forallVarC),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.fHeapElemApplyTo(compVar, fhOld, idxVar)))(),
            Trigger(Seq(helper.fHeapElemApplyTo(compVar, fhNew, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(idxNotInRefs, helper.permNonZeroCmp(idxVar, compVar, field.name)),
            Seq(
              idxNotInRefs,
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhOld, invRecvIndApp),
                helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)())
              )(),
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhNew, invRecvIndApp),
                helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)())
              )()
            ),
          )
        )()
      )()
    )()

    Seq(compFraming, lookupInOldState, lookupUnmodified)
  }

  private def generateInhaleAxiomsPerComp(compADecl: ACompDecl, declaredGains: mutable.Set[LocalVarDecl]): Seqn = {
    val field = program.findField(compADecl.fieldName)

    // Find if newP already defined for this field
    // Ignoring the label number because using the `contains` check
    val alreadyDeclaredGained = declaredGains.find(l => l.name.contains(s"gainedP_${field.name}"))
    alreadyDeclaredGained match {
      // If already defined, just generate inhale axioms
      case Some(declared) =>
        val mainAxiom = mainInhaleAxioms(compADecl, declared.localVar)
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
        val mainAxioms = mainInhaleAxioms(compADecl, declareGained.localVar)

        Seqn(lostAxiom +: mainAxioms, Seq(declareGained))()
    }
  }

  private def mainInhaleAxioms(compADecl: ACompDecl, gainedPVal: LocalVar): Seq[Stmt] = {
    val field = program.findField(compADecl.fieldName)

    // Extract the comp Domain type
    val compDType = compADecl.compDType(program)
    val compIdxType = compADecl.compType._1

    // fHeap declarations
    val fhOld = getLastfHeap
    val fhNew = getCurrentfHeap
    val forallVarfH = LocalVarDecl("__exfh", AFHeap.getType)()

    // Comp var declaration
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(compIdxType))()
    val forallVarExFS = LocalVarDecl("__exfs", SetType(compIdxType))()

    val triggerOld = Trigger(Seq(helper.compApply(fhOld.toLocalVar, compVar, forallVarFS.localVar)))()
    val triggerNew = Trigger(Seq(helper.compApply(fhNew.toLocalVar, compVar, forallVarFS.localVar)))()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(forallVarFS.localVar, compVar)
    val frGoodOrInj = helper.filterRecvGoodOrInjCheck(forallVarFS.localVar, compVar)
    // Have access to the big filter in new
    val forallCurrHasPerm = helper.forallFilterHaveSomeAccess(forallVarFS.localVar,
      compVar, field.name, None)

    // ---------------Making the RHS---------------
    val framingEq = EqCmp(
      helper.applyDomainFunc(
        DomainsGenerator.compApplyPrimeKey,
        Seq(fhOld.toLocalVar, compVar, forallVarFS.localVar),
        compDType.typVarsMap
      ),
      helper.applyDomainFunc(
        DomainsGenerator.compApplyKey,
        Seq(fhNew.toLocalVar, compVar, forallVarFS.localVar),
        compDType.typVarsMap
      )
    )()

    val compFraming = Assume(
      Forall(
        Seq(forallVarC, forallVarFS),
        Seq(triggerOld),
        helper.foldedConjImplies(
          Seq(frGoodOrInj, forallCurrHasPerm),
          Seq(frGood, framingEq)
        )
      )()
    )()

    val triggerDeleteBlockNew = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.compApply(fhNew.toLocalVar, compVar, forallVarExFS.localVar), forallVarFS.localVar),
      compDType.typVarsMap
    )

    val triggerDeleteBlockExFS = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.compApply(forallVarfH.localVar, compVar, forallVarExFS.localVar), forallVarFS.localVar),
      compDType.typVarsMap
    )

    val setDelExFSFS = helper.applyDomainFunc(
      DomainsGenerator.setDeleteKey,
      Seq(forallVarExFS.localVar, forallVarFS.localVar),
      compDType.typVarsMap
    )

    val triggerExtOldExFS = helper.applyDomainFunc(
      DomainsGenerator.trigExtKey,
      Seq(
        helper.applyDomainFunc(
          DomainsGenerator.compApplyPrimeKey,
          Seq(fhNew.toLocalVar, compVar, setDelExFSFS),
          compDType.typVarsMap
        ),
        helper.applyDomainFunc(
          DomainsGenerator.compApplyPrimeKey,
          Seq(forallVarfH.localVar, compVar, setDelExFSFS),
          compDType.typVarsMap
        )
      ),
      compDType.typVarsMap
    )

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.compGetRecvKey,
      Seq(compVar),
      compDType.typVarsMap
    )

    val subsetNotInRefsGained = helper.applyDomainFunc(
      DomainsGenerator.subsetNotInRefsKey,
      Seq(forallVarFS.localVar, receiverApp, gainedPVal),
      compDType.typVarsMap
    )

    val triggerDeleteBlockNotGained = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(helper.compApply(fhNew.toLocalVar, compVar, forallVarFS.localVar), subsetNotInRefsGained),
      compDType.typVarsMap
    )

    val dummyApplyOldNotGained = helper.applyDomainFunc(
      DomainsGenerator.compApplyDummyKey,
      Seq(helper.compApply(fhOld.toLocalVar, compVar, subsetNotInRefsGained)),
      compDType.typVarsMap
    )

    val forallVarIdxHasPerm = helper.forallFilterHaveSomeAccess(
      forallVarFS.localVar,
      compVar,
      field.name,
      None
    )

    //    val forallVarFieldId = LocalVarDecl("__id", Int)()

    //    val getFieldIdEq = EqCmp(
    //      helper.applyDomainFunc(
    //        DomainsGenerator.getFieldIDKey,
    //        Seq(forallVarC.localVar),
    //        compDType.typVarsMap
    //      ),
    //      IntLit(ACompDecl.getFieldInt(field.name))()
    //    )()

    val exhaleCF = helper.applyDomainFunc(
      DomainsGenerator.exhaleFoldSetKey,
      Seq(
        forallVarfH.localVar,
        compVar,
        forallVarExFS.localVar,
        IntLit(ACompDecl.getFieldInt(field.name))()
      ),
      compDType.typVarsMap
    )

    val succfHeap = helper.applyDomainFunc(
      DomainsGenerator.fHeapSTKey,
      Seq(forallVarfH.localVar, fhOld.toLocalVar),
      compDType.typVarsMap
    )

    val blockDecompOverPrevExhales = Assume(
      Forall(
        Seq(forallVarfH, forallVarC, forallVarFS, forallVarExFS),
        Seq(
          Trigger(Seq(
            helper.compApply(fhOld.toLocalVar, compVar, forallVarFS.localVar),
            exhaleCF,
            succfHeap
          ))()
        ),
        helper.foldedConjImplies(
          Seq(
            //            getFieldIdEq,
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
        Seq(forallVarC, forallVarFS),
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
    val forallVarIdx = LocalVarDecl("__ind", compIdxType)()
    val idxVar = forallVarIdx.localVar
    val receiverAppIdx = helper.applyDomainFunc(
      DomainsGenerator.recApplyKey,
      Seq(receiverApp, idxVar),
      compDType.typVarsMap
    )

    val invRecvIndApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, receiverAppIdx),
      compDType.typVarsMap
    )

    val lookupInOldState = Assume(
      Forall(
        Seq(forallVarC),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.fHeapElemApplyTo(compVar, fhOld, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(
              LabelledOld(
                helper.permNonZeroCmp(idxVar, compVar, field.name),
                getLastLabel.name
              )()
            ),
            Seq(
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhOld, invRecvIndApp),
                LabelledOld(
                  helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)()),
                  getLastLabel.name
                )()
              )(),
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhNew, invRecvIndApp),
                LabelledOld(
                  helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)()),
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
        Seq(forallVarC),
        Seq(Trigger(Seq(receiverApp))()),
        Forall(
          Seq(forallVarIdx),
          Seq(
            Trigger(Seq(helper.fHeapElemApplyTo(compVar, fhNew, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(helper.permNonZeroCmp(idxVar, compVar, field.name)),
            Seq(
              EqCmp(
                helper.fHeapElemApplyTo(compVar, fhNew, invRecvIndApp),
                helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)())
              )()
            ),
          )
        )()
      )()
    )()

    Seq(compFraming, blockDecompOverPrevExhales, blockDecompOverGainedPerms, lookupInOldState, lookupInNewState)
  }


}
