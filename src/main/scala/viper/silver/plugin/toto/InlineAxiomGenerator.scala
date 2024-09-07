package viper.silver.plugin.toto

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.plugin.toto.ast.{ACompApply, ACompDecl, AFHeap}
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

  private def getCurrentfHeap: AFHeap = {
    AFHeap(s"${helper.labelPrefix}l$currentLabelNum", currentLabelNum)()
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
    AFHeap(s"${helper.labelPrefix}l${currentLabelNum-1}", currentLabelNum-1)()
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
    val allLostVars = exhaleAxioms.flatMap(e => e.scopedSeqnDeclarations)
    val allExhaleAxioms = exhaleAxioms.flatMap(e => e.ss)

    Seqn(e +: getCurrentLabel +: allExhaleAxioms, allLostVars)(e.pos, e.info, e.errT)
  }

  def generateInhaleAxioms(i: Inhale, relevantField: Set[Field]): Seqn = {
    labelIncrement()
    val relevantCompDecls = compDeclsUsed.toSeq.filter(compDecl =>
      relevantField.contains(compDecl.findFieldInProgram(program)))
    val inhaleAxioms = relevantCompDecls.map(compDecl => generateInhaleAxiomsPerComp(compDecl))
    val allInhaleAxioms = inhaleAxioms.flatten

    Seqn(i +: getCurrentLabel +: allInhaleAxioms, Seq())(i.pos, i.info, i.errT)
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
    Seqn(writeStmt +: getCurrentLabel +: out, Seq())(writeStmt.pos, writeStmt.info, writeStmt.errT)
  }

  def generateHeapReadAxioms(readStmt: Stmt): Stmt = {
    var accLHS = Set[FieldAccess]()
    val relevantPart: Node = readStmt match {
      case w : While =>
        w.copy(body = Seqn(Seq(), Seq())())(w.pos, w.info, w.errT)
      case i : If =>
        i.copy(thn = Seqn(Seq(), Seq())(), els = Seqn(Seq(), Seq())())(i.pos, i.info, i.errT)
      case out@ Seqn(_, _) =>
        return out
      // Do this to ignore LHS in case of a heap write tgt with heap read. Could cause redundancy.
      case a: FieldAssign =>
        accLHS = accLHS + a.lhs
        a.rhs
      case generated: Assume =>
        return generated
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
    var reads = allReads.filterNot(r => ignoreAcc.exists(p => p eq r)).toSet
    reads = reads.filterNot(r => allQuantifiedVars.exists(p =>  r.contains(p.localVar)))
    reads = reads -- accLHS // remove all reads with quantified var

    if (reads.isEmpty) {
      return readStmt
    }

    val compAndFields = reads.flatMap(r =>
      compDeclsUsed.filter(cd => cd.findFieldInProgram(program) == r.field).zipAll(Seq(), null, r)
    ).toSeq
    val out = compAndFields.flatMap(compAndField =>
      generateHeapReadAxiomPerComp(compAndField._1, compAndField._2.rcv)
    )
    Seqn(out :+ readStmt, Seq())(readStmt.pos, readStmt.info, readStmt.errT)
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

    val fRGood = helper.filterReceiverGood(forallVarFS.localVar, compVar)
    val fAccess = helper.forallFilterHaveSomeAccess(forallVarFS.localVar, compVar, field.name, None)

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.compGetRecvKey,
      Seq(compVar),
      compDType.typVarsMap
    )

    val trigger1 = Trigger(Seq(helper.compApply(fhOld, compVar, forallVarFS.localVar)))()

    val invRecvApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, writeTo),
      compDType.typVarsMap
    )

    val triggerDeleteKeyNew = helper.applyDomainFunc(
      DomainsGenerator.trigDelKey1Key,
      Seq(helper.compApply(fhNew, compVar, forallVarFS.localVar), invRecvApp),
      compDType.typVarsMap
    )
    val triggerDeleteKeyOld = helper.applyDomainFunc(
      DomainsGenerator.trigDelKey1Key,
      Seq(helper.compApply(fhOld, compVar, forallVarFS.localVar), invRecvApp),
      compDType.typVarsMap
    )

    val setDeleteFSInv = ExplicitSet(
      Seq(helper.applyDomainFunc(
        DomainsGenerator.setDeleteKey,
        Seq(forallVarFS.localVar, invRecvApp),
        compDType.typVarsMap
      ))
    )()

    val framingEq = EqCmp(
      helper.applyDomainFunc(
        DomainsGenerator.compApplyPrimeKey,
        Seq(fhOld, compVar, setDeleteFSInv),
        compDType.typVarsMap
      ),
      helper.applyDomainFunc(
        DomainsGenerator.compApplyPrimeKey,
        Seq(fhNew, compVar, setDeleteFSInv),
        compDType.typVarsMap
      )
    )()

    val compFraming = Assume(
      Forall(
        Seq(forallVarC, forallVarFS),
        Seq(trigger1),
        helper.foldedConjImplies(
          Seq(fRGood, fAccess),
          Seq(fRGood, triggerDeleteKeyNew, triggerDeleteKeyOld, framingEq),
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
            Trigger(Seq(helper.fHeapElemApplyTo(fhOld, idxVar)))(),
            Trigger(Seq(helper.fHeapElemApplyTo(fhNew, idxVar)))()
          ),
          helper.foldedConjImplies(
            Seq(NeCmp(idxVar, invRecvApp)(), helper.permNonZeroCmp(invRecvApp, idxVar, field.name)),
            Seq(
              NeCmp(idxVar, invRecvApp)(),
              EqCmp(
                helper.fHeapElemApplyTo(fhOld, idxVar),
                helper.mapApplyTo(compVar, FieldAccess(receiverAppIdx, field)())
              )(),
              EqCmp(
                helper.fHeapElemApplyTo(fhNew, idxVar),
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
              helper.fHeapElemApplyTo(fhOld, invRecvApp),
              helper.mapApplyTo(compVar, FieldAccess(writeTo, field)())
            )(),
            EqCmp(
              helper.fHeapElemApplyTo(fhNew, invRecvApp),
              helper.mapApplyTo(compVar, writeExp)
            )()
          )
        )
      )()
    )()

    Seq(compFraming, lookupUnmodified, lookupModified)
  }

  private def generateHeapReadAxiomPerComp(compADecl:  ACompDecl, readFrom: Exp) : Seq[Stmt] = {
    val field = program.findField(compADecl.fieldName)

    // Extract the comp Domain type
    val compDType = compADecl.compDType(program)
    val compIdxType = compADecl.compType._1

    // Extract the comp func declaration
    val compDecl = compADecl.viperDecl(program)

    // Comp var declaration
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // fHeap declaration
    val fh = getCurrentfHeap

    // Filter Var declaration
    val forallVarFS = LocalVarDecl("__fs", SetType(compIdxType))()
    val fRGood = helper.filterReceiverGood(forallVarFS.localVar, compVar)
    val fAccess = helper.forallFilterHaveSomeAccess(forallVarFS.localVar, compVar, field.name, None)

    val receiverApp = helper.applyDomainFunc(
      DomainsGenerator.compGetRecvKey,
      Seq(compVar),
      compDType.typVarsMap
    )

    val trigger = Trigger(Seq(helper.compApply(fh, compVar, forallVarFS.localVar)))()

    val invRecvApp = helper.applyDomainFunc(
      DomainsGenerator.recInvKey,
      Seq(receiverApp, readFrom),
      compDType.typVarsMap
    )

    val triggerDeleteKey = helper.applyDomainFunc(
      DomainsGenerator.trigDelKey1Key,
      Seq(helper.compApply(fh, compVar, forallVarFS.localVar), invRecvApp),
      compDType.typVarsMap)

    val outForall = Forall(
      Seq(forallVarC, forallVarFS),
      Seq(trigger),
      helper.foldedConjImplies(Seq(fRGood, fAccess), Seq(fRGood, triggerDeleteKey))
    )()

    Seq(Assume(outForall)())
  }

  private def generateExhaleAxiomsPerComp(compADecl:  ACompDecl, declaredLosts: mutable.Set[LocalVarDecl]): Seqn =  {
    val field = program.findField(compADecl.fieldName)
//    val fieldUniqueId = fieldMaptoInt(field)
    // Find if lostP already defined for this field
    // Ignoring the label number because using the `contains` check
    val alreadyDeclaredLost = declaredLosts.find(l => l.name.contains(s"lostP_${field.name}"))
    alreadyDeclaredLost match {
      // If already defined, just generate exhale axiom
      case Some(declared) =>
        val mainAxiom = mainExhaleAxiom(compADecl, declared.localVar)
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
        val Anded = And(permNotWrite, permOldWrite)()
        // iP in lostP_val <==> (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        val forallBody = EqCmp(AnySetContains(forallVars.localVar, declareLost.localVar)(),
          Anded)()
        // forall iP : Ref:: {iP in lostP_val} ...
        val lostAxiom = Assume(Forall(Seq(forallVars), Seq(forallTriggers), forallBody)())()
        val mainAxiom = mainExhaleAxiom(compADecl, declareLost.localVar)

        Seqn(lostAxiom +: mainAxiom, Seq(declareLost))()
    }
  }

  private def mainExhaleAxiom(compADecl:  ACompDecl, lostPVal: LocalVar): Seq[Stmt] = {
    val field = program.findField(compADecl.fieldName)
    // Extract the comp Domain type
    val compDType = compADecl.compDType(program)
    // Extract the comp func declaration
    val compDecl = compADecl.viperDecl(program)

    // Comp var declaration
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var declaration
    val forallVarFilter = LocalVarDecl("__filter", SetType(compADecl.compType._1))()
    val trigger = Trigger(
      Seq(LabelledOld(helper.compApply(compVar, compDecl, forallVarFilter.localVar),
          getLastLabel.name)()
      )
    )()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(forallVarFilter.localVar, compVar)
    // Have access to the big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(forallVarFilter.localVar,
      compVar, field.name, Some(getLastLabel.name))

    // filterNotLost
    val filterNotLostApplied = helper.filterNotLost(forallVarFilter.localVar, compVar, lostPVal)
    // Have access to the remaining filter in new state
    val forallNewStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotLostApplied,
      compVar, field.name, None)

    // ---------------Making the RHS---------------
    val compApplyNotLost = helper.compApply(
      compVar,
      compDecl,
      filterNotLostApplied
    )
    val compApplyF = helper.compApply(
      compVar,
      compDecl,
      forallVarFilter.localVar
    )
    val dummy1 = helper.applyDomainFunc(
      DomainsGenerator.compApplyDummyKey,
      Seq(compApplyNotLost),
      compDType.typVarsMap
    )
    val triggerDelete = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(LabelledOld(compApplyF, getLastLabel.name)(), filterNotLostApplied),
      compDType.typVarsMap
    )
    val exhaleCF = helper.applyDomainFunc(
      DomainsGenerator.exhaleFoldSetKey,
      Seq(
        compVar,
        LabelledOld(FuncApp(compDecl, Seq(compVar, forallVarFilter.localVar))(), getLastLabel.name)(),
        IntLit(ACompDecl.getFieldInt(field.name))()
      ),
      compDType.typVarsMap
    )

    val outForall = Forall(
      Seq(forallVarC, forallVarFilter),
      Seq(trigger),
      helper.foldedConjImplies(
        Seq(frGood, forallOldHasPerm, forallNewStillHasPerm),
        Seq(frGood, triggerDelete, dummy1, exhaleCF)
      )
    )()

    Seq(Assume(outForall)())
  }

  private def generateInhaleAxiomsPerComp(compADecl:  ACompDecl) : Seq[Stmt] = {
    val field = program.findField(compADecl.fieldName)
    // Extract the comp Domain type
    val compDType = compADecl.compDType(program)
    // Extract the comp func declaration
    val compDecl = compADecl.viperDecl(program)

    // Comp var declaration
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var declaration
    val forallVarF = LocalVarDecl("__f", SetType(compADecl.compType._1))()
    val forallVarM = LocalVarDecl("__m", MapType(compADecl.compType._1, compADecl.compType._3))()

    val trigger = Trigger(Seq(
      // First trigger
      LabelledOld(helper.compApply(compVar, compDecl, forallVarF.localVar), getLastLabel.name)(),
      // Second trigger
      helper.applyDomainFunc(DomainsGenerator.exhaleFoldSetKey,
        Seq(compVar, forallVarM.localVar, IntLit(ACompDecl.getFieldInt(field.name))()),
        compDType.typVarsMap)))()

    val filter1ReceiverGood = helper.filterReceiverGood(forallVarF.localVar, compVar)
    val mapDomain = MapDomain(forallVarM.localVar)()
    val mapDomainReceiverGood = helper.filterReceiverGood(mapDomain, compVar)
    val f1subsetM = AnySetSubset(forallVarF.localVar, mapDomain)()

    val mapDAccess = helper.forallFilterHaveSomeAccess(mapDomain,
      compVar, field.name, None)

    // // triggerDeleteBlock(
    //    //     (compApply($c, snap_val_Int($c,domain(m1)))),
    //    //     $f) &&
    val triggerDelete = helper.applyDomainFunc(DomainsGenerator.trigDelBlockKey,
      Seq(helper.compApply(compVar, compDecl, mapDomain), forallVarF.localVar),
      compDType.typVarsMap)

    // // triggerDeleteBlock(
    //    //     (compApply($c, m1)),
    //    //     $f)
    val compApply = program.findDomainFunction(DomainsGenerator.compApplyKey)
    val compAppliedOldM = DomainFuncApp(compApply, Seq(compVar, forallVarM.localVar), compDType.typVarsMap)()
    val triggerDeleteOld = helper.applyDomainFunc(
      DomainsGenerator.trigDelBlockKey,
      Seq(compAppliedOldM, forallVarF.localVar),
      compDType.typVarsMap
    )
    val outForall = Forall(
      Seq(forallVarC, forallVarF, forallVarM),
      Seq(trigger),
      helper.foldedConjImplies(
        Seq(filter1ReceiverGood, mapDomainReceiverGood, f1subsetM, mapDAccess),
        Seq(filter1ReceiverGood, mapDomainReceiverGood, f1subsetM, triggerDelete, triggerDeleteOld)
      )
    )()
    Seq(Assume(outForall)())
  }

}
