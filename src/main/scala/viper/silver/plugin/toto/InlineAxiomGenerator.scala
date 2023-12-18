package viper.silver.plugin.toto

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.plugin.toto.util.AxiomHelper

import scala.collection.mutable


// TODOS: 1. Count how many inhales to find how many Lost vars we need to declare
// 2. track which Lost Var is related to which inhale


class InlineAxiomGenerator(program: Program, methodName: String) {

  val method = program.findMethod(methodName)
  val helper = new AxiomHelper(program)

  val fieldMaptoInt = program.fields.zipWithIndex.map(f => (f._1, f._2)).toMap

  val snapshotDeclsUsed = {
    method.deepCollect( {
      case fa: ASnapshotApp =>
        fa.snapshotFunctionDeclaration
    }).toSet
  }

//  val allReleventFields = {
//    snapshotDeclsUsed.map(snapDecl => program.findField(snapDecl.fieldName))
//  }
//

//  val snapshotDeclsUsed = {
//    method.deepCollect( {
//    case fa: FuncApp if fa.func(program).name.contains("_snap_") =>
//      fa.func(program)
//  })
//  }

  private var currentLabelNum = 0
  private var uniqueIDMethodOut = 0
  private var uniqueLabelMethod = 0
  private var uniqueIDLost = 0

//  private val trackAllRelavantSnapshotDefs = program.functions.filter(f => f.name.contains("snapshot"))

  private def getUniqueIDMethodOut() : String = {
    uniqueIDMethodOut += 1
    s"$uniqueIDMethodOut"
  }

  // get unique method label
  private def getUniqueLabelMethod() : Label = {
    uniqueLabelMethod += 1
    Label(s"${helper.methodLabelPrefix}l$uniqueLabelMethod", Seq())()
  }

  private def getCurrentLabel() : Label = {
    Label(s"${helper.labelPrefix}l$currentLabelNum", Seq())()
  }

  private def getLabNumForLost() : String = {
    s"l$currentLabelNum"
  }

  private def labelIncrement() : Unit = {
    currentLabelNum += 1
  }

  private def getLastLabel() : Label = {
    Label(s"${helper.labelPrefix}l${currentLabelNum-1}", Seq())()
  }

  def convertMethodToInhaleExhale(methodCall: MethodCall): Seqn = {
    // Get method declaration

    val oldLabel = getUniqueLabelMethod()

    val methodDecl = program.findMethod(methodCall.methodName)

    // LocalVarsDecls for temporary return values
    val returnDecls = methodDecl.formalReturns.map(r =>
      LocalVarDecl(r.name ++ "_out_" ++ getUniqueIDMethodOut(),r.typ)(r.pos, r.info, r.errT)
    )

    // LocalVars for temporary return values
    val returnDeclVars = returnDecls.map(td => td.localVar)

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
    val exhales = newPres.map(p => Exhale(p)(p.pos, p.info, p.errT))
    var inhales = newPost.map(p => Inhale(p)(p.pos, p.info, p.errT))

    // change all old to the correct label
    inhales = inhales.map(inhale => inhale.transform(
      {
        case old: Old =>
          LabelledOld(old.exp, oldLabel.name)(old.pos, old.info, old.errT)
      }
    ))

    // Assign targets with temporary return values
    val assigns = methodCall.targets.zip(returnDeclVars).map(
      t => AbstractAssign(t._1, t._2)
      (t._1.pos, t._1.info, t._1.errT)
    )
    Seqn(Seq(oldLabel) ++ exhales.reverse ++ inhales ++ assigns,
      returnDecls)(methodCall.pos, methodCall.info, methodCall.errT)
  }



  def generateExhaleAxioms(e: Exhale, relevantField: Set[Field]): Seqn = {
    labelIncrement()
    val declaredFieldVars = mutable.Set[LocalVarDecl]()
    val relevantSnapDecls = snapshotDeclsUsed.toSeq.filter(snapDecl =>
      relevantField.contains(snapDecl.findFieldInProgram(program)))
    val exhaleAxioms = relevantSnapDecls.map(snapDecl => generateExhaleAxiomsPerSnap(snapDecl, declaredFieldVars))
    val allLostVars = exhaleAxioms.flatMap(e => e.scopedSeqnDeclarations)
    val allExhaleAxioms = exhaleAxioms.flatMap(e => e.ss)
    Seqn(e +: getCurrentLabel() +: allExhaleAxioms, allLostVars)(
      e.pos, e.info, e.errT)
  }

  def generateInhaleAxioms(i: Inhale, relevantField: Set[Field]): Seqn = {
    labelIncrement()
    val relevantSnapDecls = snapshotDeclsUsed.toSeq.filter(snapDecl =>
      relevantField.contains(snapDecl.findFieldInProgram(program)))
    val inhaleAxioms = relevantSnapDecls.map(snapDecl => generateInhaleAxiomsPerSnap(snapDecl))
    val allInhaleAxioms = inhaleAxioms.flatten
    Seqn(i +: getCurrentLabel() +: allInhaleAxioms, Seq())(
      i.pos, i.info, i.errT)
  }

  def generateHeapWriteAxioms(writeStmt: Stmt): Seqn = {
    labelIncrement()
    val writes = writeStmt.deepCollect({
      case fieldAssign: FieldAssign =>
        fieldAssign
    }).toSet
    val snapsAndFields = writes.flatMap(w =>
      snapshotDeclsUsed.filter(sd => sd.findFieldInProgram(program) == w.lhs.field).zipAll(Seq(),null,w)
    ).toSeq
    val out = snapsAndFields.flatMap(snapAndField =>
      generateHeapWriteAxiomPerSnap(snapAndField._1,
        snapAndField._2.lhs.rcv)
    )
    Seqn(writeStmt +: getCurrentLabel() +: out, Seq())(writeStmt.pos, writeStmt.info, writeStmt.errT)
  }

  def generateHeapReadAxioms(readStmt: Stmt): Stmt = {

    var accLHS = Set[FieldAccess]()

    val releventPart: Node = readStmt match {
      case w : While =>
        w.copy(body = Seqn(Seq(), Seq())())(w.pos, w.info, w.errT)
      case i : If =>
        i.copy(thn = Seqn(Seq(), Seq())(), els = Seqn(Seq(), Seq())())(i.pos, i.info, i.errT)
      case out@ Seqn(ss, _) => return out
      // Do this to ignore LHS in case of a heap write tgt with heap read. Could cause redundancy.
      case a: FieldAssign => {
        accLHS = accLHS + a.lhs;
        a.rhs
      }
      case generated: Assume => return generated
      case _ => readStmt
    }
    // remove accessibility predicate

    // These reads cannot contained quantified vars
    val allQuantifiedVars = releventPart.deepCollect({
      case quanti: QuantifiedExp =>
        quanti.variables
    }).flatten


    // TODO: remove stuff in accessibility predicate TOO!!
    val ignoreAcc = releventPart.deepCollect({
      case acc: FieldAccessPredicate =>
        acc.loc
    })

    val allReads = releventPart.deepCollect({
      case fieldAccess: FieldAccess =>
        fieldAccess
    })

    // Filters things in ignoreAcc, using reference equality
    // then convert ot Set
    var reads = allReads.filterNot(r => ignoreAcc.exists(p => p eq r)).toSet
    reads = reads.filterNot(r => allQuantifiedVars.exists(p =>  r.contains(p.localVar)))
    reads = reads -- accLHS
    // remove all reads with quantified var


    if (reads.isEmpty) {
      return readStmt
    }

    val snapsAndFields = reads.flatMap(r =>
      snapshotDeclsUsed.filter(sd => sd.findFieldInProgram(program) == r.field).zipAll(Seq(),null,r)
    ).toSeq
    val out = snapsAndFields.flatMap(snapAndField =>
      generateHeapReadAxiomPerSnap(snapAndField._1,
      snapAndField._2.rcv)
    )
    Seqn(out :+ readStmt, Seq())(readStmt.pos, readStmt.info, readStmt.errT)

  }

  private def generateHeapWriteAxiomPerSnap(snapADecl: ASnapshotDecl, writeTo: Exp) : Seq[Stmt] = {
    val field = program.findField(snapADecl.fieldName)
    // Extract the comp Domain type
    val compDType = snapADecl.compDType(program)
    // Extract the snap func decl
    val snapDecl = snapADecl.viperDecl(program)

    // Comp var decl
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var decl
    val forallVarF = LocalVarDecl("__f", SetType(snapADecl.compType._1))()
    val trigger = Trigger(Seq(
      LabelledOld(helper.compApplySnapApply(compVar, snapDecl, forallVarF.localVar), getLastLabel().name)())
    )()
    val trigger2 = Trigger(Seq(
      helper.compApplySnapApply(compVar, snapDecl, forallVarF.localVar)
    ))()

    val fRGood = helper.filterReceiverGood(forallVarF.localVar, compVar)
    val fAccess = helper.forallFilterHaveSomeAccess(forallVarF.localVar,
      compVar, field.name, None)

    val receiverApp = helper.applyDomainFunc("getreceiver", Seq(compVar), compDType.typVarsMap)
    val invApp = helper.applyDomainFunc(DomainsGenerator.recInvKey,
      Seq(receiverApp, writeTo),
      compDType.typVarsMap)
    val triggerDeleteKeyNew = helper.applyDomainFunc("_triggerDeleteKey1",
      Seq(helper.compApplySnapApply(compVar, snapDecl, forallVarF.localVar), invApp),
      compDType.typVarsMap)
    val triggerDeleteKeyOld = helper.applyDomainFunc("_triggerDeleteKey1",
      Seq(
        LabelledOld(helper.compApplySnapApply(compVar, snapDecl, forallVarF.localVar), getLastLabel().name)(),
        invApp),
      compDType.typVarsMap)

    val outForall = Forall(
      Seq(forallVarC, forallVarF),
      Seq(trigger, trigger2),
      helper.andedImplies(
        Seq(fRGood, fAccess),
        Seq(fRGood, triggerDeleteKeyNew, triggerDeleteKeyOld),
      ))()
    Seq(Assume(outForall)())
  }

  private def generateHeapReadAxiomPerSnap(snapADecl: ASnapshotDecl, readFrom: Exp) : Seq[Stmt] = {
    val field = program.findField(snapADecl.fieldName)
    // Extract the comp Domain type
    val compDType = snapADecl.compDType(program)
    // Extract the snap func decl
    val snapDecl = snapADecl.viperDecl(program)

    // Comp var decl
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var decl
    val forallVarF = LocalVarDecl("__f", SetType(snapADecl.compType._1))()
    val trigger = Trigger(Seq(helper.compApplySnapApply(compVar,
      snapDecl, forallVarF.localVar)))()
    val fRGood = helper.filterReceiverGood(forallVarF.localVar, compVar)
    val fAccess = helper.forallFilterHaveSomeAccess(forallVarF.localVar,
      compVar, field.name, None)

    val receiverApp = helper.applyDomainFunc("getreceiver", Seq(compVar), compDType.typVarsMap)
    val invApp = helper.applyDomainFunc(DomainsGenerator.recInvKey,
      Seq(receiverApp, readFrom),
      compDType.typVarsMap)
    val triggerDeleteKey = helper.applyDomainFunc("_triggerDeleteKey1",
      Seq(helper.compApplySnapApply(compVar, snapDecl, forallVarF.localVar), invApp),
      compDType.typVarsMap)

    val outForall = Forall(
      Seq(forallVarC, forallVarF),
      Seq(trigger),
      helper.andedImplies(
        Seq(fRGood, fAccess),
        Seq(fRGood, triggerDeleteKey)
      ))()
    Seq(Assume(outForall)())
  }

  private def generateExhaleAxiomsPerSnap(snapDecl: ASnapshotDecl, declaredLosts: mutable.Set[LocalVarDecl]): Seqn =  {
    val field = program.findField(snapDecl.fieldName)
    val fieldUniqueId = fieldMaptoInt(field)
    // Find if lostP already defined for this field
    // Ignoring the label number because using the `contains` check
    val alreadyDeclaredLost = declaredLosts.find(l => l.name.contains(s"lostP_${field.name}"))
    alreadyDeclaredLost match {
      // If already defined, just generate exhale axiom
      case Some(declared) =>
        val mainAxiom = mainExhaleAxiom(snapDecl, declared.localVar)
        Seqn(mainAxiom, Seq())()
      //  If not defined, generate lostP and exhale axiom
      case None =>
        val declareLost = LocalVarDecl(s"lostP_${field.name}_${getLabNumForLost()}", SetType(Ref))()
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
        val oldExp = LabelledOld(insidePerm, getLastLabel().name)()
        // (perm(iP.val) != write)
        val permNotWrite = EqCmp(insidePerm, NoPerm()())()
        // old[l0](perm(iP.val) == write)
        val permOldWrite = GtCmp(oldExp, NoPerm()())()
        // (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        val Anded = And(permNotWrite, permOldWrite)()
        // iP in lostP_val <==> (perm(iP.val) != write) && old[l0](perm(iP.val) == write)
        var forallBody = EqCmp(AnySetContains(forallVars.localVar, declareLost.localVar)(),
          Anded)()
        // forall iP : Ref:: {iP in lostP_val} ...
        val lostAxiom = Assume(Forall(Seq(forallVars), Seq(forallTriggers), forallBody)())()
        val mainAxiom = mainExhaleAxiom(snapDecl, declareLost.localVar)

        Seqn(lostAxiom +: mainAxiom, Seq(declareLost))()
    }
  }


  private def mainExhaleAxiom(snapADecl: ASnapshotDecl, lostPVal: LocalVar): Seq[Stmt] = {
    val field = program.findField(snapADecl.fieldName)
    // Extract the comp Domain type
    val compDType = snapADecl.compDType(program)
    // Extract the snap func decl
    val snapDecl = snapADecl.viperDecl(program)

    // Comp var decl
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var decl
    val forallVarFilter = LocalVarDecl("__filter", SetType(snapADecl.compType._1))()
    val trigger = Trigger(Seq(LabelledOld(
      helper.compApplySnapApply(compVar,
        snapDecl,
        forallVarFilter.localVar),
      getLastLabel().name)()))()

    // ---------------Making the LHS---------------
    // FilterReceiverGood
    val frGood = helper.filterReceiverGood(forallVarFilter.localVar, compVar)
    // Have access to the big filter in old
    val forallOldHasPerm = helper.forallFilterHaveSomeAccess(forallVarFilter.localVar,
      compVar, field.name, Some(getLastLabel().name))

    // filterNotLost
    val filterNotLostApplied = helper.filterNotLost(forallVarFilter.localVar, compVar, lostPVal)
    // Have access to the remaining filter in new state
    val forallNewStillHasPerm = helper.forallFilterHaveSomeAccess(filterNotLostApplied,
      compVar, field.name, None)

    // ---------------Making the RHS---------------
    val compApplyNotLost = helper.compApplySnapApply(compVar,
      snapDecl,
      filterNotLostApplied)
    val compApplyF = helper.compApplySnapApply(compVar,
      snapDecl,
      forallVarFilter.localVar)
    val dummy1 = helper.applyDomainFunc("dummy1", Seq(compApplyNotLost), compDType.typVarsMap)
    val triggerDelete = helper.applyDomainFunc("_triggerDeleteBlock",
      Seq(LabelledOld(compApplyF, getLastLabel().name)(), filterNotLostApplied),
      compDType.typVarsMap)
    val exhaleCF = helper.applyDomainFunc("exhaleCompMap",
      Seq(compVar, LabelledOld(
        FuncApp(snapDecl,
          Seq(compVar, forallVarFilter.localVar))(),
        getLastLabel().name)(),
        IntLit(ASnapshotDecl.getFieldInt(field.name))()),
      compDType.typVarsMap)

    val outForall = Forall(
      Seq(forallVarC, forallVarFilter),
      Seq(trigger),
      helper.andedImplies(
        Seq(frGood, forallOldHasPerm, forallNewStillHasPerm),
        Seq(frGood, triggerDelete, dummy1, exhaleCF)
    ))()

    Seq(Assume(outForall)())
  }

  private def generateInhaleAxiomsPerSnap(snapADecl: ASnapshotDecl) : Seq[Stmt] = {
    val field = program.findField(snapADecl.fieldName)
    // Extract the comp Domain type
    val compDType = snapADecl.compDType(program)
    // Extract the snap func decl
    val snapDecl = snapADecl.viperDecl(program)

    // Comp var decl
    val forallVarC = LocalVarDecl("__c", compDType)()
    val compVar = forallVarC.localVar

    // Filter Var decl
    val forallVarF = LocalVarDecl("__f", SetType(snapADecl.compType._1))()
    val forallVarM = LocalVarDecl("__m", MapType(snapADecl.compType._1, snapADecl.compType._3))()

    val trigger = Trigger(Seq(
      // First trigger
      LabelledOld(helper.compApplySnapApply(compVar,
        snapDecl,
        forallVarF.localVar),
        getLastLabel().name)(),
      // Second trigger
      helper.applyDomainFunc("exhaleCompMap",
        Seq(compVar, forallVarM.localVar,
          IntLit(ASnapshotDecl.getFieldInt(field.name))()
        ),
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
    val triggerDelete = helper.applyDomainFunc("_triggerDeleteBlock",
      Seq(helper.compApplySnapApply(compVar, snapDecl, mapDomain), forallVarF.localVar),
      compDType.typVarsMap)



    // // triggerDeleteBlock(
    //    //     (compApply($c, m1)),
    //    //     $f)
    val compApply = program.findDomainFunction(DomainsGenerator.compApplyKey)
    val compAppliedOldM =
      DomainFuncApp(compApply,
        Seq(compVar, forallVarM.localVar), compDType.typVarsMap
    )()
    val triggerDeleteOld = helper.applyDomainFunc("_triggerDeleteBlock",
      Seq(compAppliedOldM, forallVarF.localVar),
      compDType.typVarsMap)
    val outForall = Forall(
      Seq(forallVarC, forallVarF, forallVarM),
      Seq(trigger),
      helper.andedImplies(
        Seq(filter1ReceiverGood, mapDomainReceiverGood, f1subsetM, mapDAccess),
        Seq(filter1ReceiverGood, mapDomainReceiverGood, f1subsetM, triggerDelete, triggerDeleteOld)
      ))()
    Seq(Assume(outForall)())
  }




}
