package viper.silver.plugin.hreduce.util

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.plugin.hreduce.DomainsGenerator

class AxiomHelper(program: Program, fuelIsTwo: Boolean) {

  //  def getStartLabel: Label = {
  //    Label(s"${labelPrefix}l0", Seq())()
  //  }

  val fuelDomainType: DomainType = {
    val fuelDomain = program.findDomain(DomainsGenerator.fuelDKey)
    DomainType.apply(fuelDomain, Map())
  }

  var fuelDefaultExp: Exp = {
    val sFuel = if (fuelIsTwo) {
      applyDomainFunc(
        DomainsGenerator.fuelSKey,
        Seq(applyDomainFunc(
          DomainsGenerator.fuelSKey,
          Seq(applyDomainFunc(DomainsGenerator.fuelZKey, Seq(), fuelDomainType.typVarsMap)),
          fuelDomainType.typVarsMap)),
        fuelDomainType.typVarsMap)
    } else { // fuel is one
      applyDomainFunc(
        DomainsGenerator.fuelSKey,
        Seq(applyDomainFunc(DomainsGenerator.fuelZKey, Seq(), fuelDomainType.typVarsMap)),
        fuelDomainType.typVarsMap)
    }
    sFuel
  }

  def labelPrefix: String = {
    "_reduceLabel"
  }

  def rHeapPrefix: String = {
    "_rh"
  }

  def methodLabelPrefix : String = {
    "_methodLabel"
  }

  def extractFieldAcc(e: Exp): Set[Field] = {
    e.deepCollect({
      case fieldAccess: FieldAccess =>
        fieldAccess.field
    }).toSet
  }

  def extractFieldAcc(s: Stmt): Set[Field] = {
    s.deepCollect({
      case fieldAccessPredicate: FieldAccessPredicate =>
        fieldAccessPredicate.loc.field
    }).toSet
  }

  def checkIfPure(stmt: Stmt): Boolean = {
    stmt match {
      case Exhale(exp) => Expressions.isPure(exp)
      case Inhale(exp) => Expressions.isPure(exp)
      case Assert(exp) => Expressions.isPure(exp)
      case Assume(exp) => Expressions.isPure(exp)
      case Seqn(ss, _) => ss.forall(checkIfPure)
      case If(cond, thn, els) =>
        Expressions.isPure(cond) && checkIfPure(thn) && checkIfPure(els)
      case While(cond, invs, body) =>
        Expressions.isPure(cond) && invs.forall(Expressions.isPure) && checkIfPure(body)
      case Label(_, invs) =>
        invs.forall(Expressions.isPure)
      case Goto(_) =>
        true
      case LocalVarDeclStmt(_) =>
        true
      case _ =>
        false
    }
  }

  //-----------------------------------------------------------------
  //-----------------------------------------------------------------
  //-----------------------------------------------------------------
  // Helper functions
  def applyFunc(funcName: String, applyTo: Seq[Exp]): FuncApp = {
    val func = program.findFunction(funcName)
    FuncApp(func, applyTo)()
  }

  def applyDomainFunc(domainFuncName: String, applyTo: Seq[Exp],
                      typMap: Map[TypeVar, Type]): DomainFuncApp = {
    val domainFunc = program.findDomainFunction(domainFuncName)
    DomainFuncApp(domainFunc, applyTo, typMap)()
  }

  def reduceApply(fuel: Exp, rHeap: Exp, reduce: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
    val reduceApply = if (hasID) DomainsGenerator.reduceApplyKeyM else DomainsGenerator.reduceApplyKeyS
    applyDomainFunc(
      reduceApply,
      Seq(fuel, rHeap, reduce, filter),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

//  def reducePrimeApply(rHeap: Exp, reduce: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
//    val reduceApplyPrime = if (hasID) DomainsGenerator.reduceApplyPrimeKeyM else DomainsGenerator.reduceApplyPrimeKeyS
//    applyDomainFunc(
//      reduceApplyPrime,
//      Seq(rHeap, reduce, filter),
//      reduce.typ.asInstanceOf[DomainType].typVarsMap
//    )
//  }

  def reduceDummyApply(fuel: Exp, rHeap: Exp, reduce: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
    val reduceApplyDummyKey = if (hasID) DomainsGenerator.reduceApplyDummyKeyM else DomainsGenerator.reduceApplyDummyKeyS
    applyDomainFunc(
      reduceApplyDummyKey,
      Seq(reduceApply(fuel, rHeap, reduce, filter)(hasID)),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

//  def exhaleReduceSetApply(rHeap: Exp, reduce: Exp, filter: Exp, fieldId: Exp)(hasID: Boolean): DomainFuncApp = {
//    val exhaleReduceSetKey = if (hasID) DomainsGenerator.exhaleReduceSetKeyM else DomainsGenerator.exhaleReduceSetKeyS
//    applyDomainFunc(
//      exhaleReduceSetKey,
//      Seq(rHeap, reduce, filter, fieldId),
//      reduce.typ.asInstanceOf[DomainType].typVarsMap
//    )
//  }

  def trigExtApply(fuel1: Exp, rHeap1: Exp, fuel2: Exp, rHeap2: Exp, reduce: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
    val trigExtKey = if (hasID) DomainsGenerator.trigExtKeyM else DomainsGenerator.trigExtKeyS
    applyDomainFunc(
      trigExtKey,
      Seq(reduceApply(fuel1, rHeap1, reduce, filter)(hasID), reduceApply(fuel2, rHeap2, reduce, filter)(hasID)),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def getReceiverApply(reduce: Exp)(hasID: Boolean): DomainFuncApp = {
    val reduceGetRecvKey = if (hasID) DomainsGenerator.reduceGetRecvKeyM else DomainsGenerator.reduceGetRecvKeyS
    applyDomainFunc(
      reduceGetRecvKey,
      Seq(reduce),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def getMappingApply(reduce: Exp)(hasID: Boolean): DomainFuncApp = {
    val reduceGetMappingKey = if (hasID) DomainsGenerator.reduceGetMappingKeyM else DomainsGenerator.reduceGetMappingKeyS
    applyDomainFunc(
      reduceGetMappingKey,
      Seq(reduce),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def trigDelKeyApply(fuel: Exp, rHeap: Exp, reduce: Exp, filter: Exp, key: Exp)(hasID: Boolean): DomainFuncApp = {
    val trigDelKey1Key = if (hasID) DomainsGenerator.trigDelKey1KeyM else DomainsGenerator.trigDelKey1KeyS
    val reduceApplyApp = reduceApply(fuel, rHeap, reduce, filter)(hasID)
    applyDomainFunc(
      trigDelKey1Key,
      Seq(reduceApplyApp, key),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def trigDelBlockApply(fuel: Exp, rHeap: Exp, reduce: Exp, filter: Exp, keySet: Exp)(hasID: Boolean): DomainFuncApp = {
    val trigDelBlockKey = if (hasID) DomainsGenerator.trigDelBlockKeyM else DomainsGenerator.trigDelBlockKeyS
    val reduceApplyApp = reduceApply(fuel, rHeap, reduce, filter)(hasID)
    applyDomainFunc(
      trigDelBlockKey,
      Seq(reduceApplyApp, keySet),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def foldConj(exps: Seq[Exp]): Exp = {
    if (exps.length == 1) {
      exps.head
    } else if (exps.length == 2) {
      And(exps(0), exps(1))()
    } else {
      And(exps.head, foldConj(exps.tail))()
    }
  }

  def foldedConjImplies(lhsExps: Seq[Exp], rhsExps: Seq[Exp]): Exp = {
    Implies(foldConj(lhsExps), foldConj(rhsExps))()
  }

  def injectiveFullCheck(filter: Exp, reduceExp: Exp)(hasID: Boolean): QuantifiedExp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(reduceExp)(hasID)

    val recvElemType = filter.typ match {
      case setType: SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    // Make the injectivity checks
    val forallVarInd1 = LocalVarDecl("__ind1", recvElemType)()
    val forallVarInd2 = LocalVarDecl("__ind2", recvElemType)()
    val setContains1 = AnySetContains(forallVarInd1.localVar, filter)()
    val setContains2 = AnySetContains(forallVarInd2.localVar, filter)()
    val idxsNeq = NeCmp(forallVarInd1.localVar, forallVarInd2.localVar)()
    val recApplyInd1 = applyDomainFunc(DomainsGenerator.recApplyKey,
      Seq(getreceiverApplied, forallVarInd1.localVar),
      recvType.typVarsMap)
    val recApplyInd2 = applyDomainFunc(DomainsGenerator.recApplyKey,
      Seq(getreceiverApplied, forallVarInd2.localVar),
      recvType.typVarsMap)
    val recApplyNeq = NeCmp(recApplyInd1, recApplyInd2)()
    val injectiveFullCheck = Forall(
      Seq(forallVarInd1, forallVarInd2),
      Seq(Trigger(Seq(setContains1, setContains2))()),
      foldedConjImplies(
        Seq(setContains1, setContains2, idxsNeq),
        Seq(recApplyNeq)
      )
    )()
    injectiveFullCheck
  }

  def filterReceiverGood(filter: Exp, reduceExp: Exp)(hasID: Boolean): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val filterReceiverGoodFunc = program.findDomainFunction(DomainsGenerator.filterRecvGoodKey)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(reduceExp)(hasID)

    DomainFuncApp(
      filterReceiverGoodFunc,
      Seq(filter, getreceiverApplied),
      recvType.typVarsMap
    )()
  }

  def filterRecvGoodOrInjCheck(filter: Exp, reduceExp: Exp)(hasID: Boolean): DomainBinExp = {
    Or(
      filterReceiverGood(filter, reduceExp)(hasID),
      injectiveFullCheck(filter, reduceExp)(hasID)
    )()
  }

  def subsetNotInRefs(fs: Exp, reduceExp: Exp, refs: LocalVar)(hasID: Boolean): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val filterNotLostFunc = program.findDomainFunction(DomainsGenerator.subsetNotInRefsKey)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(reduceExp)(hasID)

    DomainFuncApp(filterNotLostFunc,
      Seq(fs, getreceiverApplied, refs),
      recvType.typVarsMap
    )()
  }

  def rHeapElemApplyTo(rHeap: Exp, reduceExp: Exp, arg: Exp)(hasID: Boolean): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val rHeapFuncKey = if (hasID) DomainsGenerator.rHeapElemKeyM else DomainsGenerator.rHeapElemKeyS
    val rHeapFunc: DomainFunc = program.findDomainFunction(rHeapFuncKey)
    DomainFuncApp(
      rHeapFunc,
      Seq(rHeap, reduceExp, arg),
      reduceType.typVarsMap
    )()
  }

  def mapApplyTo(reduceExp: Exp, arg: Exp)(hasID: Boolean): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val mapType = DomainType.apply(program.findDomain(DomainsGenerator.mapDKey), reduceType.typVarsMap)
    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
    // getmapping($c)
    val getmappingApplied = getMappingApply(reduceExp)(hasID)
    DomainFuncApp(
      mapApply,
      Seq(getmappingApplied, arg),
      mapType.typVarsMap
    )()
  }

  def permNonZeroCmp(forallVarInd: Exp, reduceExp: Exp, fieldName: String)(hasID: Boolean): GtCmp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(reduceExp)(hasID)
    val recApplied = DomainFuncApp(
      recApply,
      Seq(getreceiverApplied, forallVarInd),
      recvType.typVarsMap
    )()
    val permFieldAccessed = CurrentPerm(FieldAccess(recApplied, field)())()
    GtCmp(permFieldAccessed, NoPerm()())()
  }

  // generate a forall in the format:
  // (forall $ind: Int :: {$ind in $f}  $ind in $f ==> perm(recApply(getreceiver($c), $ind).val) == write)
  def forallFilterHaveSomeAccess(filter: Exp, reduceExp: Exp,
                                 fieldName: String, oldOption: Option[String])(hasID: Boolean): Forall = {
    val fElemType = filter.typ match {
      case setType : SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val permNonZero = permNonZeroCmp(forallVarInd.localVar, reduceExp, fieldName)(hasID)
    val oldApplied = oldOption match {
      case Some(lbl) => LabelledOld(permNonZero, lbl)()
      case None => permNonZero
    }
    val setContains = AnySetContains(forallVarInd.localVar, filter)()
    val forallTrigger = Trigger(Seq(setContains))()

    Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, oldApplied)())()
  }

//  // generate a forall in the format:
//  // (forall $ind: Int :: {$ind in $f}  $ind in $f ==> perm(recApply(getreceiver($c), $ind).val) == write)
//  def forallFilterHaveAccImpure(filter: Exp, reduceExp: Exp,
//                                fieldName: String, acc: PermExp)(hasID: Boolean): Forall = {
//    val fElemType = filter.typ match {
//      case setType: SetType => setType.elementType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarInd = LocalVarDecl("__ind", fElemType)()
//    val setContains = AnySetContains(forallVarInd.localVar, filter)()
//    val forallTrigger = Trigger(Seq(setContains))()
//    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
//    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
//    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
//    val field = program.findField(fieldName)
//
//    // getreceiver($c)
//    val getreceiverApplied = getReceiverApply(reduceExp)(hasID)
//    val recApplied = DomainFuncApp(
//      recApply,
//      Seq(getreceiverApplied, forallVarInd.localVar),
//      recvType.typVarsMap
//    )()
//
//    val fieldAcc = FieldAccess(recApplied, field)(
//      errT =
//        ReTrafo({
//          case reasons.InsufficientPermission(a) => ReduceReasons.PermissionsError(a, fieldName)
//        })
//    )
//    val accExp = FieldAccessPredicate(fieldAcc, acc)()
//    val output = Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, accExp)())()
//    output
//  }
//
//  // ensures forall i: Int :: {result[i]}  ...
//  def forallFilterResultMap(filter: Exp, reduceExp: Exp, fieldName: String, mapResult: Exp)(hasID: Boolean): Forall = {
//    val fElemType = filter.typ match {
//      case setType: SetType => setType.elementType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarInd = LocalVarDecl("__ind", fElemType)()
//    val setContains = AnySetContains(forallVarInd.localVar, filter)()
//    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
//    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
//    val mapType = DomainType.apply(program.findDomain(DomainsGenerator.mapDKey), reduceType.typVarsMap)
//    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
//    val field = program.findField(fieldName)
//
//    // getreceiver($c)
//    val getreceiverApplied = getReceiverApply(reduceExp)(hasID)
//    val recApplied = DomainFuncApp(
//      recApply,
//      Seq(getreceiverApplied, forallVarInd.localVar),
//      recvType.typVarsMap
//    )()
//    val recAppliedVal = FieldAccess(recApplied, field)()
//
//    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
//    val getmappingApplied = getMappingApply(reduceExp)(hasID)
//    val mappingApplied = DomainFuncApp(
//      mapApply,
//      Seq(getmappingApplied, recAppliedVal),
//      mapType.typVarsMap
//    )()
//    val mapAccessEq = EqCmp(MapLookup(mapResult, forallVarInd.localVar)(), mappingApplied)()
//    val forallTrigger = Trigger(Seq(MapLookup(mapResult, forallVarInd.localVar)()))()
//    val output = Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, mapAccessEq)())()
//    output
//  }
//
//  // ensures forall s: Set[Int] :: {mapDelete(result, s)}
//  def forallMapDelete(filter: Exp, reduceExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
//    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
//
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarSet = LocalVarDecl("__s", fSetType)()
//    val setNotEmpty = NeCmp(forallVarSet.localVar, EmptySet(fSetType.elementType)())()
//
//    val primeAppSetMinus = FuncApp(primeDecl, Seq(reduceExp, AnySetMinus(filter, forallVarSet.localVar)()))()
//    val mapDeleteApplied = applyDomainFunc(
//      "mapDelete",
//      Seq(mapResult, forallVarSet.localVar),
//      reduceType.typVarsMap
//    )
//    val primeEqDelete = EqCmp(primeAppSetMinus, mapDeleteApplied)()
//
//    val implies = Implies(setNotEmpty, primeEqDelete)()
//
//    val forallTrigger = Trigger(Seq(mapDeleteApplied))()
//
//    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), implies)()
//    output
//  }
//
//  //     ensures forall es: Set[Int] :: {mapSubmap(result, es)}
//  def forallMapSubmap(filter: Exp, reduceExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
//    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
//
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarSet = LocalVarDecl("__s", fSetType)()
//    val subset = AnySetSubset(forallVarSet.localVar, filter)()
//    val setNotEqual = NeCmp(forallVarSet.localVar, filter)()
//
//    val primeAppSet = FuncApp(primeDecl, Seq(reduceExp, forallVarSet.localVar))()
//    val mapSubmapApplied = applyDomainFunc("mapSubmap", Seq(mapResult, forallVarSet.localVar),
//      reduceType.typVarsMap)
//    val primeEqDelete = EqCmp(primeAppSet, mapSubmapApplied)()
//    val implies = foldedConjImplies(Seq(subset, setNotEqual), Seq(subset, setNotEqual, primeEqDelete))
//    val forallTrigger = Trigger(Seq(mapSubmapApplied))()
//
//    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), implies)()
//    output
//  }
//
//  def forallDummyExtensionality(filter: Exp, reduceExp: Exp, hasID: Boolean, primeDecl: ast.Function): Forall = {
//    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
//
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//
//    val forallVarSet = LocalVarDecl("__s", fSetType)()
//    val primeApplied = FuncApp(primeDecl, Seq(reduceExp, forallVarSet.localVar))()
//    val reduceApplied1 = reducePrimeApply()
//      applyDomainFunc(
//      DomainsGenerator.reduceApplyPrimeKey,
//      Seq(reduceExp, primeApplied),
//      reduceType.typVarsMap
//    )
//    val dummyApplied = applyDomainFunc(
//      DomainsGenerator.reduceApplyreduceApplyDummyKey,
//      Seq(EqCmp(forallVarSet.localVar, filter)()),
//      reduceType.typVarsMap
//    )
//
//    val forallTrigger = Trigger(Seq(reduceApplied1))()
//
//    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), dummyApplied)()
//    output
//  }
//
//  def forallDisjUnion(filter: Exp, reduceExp: Exp, primeDecl: ast.Function, mapResult: Exp) : Forall = {
//    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarSet1 = LocalVarDecl("__s1", fSetType)()
//    val forallVarSet2 = LocalVarDecl("__s2", fSetType)()
//    val disjApplied = applyDomainFunc(
//      DomainsGenerator.disjUnionKey,
//      Seq(forallVarSet1.localVar, forallVarSet2.localVar, filter),
//      reduceType.typVarsMap
//    )
//
//    val snapPrime1 = FuncApp(primeDecl, Seq(reduceExp, forallVarSet1.localVar))()
//    val snapPrime2 = FuncApp(primeDecl, Seq(reduceExp, forallVarSet2.localVar))()
//
//    val reduceApplyPrime1 = applyDomainFunc(
//      DomainsGenerator.reduceApplyPrimeKey,
//      Seq(reduceExp, snapPrime1),
//      reduceType.typVarsMap
//    )
//    val reduceApplyPrime2 = applyDomainFunc(
//      DomainsGenerator.reduceApplyPrimeKey,
//      Seq(reduceExp, snapPrime2),
//      reduceType.typVarsMap
//    )
//    val reduceApplyResult = applyDomainFunc(
//      DomainsGenerator.reduceApplyPrimeKey,
//      Seq(reduceExp, mapResult),
//      reduceType.typVarsMap
//    )
//
//    val getOpApplied = applyDomainFunc(DomainsGenerator.reduceGetOperKey, Seq(reduceExp), reduceType.typVarsMap)
//
//    val opApplied = applyDomainFunc(
//      DomainsGenerator.opApplyKey,
//      Seq(getOpApplied, reduceApplyPrime1, reduceApplyPrime2),
//      reduceType.typVarsMap
//    )
//
//    val equals = EqCmp(reduceApplyResult, opApplied)()
//    val implies = foldedConjImplies(Seq(disjApplied), Seq(disjApplied, equals))
//    val trigger = Trigger(Seq(disjApplied))()
//    val output = Forall(Seq(forallVarSet1, forallVarSet2), Seq(trigger), implies)()
//    output
//  }

}

object AxiomHelper {
  def tupleFieldToString(t: (Type, Type, Type), fieldID: String): String = {
    // replace letters [ and ] with _
    ("__getrh_" + t._1.toString() + "_" + t._2.toString() + "_" + t._3.toString() + "_" + fieldID
      ).replaceAll("[\\[\\]]", "_")
  }
}