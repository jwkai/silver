package viper.silver.plugin.crimp.util

import viper.silver.ast._
import viper.silver.ast.utility.Expressions
import viper.silver.plugin.crimp.DomainsGenerator

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
    "_crimpLabel"
  }

  def cHeapPrefix: String = {
    "_ch"
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

  def crimpApply(fuel: Exp, cHeap: Exp, crimp: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
    val crimpApply = if (hasID) DomainsGenerator.crimpApplyKeyM else DomainsGenerator.crimpApplyKeyS
    applyDomainFunc(
      crimpApply,
      Seq(fuel, cHeap, crimp, filter),
      crimp.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

//  def crimpPrimeApply(cHeap: Exp, crimp: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
//    val crimpApplyPrime = if (hasID) DomainsGenerator.crimpApplyPrimeKeyM else DomainsGenerator.crimpApplyPrimeKeyS
//    applyDomainFunc(
//      crimpApplyPrime,
//      Seq(cHeap, crimp, filter),
//      crimp.typ.asInstanceOf[DomainType].typVarsMap
//    )
//  }

  def crimpDummyApply(fuel: Exp, cHeap: Exp, crimp: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
    val crimpApplyDummyKey = if (hasID) DomainsGenerator.crimpApplyDummyKeyM else DomainsGenerator.crimpApplyDummyKeyS
    applyDomainFunc(
      crimpApplyDummyKey,
      Seq(crimpApply(fuel, cHeap, crimp, filter)(hasID)),
      crimp.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

//  def exhaleCrimpSetApply(cHeap: Exp, crimp: Exp, filter: Exp, fieldId: Exp)(hasID: Boolean): DomainFuncApp = {
//    val exhaleCrimpSetKey = if (hasID) DomainsGenerator.exhaleCrimpSetKeyM else DomainsGenerator.exhaleCrimpSetKeyS
//    applyDomainFunc(
//      exhaleCrimpSetKey,
//      Seq(cHeap, crimp, filter, fieldId),
//      crimp.typ.asInstanceOf[DomainType].typVarsMap
//    )
//  }

  def trigExtApply(fuel1: Exp, cHeap1: Exp, fuel2: Exp, cHeap2: Exp, crimp: Exp, filter: Exp)(hasID: Boolean): DomainFuncApp = {
    val trigExtKey = if (hasID) DomainsGenerator.trigExtKeyM else DomainsGenerator.trigExtKeyS
    applyDomainFunc(
      trigExtKey,
      Seq(crimpApply(fuel1, cHeap1, crimp, filter)(hasID), crimpApply(fuel2, cHeap2, crimp, filter)(hasID)),
      crimp.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def getReceiverApply(crimp: Exp)(hasID: Boolean): DomainFuncApp = {
    val crimpGetRecvKey = if (hasID) DomainsGenerator.crimpGetRecvKeyM else DomainsGenerator.crimpGetRecvKeyS
    applyDomainFunc(
      crimpGetRecvKey,
      Seq(crimp),
      crimp.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def getMappingApply(crimp: Exp)(hasID: Boolean): DomainFuncApp = {
    val crimpGetMappingKey = if (hasID) DomainsGenerator.crimpGetMappingKeyM else DomainsGenerator.crimpGetMappingKeyS
    applyDomainFunc(
      crimpGetMappingKey,
      Seq(crimp),
      crimp.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def trigDelKeyApply(fuel: Exp, cHeap: Exp, crimp: Exp, filter: Exp, key: Exp)(hasID: Boolean): DomainFuncApp = {
    val trigDelKey1Key = if (hasID) DomainsGenerator.trigDelKey1KeyM else DomainsGenerator.trigDelKey1KeyS
    val crimpApplyApp = crimpApply(fuel, cHeap, crimp, filter)(hasID)
    applyDomainFunc(
      trigDelKey1Key,
      Seq(crimpApplyApp, key),
      crimp.typ.asInstanceOf[DomainType].typVarsMap
    )
  }

  def trigDelBlockApply(fuel: Exp, cHeap: Exp, crimp: Exp, filter: Exp, keySet: Exp)(hasID: Boolean): DomainFuncApp = {
    val trigDelBlockKey = if (hasID) DomainsGenerator.trigDelBlockKeyM else DomainsGenerator.trigDelBlockKeyS
    val crimpApplyApp = crimpApply(fuel, cHeap, crimp, filter)(hasID)
    applyDomainFunc(
      trigDelBlockKey,
      Seq(crimpApplyApp, keySet),
      crimp.typ.asInstanceOf[DomainType].typVarsMap
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

  def foldedConjImplies(lhsExps: Seq[Exp], chsExps: Seq[Exp]): Exp = {
    Implies(foldConj(lhsExps), foldConj(chsExps))()
  }

  def injectiveFullCheck(filter: Exp, crimpExp: Exp)(hasID: Boolean): QuantifiedExp = {
    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), crimpType.typVarsMap)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(crimpExp)(hasID)

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

  def filterReceiverGood(filter: Exp, crimpExp: Exp)(hasID: Boolean): DomainFuncApp = {
    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), crimpType.typVarsMap)
    val filterReceiverGoodFunc = program.findDomainFunction(DomainsGenerator.filterRecvGoodKey)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(crimpExp)(hasID)

    DomainFuncApp(
      filterReceiverGoodFunc,
      Seq(filter, getreceiverApplied),
      recvType.typVarsMap
    )()
  }

  def filterRecvGoodOrInjCheck(filter: Exp, crimpExp: Exp)(hasID: Boolean): DomainBinExp = {
    Or(
      filterReceiverGood(filter, crimpExp)(hasID),
      injectiveFullCheck(filter, crimpExp)(hasID)
    )()
  }

  def subsetNotInRefs(fs: Exp, crimpExp: Exp, refs: LocalVar)(hasID: Boolean): DomainFuncApp = {
    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), crimpType.typVarsMap)
    val filterNotLostFunc = program.findDomainFunction(DomainsGenerator.subsetNotInRefsKey)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(crimpExp)(hasID)

    DomainFuncApp(filterNotLostFunc,
      Seq(fs, getreceiverApplied, refs),
      recvType.typVarsMap
    )()
  }

  def cHeapElemApplyTo(cHeap: Exp, crimpExp: Exp, arg: Exp)(hasID: Boolean): DomainFuncApp = {
    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
    val cHeapFuncKey = if (hasID) DomainsGenerator.cHeapElemKeyM else DomainsGenerator.cHeapElemKeyS
    val cHeapFunc: DomainFunc = program.findDomainFunction(cHeapFuncKey)
    DomainFuncApp(
      cHeapFunc,
      Seq(cHeap, crimpExp, arg),
      crimpType.typVarsMap
    )()
  }

  def mapApplyTo(crimpExp: Exp, arg: Exp)(hasID: Boolean): DomainFuncApp = {
    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
    val mapType = DomainType.apply(program.findDomain(DomainsGenerator.mapDKey), crimpType.typVarsMap)
    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
    // getmapping($c)
    val getmappingApplied = getMappingApply(crimpExp)(hasID)
    DomainFuncApp(
      mapApply,
      Seq(getmappingApplied, arg),
      mapType.typVarsMap
    )()
  }

  def permNonZeroCmp(forallVarInd: Exp, crimpExp: Exp, fieldName: String)(hasID: Boolean): GtCmp = {
    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), crimpType.typVarsMap)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = getReceiverApply(crimpExp)(hasID)
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
  def forallFilterHaveSomeAccess(filter: Exp, crimpExp: Exp,
                                 fieldName: String, oldOption: Option[String])(hasID: Boolean): Forall = {
    val fElemType = filter.typ match {
      case setType : SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val permNonZero = permNonZeroCmp(forallVarInd.localVar, crimpExp, fieldName)(hasID)
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
//  def forallFilterHaveAccImpure(filter: Exp, crimpExp: Exp,
//                                fieldName: String, acc: PermExp)(hasID: Boolean): Forall = {
//    val fElemType = filter.typ match {
//      case setType: SetType => setType.elementType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarInd = LocalVarDecl("__ind", fElemType)()
//    val setContains = AnySetContains(forallVarInd.localVar, filter)()
//    val forallTrigger = Trigger(Seq(setContains))()
//    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
//    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), crimpType.typVarsMap)
//    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
//    val field = program.findField(fieldName)
//
//    // getreceiver($c)
//    val getreceiverApplied = getReceiverApply(crimpExp)(hasID)
//    val recApplied = DomainFuncApp(
//      recApply,
//      Seq(getreceiverApplied, forallVarInd.localVar),
//      recvType.typVarsMap
//    )()
//
//    val fieldAcc = FieldAccess(recApplied, field)(
//      errT =
//        ReTrafo({
//          case reasons.InsufficientPermission(a) => CrimpReasons.PermissionsError(a, fieldName)
//        })
//    )
//    val accExp = FieldAccessPredicate(fieldAcc, acc)()
//    val output = Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, accExp)())()
//    output
//  }
//
//  // ensures forall i: Int :: {result[i]}  ...
//  def forallFilterResultMap(filter: Exp, crimpExp: Exp, fieldName: String, mapResult: Exp)(hasID: Boolean): Forall = {
//    val fElemType = filter.typ match {
//      case setType: SetType => setType.elementType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarInd = LocalVarDecl("__ind", fElemType)()
//    val setContains = AnySetContains(forallVarInd.localVar, filter)()
//    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
//    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), crimpType.typVarsMap)
//    val mapType = DomainType.apply(program.findDomain(DomainsGenerator.mapDKey), crimpType.typVarsMap)
//    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
//    val field = program.findField(fieldName)
//
//    // getreceiver($c)
//    val getreceiverApplied = getReceiverApply(crimpExp)(hasID)
//    val recApplied = DomainFuncApp(
//      recApply,
//      Seq(getreceiverApplied, forallVarInd.localVar),
//      recvType.typVarsMap
//    )()
//    val recAppliedVal = FieldAccess(recApplied, field)()
//
//    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
//    val getmappingApplied = getMappingApply(crimpExp)(hasID)
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
//  def forallMapDelete(filter: Exp, crimpExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
//    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
//
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarSet = LocalVarDecl("__s", fSetType)()
//    val setNotEmpty = NeCmp(forallVarSet.localVar, EmptySet(fSetType.elementType)())()
//
//    val primeAppSetMinus = FuncApp(primeDecl, Seq(crimpExp, AnySetMinus(filter, forallVarSet.localVar)()))()
//    val mapDeleteApplied = applyDomainFunc(
//      "mapDelete",
//      Seq(mapResult, forallVarSet.localVar),
//      crimpType.typVarsMap
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
//  def forallMapSubmap(filter: Exp, crimpExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
//    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
//
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarSet = LocalVarDecl("__s", fSetType)()
//    val subset = AnySetSubset(forallVarSet.localVar, filter)()
//    val setNotEqual = NeCmp(forallVarSet.localVar, filter)()
//
//    val primeAppSet = FuncApp(primeDecl, Seq(crimpExp, forallVarSet.localVar))()
//    val mapSubmapApplied = applyDomainFunc("mapSubmap", Seq(mapResult, forallVarSet.localVar),
//      crimpType.typVarsMap)
//    val primeEqDelete = EqCmp(primeAppSet, mapSubmapApplied)()
//    val implies = foldedConjImplies(Seq(subset, setNotEqual), Seq(subset, setNotEqual, primeEqDelete))
//    val forallTrigger = Trigger(Seq(mapSubmapApplied))()
//
//    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), implies)()
//    output
//  }
//
//  def forallDummyExtensionality(filter: Exp, crimpExp: Exp, hasID: Boolean, primeDecl: ast.Function): Forall = {
//    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
//
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//
//    val forallVarSet = LocalVarDecl("__s", fSetType)()
//    val primeApplied = FuncApp(primeDecl, Seq(crimpExp, forallVarSet.localVar))()
//    val crimpApplied1 = crimpPrimeApply()
//      applyDomainFunc(
//      DomainsGenerator.crimpApplyPrimeKey,
//      Seq(crimpExp, primeApplied),
//      crimpType.typVarsMap
//    )
//    val dummyApplied = applyDomainFunc(
//      DomainsGenerator.crimpApplycrimpApplyDummyKey,
//      Seq(EqCmp(forallVarSet.localVar, filter)()),
//      crimpType.typVarsMap
//    )
//
//    val forallTrigger = Trigger(Seq(crimpApplied1))()
//
//    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), dummyApplied)()
//    output
//  }
//
//  def forallDisjUnion(filter: Exp, crimpExp: Exp, primeDecl: ast.Function, mapResult: Exp) : Forall = {
//    val crimpType = crimpExp.typ.asInstanceOf[DomainType]
//    val fSetType = filter.typ match {
//      case setType: SetType => setType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    val forallVarSet1 = LocalVarDecl("__s1", fSetType)()
//    val forallVarSet2 = LocalVarDecl("__s2", fSetType)()
//    val disjApplied = applyDomainFunc(
//      DomainsGenerator.disjUnionKey,
//      Seq(forallVarSet1.localVar, forallVarSet2.localVar, filter),
//      crimpType.typVarsMap
//    )
//
//    val snapPrime1 = FuncApp(primeDecl, Seq(crimpExp, forallVarSet1.localVar))()
//    val snapPrime2 = FuncApp(primeDecl, Seq(crimpExp, forallVarSet2.localVar))()
//
//    val crimpApplyPrime1 = applyDomainFunc(
//      DomainsGenerator.crimpApplyPrimeKey,
//      Seq(crimpExp, snapPrime1),
//      crimpType.typVarsMap
//    )
//    val crimpApplyPrime2 = applyDomainFunc(
//      DomainsGenerator.crimpApplyPrimeKey,
//      Seq(crimpExp, snapPrime2),
//      crimpType.typVarsMap
//    )
//    val crimpApplyResult = applyDomainFunc(
//      DomainsGenerator.crimpApplyPrimeKey,
//      Seq(crimpExp, mapResult),
//      crimpType.typVarsMap
//    )
//
//    val getOpApplied = applyDomainFunc(DomainsGenerator.crimpGetOperKey, Seq(crimpExp), crimpType.typVarsMap)
//
//    val opApplied = applyDomainFunc(
//      DomainsGenerator.opApplyKey,
//      Seq(getOpApplied, crimpApplyPrime1, crimpApplyPrime2),
//      crimpType.typVarsMap
//    )
//
//    val equals = EqCmp(crimpApplyResult, opApplied)()
//    val implies = foldedConjImplies(Seq(disjApplied), Seq(disjApplied, equals))
//    val trigger = Trigger(Seq(disjApplied))()
//    val output = Forall(Seq(forallVarSet1, forallVarSet2), Seq(trigger), implies)()
//    output
//  }

}

object AxiomHelper {
  def tupleFieldToString(t: (Type, Type, Type), fieldID: String): String = {
    // replace letters [ and ] with _
    ("__getch_" + t._1.toString() + "_" + t._2.toString() + "_" + t._3.toString() + "_" + fieldID
      ).replaceAll("[\\[\\]]", "_")
  }
}