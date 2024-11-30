package viper.silver.plugin.hreduce.util

import viper.silver.ast
import viper.silver.ast.utility.Expressions
import viper.silver.ast._
import viper.silver.plugin.hreduce.{DomainsGenerator, ReduceReasons}
import viper.silver.verifier.reasons

class AxiomHelper(program: Program) {

  //  def getStartLabel: Label = {
  //    Label(s"${labelPrefix}l0", Seq())()
  //  }

  def labelPrefix: String = {
    "_reduceLabel"
  }

  def rHeapPrefix: String = {
    "_rh"
  }

  def methodLabelPrefix : String = {
    "_methodLabel"
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

  def reduceApply(rHeap: Exp, reduce: Exp, filter: Exp): DomainFuncApp = {
    val reduceApply = program.findDomainFunction(DomainsGenerator.reduceApplyKey)

    DomainFuncApp(
      reduceApply,
      Seq(rHeap, reduce, filter),
      reduce.typ.asInstanceOf[DomainType].typVarsMap
    )()
  }

  def foldedConjImplies(lhsExps: Seq[Exp], rhsExps: Seq[Exp]): Exp = {
    def foldConj(exps: Seq[Exp]): Exp = {
      if (exps.length == 1) {
        exps.head
      } else if (exps.length == 2) {
        And(exps(0), exps(1))()
      } else {
        And(exps.head, foldConj(exps.tail))()
      }
    }
    Implies(foldConj(lhsExps), foldConj(rhsExps))()
  }

  def injectiveFullCheck(filter: Exp, reduceExp: Exp): QuantifiedExp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val getreceiver = program.findDomainFunction(DomainsGenerator.reduceGetRecvKey)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(reduceExp),
      reduceType.typVarsMap
    )()

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

  def filterReceiverGood(filter: Exp, reduceExp: Exp): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val filterReceiverGoodFunc = program.findDomainFunction(DomainsGenerator.filterRecvGoodKey)
    val getreceiver = program.findDomainFunction(DomainsGenerator.reduceGetRecvKey)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(reduceExp),
      reduceType.typVarsMap
    )()
    DomainFuncApp(
      filterReceiverGoodFunc,
      Seq(filter, getreceiverApplied),
      recvType.typVarsMap
    )()
  }


  def filterRecvGoodOrInjCheck(filter: Exp, reduceExp: Exp): DomainBinExp = {
    Or(
      filterReceiverGood(filter, reduceExp),
      injectiveFullCheck(filter, reduceExp)
    )()
  }

  def subsetNotInRefs(fs: Exp, reduceExp: Exp, refs: LocalVar): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val filterNotLostFunc = program.findDomainFunction(DomainsGenerator.subsetNotInRefsKey)
    val getreceiver = program.findDomainFunction(DomainsGenerator.reduceGetRecvKey)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(getreceiver, Seq(reduceExp),
      reduceType.typVarsMap)()

    DomainFuncApp(filterNotLostFunc,
      Seq(fs, getreceiverApplied, refs),
      recvType.typVarsMap
    )()
  }

  def rHeapElemApplyTo(reduceExp: Exp, rHeap: Exp, arg: Exp): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val rHeapFunc: DomainFunc = program.findDomainFunction(DomainsGenerator.rHeapElemKey)
    DomainFuncApp(
      rHeapFunc,
      Seq(reduceExp, rHeap, arg),
      reduceType.typVarsMap
    )()
  }

  def mapApplyTo(reduceExp: Exp, arg: Exp): DomainFuncApp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val mapType = DomainType.apply(program.findDomain(DomainsGenerator.mapDKey), reduceType.typVarsMap)
    val getmapping = program.findDomainFunction(DomainsGenerator.reduceGetMappingKey)
    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
    // getmapping($c)
    val getmappingApplied = DomainFuncApp(
      getmapping,
      Seq(reduceExp),
      reduceType.typVarsMap
    )()
    DomainFuncApp(
      mapApply,
      Seq(getmappingApplied, arg),
      mapType.typVarsMap
    )()
  }

  def permNonZeroCmp(forallVarInd: Exp, reduceExp: Exp, fieldName: String): GtCmp = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val getreceiver = program.findDomainFunction(DomainsGenerator.reduceGetRecvKey)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(reduceExp),
      reduceType.typVarsMap
    )()
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
                                 fieldName: String, oldOption: Option[String]): Forall = {
    val fElemType = filter.typ match {
      case setType : SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val permNonZero = permNonZeroCmp(forallVarInd.localVar, reduceExp, fieldName)
    val oldApplied = oldOption match {
      case Some(lbl) => LabelledOld(permNonZero, lbl)()
      case None => permNonZero
    }
    val setContains = AnySetContains(forallVarInd.localVar, filter)()
    val forallTrigger = Trigger(Seq(setContains))()

    Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, oldApplied)())()
  }

  // generate a forall in the format:
  // (forall $ind: Int :: {$ind in $f}  $ind in $f ==> perm(recApply(getreceiver($c), $ind).val) == write)
  def forallFilterHaveAccImpure(filter: Exp, reduceExp: Exp,
                                fieldName: String, acc: PermExp): Forall = {
    val fElemType = filter.typ match {
      case setType: SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val setContains = AnySetContains(forallVarInd.localVar, filter)()
    val forallTrigger = Trigger(Seq(setContains))()
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val getreceiver = program.findDomainFunction(DomainsGenerator.reduceGetRecvKey)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(reduceExp),
      reduceType.typVarsMap
    )()
    val recApplied = DomainFuncApp(
      recApply,
      Seq(getreceiverApplied, forallVarInd.localVar),
      recvType.typVarsMap
    )()

    val fieldAcc = FieldAccess(recApplied, field)(
      errT =
        ReTrafo({
          case reasons.InsufficientPermission(a) => ReduceReasons.PermissionsError(a, fieldName)
        })
    )
    val accExp = FieldAccessPredicate(fieldAcc, acc)()
    val output = Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, accExp)())()
    output
  }

  // ensures forall i: Int :: {result[i]}  ...
  def forallFilterResultMap(filter: Exp, reduceExp: Exp, fieldName: String, mapResult: Exp): Forall = {
    val fElemType = filter.typ match {
      case setType: SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val setContains = AnySetContains(forallVarInd.localVar, filter)()
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val recvType = DomainType.apply(program.findDomain(DomainsGenerator.recDKey), reduceType.typVarsMap)
    val mapType = DomainType.apply(program.findDomain(DomainsGenerator.mapDKey), reduceType.typVarsMap)
    val getreceiver = program.findDomainFunction(DomainsGenerator.reduceGetRecvKey)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(reduceExp),
      reduceType.typVarsMap
    )()
    val recApplied = DomainFuncApp(
      recApply,
      Seq(getreceiverApplied, forallVarInd.localVar),
      recvType.typVarsMap
    )()
    val recAppliedVal = FieldAccess(recApplied, field)()

    val getmapping = program.findDomainFunction(DomainsGenerator.reduceGetMappingKey)
    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
    val getmappingApplied = DomainFuncApp(
      getmapping,
      Seq(reduceExp),
      reduceType.typVarsMap
    )()
    val mappingApplied = DomainFuncApp(
      mapApply,
      Seq(getmappingApplied, recAppliedVal),
      mapType.typVarsMap
    )()
    val mapAccessEq = EqCmp(MapLookup(mapResult, forallVarInd.localVar)(), mappingApplied)()
    val forallTrigger = Trigger(Seq(MapLookup(mapResult, forallVarInd.localVar)()))()
    val output = Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, mapAccessEq)())()
    output
  }

  // ensures forall s: Set[Int] :: {mapDelete(result, s)}
  def forallMapDelete(filter: Exp, reduceExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]

    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarSet = LocalVarDecl("__s", fSetType)()
    val setNotEmpty = NeCmp(forallVarSet.localVar, EmptySet(fSetType.elementType)())()

    val primeAppSetMinus = FuncApp(primeDecl, Seq(reduceExp, AnySetMinus(filter, forallVarSet.localVar)()))()
    val mapDeleteApplied = applyDomainFunc(
      "mapDelete",
      Seq(mapResult, forallVarSet.localVar),
      reduceType.typVarsMap
    )
    val primeEqDelete = EqCmp(primeAppSetMinus, mapDeleteApplied)()

    val implies = Implies(setNotEmpty, primeEqDelete)()

    val forallTrigger = Trigger(Seq(mapDeleteApplied))()

    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), implies)()
    output
  }

  //     ensures forall es: Set[Int] :: {mapSubmap(result, es)}
  def forallMapSubmap(filter: Exp, reduceExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]

    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarSet = LocalVarDecl("__s", fSetType)()
    val subset = AnySetSubset(forallVarSet.localVar, filter)()
    val setNotEqual = NeCmp(forallVarSet.localVar, filter)()

    val primeAppSet = FuncApp(primeDecl, Seq(reduceExp, forallVarSet.localVar))()
    val mapSubmapApplied = applyDomainFunc("mapSubmap", Seq(mapResult, forallVarSet.localVar),
      reduceType.typVarsMap)
    val primeEqDelete = EqCmp(primeAppSet, mapSubmapApplied)()
    val implies = foldedConjImplies(Seq(subset, setNotEqual), Seq(subset, setNotEqual, primeEqDelete))
    val forallTrigger = Trigger(Seq(mapSubmapApplied))()

    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), implies)()
    output
  }

  def forallDummyExtensionality(filter: Exp, reduceExp: Exp, primeDecl: ast.Function): Forall = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]

    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }

    val forallVarSet = LocalVarDecl("__s", fSetType)()
    val primeApplied = FuncApp(primeDecl, Seq(reduceExp, forallVarSet.localVar))()
    val reduceApplied1 = applyDomainFunc(
      DomainsGenerator.reduceApplyPrimeKey,
      Seq(reduceExp, primeApplied),
      reduceType.typVarsMap
    )
    val dummyApplied = applyDomainFunc(
      DomainsGenerator.reduceApplyDummyKey,
      Seq(EqCmp(forallVarSet.localVar, filter)()),
      reduceType.typVarsMap
    )

    val forallTrigger = Trigger(Seq(reduceApplied1))()

    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), dummyApplied)()
    output
  }

  def forallDisjUnion(filter: Exp, reduceExp: Exp, primeDecl: ast.Function, mapResult: Exp) : Forall = {
    val reduceType = reduceExp.typ.asInstanceOf[DomainType]
    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarSet1 = LocalVarDecl("__s1", fSetType)()
    val forallVarSet2 = LocalVarDecl("__s2", fSetType)()
    val disjApplied = applyDomainFunc(
      DomainsGenerator.disjUnionKey,
      Seq(forallVarSet1.localVar, forallVarSet2.localVar, filter),
      reduceType.typVarsMap
    )

    val snapPrime1 = FuncApp(primeDecl, Seq(reduceExp, forallVarSet1.localVar))()
    val snapPrime2 = FuncApp(primeDecl, Seq(reduceExp, forallVarSet2.localVar))()

    val reduceApplyPrime1 = applyDomainFunc(
      DomainsGenerator.reduceApplyPrimeKey,
      Seq(reduceExp, snapPrime1),
      reduceType.typVarsMap
    )
    val reduceApplyPrime2 = applyDomainFunc(
      DomainsGenerator.reduceApplyPrimeKey,
      Seq(reduceExp, snapPrime2),
      reduceType.typVarsMap
    )
    val reduceApplyResult = applyDomainFunc(
      DomainsGenerator.reduceApplyPrimeKey,
      Seq(reduceExp, mapResult),
      reduceType.typVarsMap
    )

    val getOpApplied = applyDomainFunc(DomainsGenerator.reduceGetOperKey, Seq(reduceExp), reduceType.typVarsMap)

    val opApplied = applyDomainFunc(
      DomainsGenerator.opApplyKey,
      Seq(getOpApplied, reduceApplyPrime1, reduceApplyPrime2),
      reduceType.typVarsMap
    )

    val equals = EqCmp(reduceApplyResult, opApplied)()
    val implies = foldedConjImplies(Seq(disjApplied), Seq(disjApplied, equals))
    val trigger = Trigger(Seq(disjApplied))()
    val output = Forall(Seq(forallVarSet1, forallVarSet2), Seq(trigger), implies)()
    output
  }

}

object AxiomHelper {
  def tupleFieldToString(t: (Type, Type, Type), fieldID: String): String = {
    // replace letters [ and ] with _
    ("__getfh_" + t._1.toString() + "_" + t._2.toString() + "_" + t._3.toString() + "_" + fieldID
      ).replaceAll("[\\[\\]]", "_")
  }
}