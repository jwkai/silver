package viper.silver.plugin.toto.util

import viper.silver.ast
import viper.silver.ast.Bool.foldLeft
import viper.silver.ast.utility.Expressions
import viper.silver.ast._
import viper.silver.plugin.toto.ast.AFHeap
import viper.silver.plugin.toto.{DomainsGenerator, FoldReasons}
import viper.silver.verifier.reasons

class AxiomHelper(program: Program) {

//  def getStartLabel: Label = {
//    Label(s"${labelPrefix}l0", Seq())()
//  }

  def labelPrefix: String = {
    "_compLabel"
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
  def applyDomainFunc(domainFuncName: String, applyTo: Seq[Exp],
                      typMap: Map[TypeVar, Type]): DomainFuncApp = {
    val domainFunc = program.findDomainFunction(domainFuncName)
    DomainFuncApp(domainFunc, applyTo, typMap)()
  }

  def compApply(fHeap: Exp, comp: Exp, filter: Exp): DomainFuncApp = {
    val compApply = program.findDomainFunction(DomainsGenerator.compApplyKey)

    DomainFuncApp(
      compApply,
      Seq(fHeap, comp, filter),
      comp.typ.asInstanceOf[DomainType].typVarsMap
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

  def filterReceiverGood(filter: Exp, compExp: Exp): DomainFuncApp = {
    val compType = compExp.typ.asInstanceOf[DomainType]
    val filterReceiverGoodFunc = program.findDomainFunction(DomainsGenerator.filterRecvGoodKey)
    val getreceiver = program.findDomainFunction(DomainsGenerator.compGetRecvKey)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(compExp),
      compType.typVarsMap
    )()
    DomainFuncApp(
      filterReceiverGoodFunc,
      Seq(filter, getreceiverApplied),
      compType.typVarsMap
    )()
  }

  def subsetNotInRefs(fs: Exp, compExp: Exp, refs: LocalVar): DomainFuncApp = {
    val compType = compExp.typ.asInstanceOf[DomainType]
    val filterNotLostFunc = program.findDomainFunction(DomainsGenerator.subsetNotInRefsKey)
    val getreceiver = program.findDomainFunction(DomainsGenerator.compGetRecvKey)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(getreceiver, Seq(compExp),
      compType.typVarsMap)()

    DomainFuncApp(filterNotLostFunc,
      Seq(fs, getreceiverApplied, refs),
      compType.typVarsMap
    )()
  }

  def fHeapElemApplyTo(fHeap: AFHeap, arg: Exp): DomainFuncApp = {
    val fHeapType = AFHeap.getType.asInstanceOf[DomainType]
    DomainFuncApp(
      program.findDomainFunction(DomainsGenerator.fHeapElemKey),
      Seq(fHeap, arg),
      fHeapType.typVarsMap
    )()
  }

  def mapApplyTo(compExp: Exp, arg: Exp): DomainFuncApp = {
    val compType = compExp.typ.asInstanceOf[DomainType]
    val getmapping = program.findDomainFunction(DomainsGenerator.compGetMappingKey)
    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
    // getmapping($c)
    val getmappingApplied = DomainFuncApp(
      getmapping,
      Seq(compExp),
      compType.typVarsMap
    )()
    DomainFuncApp(
      mapApply,
      Seq(getmappingApplied, arg),
      compType.typVarsMap
    )()
  }

  def permNonZeroCmp(forallVarInd: Exp, compExp: Exp, fieldName: String): GtCmp = {
    val compType = compExp.typ.asInstanceOf[DomainType]
    val getreceiver = program.findDomainFunction(DomainsGenerator.compGetRecvKey)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(compExp),
      compType.typVarsMap
    )()
    val recApplied = DomainFuncApp(
      recApply,
      Seq(getreceiverApplied, forallVarInd),
      compType.typVarsMap
    )()
    val permFieldAccessed = CurrentPerm(FieldAccess(recApplied, field)())()
    GtCmp(permFieldAccessed, NoPerm()())()
  }

  // generate a forall in the format:
  // (forall $ind: Int :: {$ind in $f}  $ind in $f ==> perm(recApply(getreceiver($c), $ind).val) == write)
  def forallFilterHaveSomeAccess(filter: Exp, compExp: Exp,
                                 fieldName: String, oldOption: Option[String]): Forall = {
    val fElemType = filter.typ match {
      case setType : SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val permNonZero = permNonZeroCmp(forallVarInd.localVar, compExp, fieldName)
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
  def forallFilterHaveAccImpure(filter: Exp, compExp: Exp,
                                  fieldName: String, acc: PermExp): Forall = {
    val fElemType = filter.typ match {
      case setType: SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val setContains = AnySetContains(forallVarInd.localVar, filter)()
    val forallTrigger = Trigger(Seq(setContains))()
    val compType = compExp.typ.asInstanceOf[DomainType]
    val getreceiver = program.findDomainFunction(DomainsGenerator.compGetRecvKey)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(compExp),
      compType.typVarsMap
    )()
    val recApplied = DomainFuncApp(
      recApply,
      Seq(getreceiverApplied, forallVarInd.localVar),
      compType.typVarsMap
    )()

    val fieldAcc = FieldAccess(recApplied, field)(
      errT =
        ReTrafo({
          case reasons.InsufficientPermission(a) => FoldReasons.PermissionsError(a, fieldName)
        })
    )
    val accExp = FieldAccessPredicate(fieldAcc, acc)()
    val output = Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, accExp)())()
    output
  }

  // ensures forall i: Int :: {result[i]}  ...
  def forallFilterResultMap(filter: Exp, compExp: Exp, fieldName: String, mapResult: Exp): Forall = {
    val fElemType = filter.typ match {
      case setType: SetType => setType.elementType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarInd = LocalVarDecl("__ind", fElemType)()
    val setContains = AnySetContains(forallVarInd.localVar, filter)()
    val compType = compExp.typ.asInstanceOf[DomainType]
    val getreceiver = program.findDomainFunction(DomainsGenerator.compGetRecvKey)
    val recApply = program.findDomainFunction(DomainsGenerator.recApplyKey)
    val field = program.findField(fieldName)

    // getreceiver($c)
    val getreceiverApplied = DomainFuncApp(
      getreceiver,
      Seq(compExp),
      compType.typVarsMap
    )()
    val recApplied = DomainFuncApp(
      recApply,
      Seq(getreceiverApplied, forallVarInd.localVar),
      compType.typVarsMap
    )()
    val recAppliedVal = FieldAccess(recApplied, field)()

    val getmapping = program.findDomainFunction(DomainsGenerator.compGetMappingKey)
    val mapApply = program.findDomainFunction(DomainsGenerator.mapApplyKey)
    val getmappingApplied = DomainFuncApp(
      getmapping,
      Seq(compExp),
      compType.typVarsMap
    )()
    val mappingApplied = DomainFuncApp(
      mapApply,
      Seq(getmappingApplied, recAppliedVal),
      compType.typVarsMap
    )()
    val mapAccessEq = EqCmp(MapLookup(mapResult, forallVarInd.localVar)(), mappingApplied)()
    val forallTrigger = Trigger(Seq(MapLookup(mapResult, forallVarInd.localVar)()))()
    val output = Forall(Seq(forallVarInd), Seq(forallTrigger), Implies(setContains, mapAccessEq)())()
    output
  }

  // ensures forall s: Set[Int] :: {mapDelete(result, s)}
  def forallMapDelete(filter: Exp, compExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
    val compType = compExp.typ.asInstanceOf[DomainType]

    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarSet = LocalVarDecl("__s", fSetType)()
    val setNotEmpty = NeCmp(forallVarSet.localVar, EmptySet(fSetType.elementType)())()

    val primeAppSetMinus = FuncApp(primeDecl, Seq(compExp, AnySetMinus(filter, forallVarSet.localVar)()))()
    val mapDeleteApplied = applyDomainFunc(
      "mapDelete",
      Seq(mapResult, forallVarSet.localVar),
      compType.typVarsMap
    )
    val primeEqDelete = EqCmp(primeAppSetMinus, mapDeleteApplied)()

    val implies = Implies(setNotEmpty, primeEqDelete)()

    val forallTrigger = Trigger(Seq(mapDeleteApplied))()

    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), implies)()
    output
  }

  //     ensures forall es: Set[Int] :: {mapSubmap(result, es)}
  def forallMapSubmap(filter: Exp, compExp: Exp, primeDecl: ast.Function, mapResult: Exp): Forall = {
    val compType = compExp.typ.asInstanceOf[DomainType]

    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarSet = LocalVarDecl("__s", fSetType)()
    val subset = AnySetSubset(forallVarSet.localVar, filter)()
    val setNotEqual = NeCmp(forallVarSet.localVar, filter)()

    val primeAppSet = FuncApp(primeDecl, Seq(compExp, forallVarSet.localVar))()
    val mapSubmapApplied = applyDomainFunc("mapSubmap", Seq(mapResult, forallVarSet.localVar),
      compType.typVarsMap)
    val primeEqDelete = EqCmp(primeAppSet, mapSubmapApplied)()
    val implies = foldedConjImplies(Seq(subset, setNotEqual), Seq(subset, setNotEqual, primeEqDelete))
    val forallTrigger = Trigger(Seq(mapSubmapApplied))()

    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), implies)()
    output
  }

  def forallDummyExtensionality(filter: Exp, compExp: Exp, primeDecl: ast.Function): Forall = {
    val compType = compExp.typ.asInstanceOf[DomainType]

    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }

    val forallVarSet = LocalVarDecl("__s", fSetType)()
    val primeApplied = FuncApp(primeDecl, Seq(compExp, forallVarSet.localVar))()
    val compApplied1 = applyDomainFunc(
      DomainsGenerator.compApplyPrimeKey,
      Seq(compExp, primeApplied),
      compType.typVarsMap
    )
    val dummyApplied = applyDomainFunc(
      DomainsGenerator.compApplyDummyKey,
      Seq(EqCmp(forallVarSet.localVar, filter)()),
      compType.typVarsMap
    )

    val forallTrigger = Trigger(Seq(compApplied1))()

    val output = Forall(Seq(forallVarSet), Seq(forallTrigger), dummyApplied)()
    output
  }

  def forallDisjUnion(filter: Exp, compExp: Exp, primeDecl: ast.Function, mapResult: Exp) : Forall = {
    val compType = compExp.typ.asInstanceOf[DomainType]
    val fSetType = filter.typ match {
      case setType: SetType => setType
      case _ => throw new Exception("Filter must be a set")
    }
    val forallVarSet1 = LocalVarDecl("__s1", fSetType)()
    val forallVarSet2 = LocalVarDecl("__s2", fSetType)()
    val disjApplied = applyDomainFunc(
      DomainsGenerator.disjUnionKey,
      Seq(forallVarSet1.localVar, forallVarSet2.localVar, filter),
      compType.typVarsMap
    )

    val snapPrime1 = FuncApp(primeDecl, Seq(compExp, forallVarSet1.localVar))()
    val snapPrime2 = FuncApp(primeDecl, Seq(compExp, forallVarSet2.localVar))()

    val compApplyPrime1 = applyDomainFunc(
      DomainsGenerator.compApplyPrimeKey,
      Seq(compExp, snapPrime1),
      compType.typVarsMap
    )
    val compApplyPrime2 = applyDomainFunc(
      DomainsGenerator.compApplyPrimeKey,
      Seq(compExp, snapPrime2),
      compType.typVarsMap
    )
    val compApplyResult = applyDomainFunc(
      DomainsGenerator.compApplyPrimeKey,
      Seq(compExp, mapResult),
      compType.typVarsMap
    )

    val getOpApplied = applyDomainFunc(DomainsGenerator.compGetOperKey, Seq(compExp), compType.typVarsMap)

    val opApplied = applyDomainFunc(
      DomainsGenerator.opApplyKey,
      Seq(getOpApplied, compApplyPrime1, compApplyPrime2),
      compType.typVarsMap
    )

    val equals = EqCmp(compApplyResult, opApplied)()
    val implies = foldedConjImplies(Seq(disjApplied), Seq(disjApplied, equals))
    val trigger = Trigger(Seq(disjApplied))()
    val output = Forall(Seq(forallVarSet1, forallVarSet2), Seq(trigger), implies)()
    output
  }

}
