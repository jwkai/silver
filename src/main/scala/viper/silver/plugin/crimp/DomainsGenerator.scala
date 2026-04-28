package viper.silver.plugin.crimp

import fastparse.{P, Parsed, StringIn}
import viper.silver.ast.{NoPosition, Position}
import viper.silver.parser._

case class ParseException(msg: String, pos: (Position, Position)) extends Exception

object DomainsGenerator {
  final val intKey = "Int"
  final val crimpDKeyM = "CrimpM"
  final val crimpDTV0 = "I"
  final val crimpDTV1 = "V"
  final val crimpDTV2 = "S"
  final val prefix = "__crimp_"

  final val emptyCrimpAxiomM = "_emptyCrimpM"
  final val applyCrimpFuelEqAxiomM = "applyCrimpFuelEqM"
  final val invAxCrimpAxiomM = "_invAxCrimpM"
  final val singletonAxiomM = "_singletonM"
  final val dropOne1AxiomM = "_dropOne1M"
  final val loseManyAxiomM = "_loseManyM"
  final val setExtEqAxiomM = "_setExtEqM"
  final val disjUnionAxiomM = "_disjUnionM"
  final val trigExtensionalityAxiomM = "_trigExtensionalityM"
  final val extensionalityAxiomM = "_extensionalityM"
  final val crimpConstructKeyM = "hcrimpM"
  final val crimpApplyKeyM = "hcrimpApplyM"
  final val crimpApplyDummyKeyM = "hcrimpApplyDummyM"
  final val setEqDummyKeyM = "setEqDummyM"
  final val crimpGetRecvKeyM = "getreceiverM"
  final val crimpGetOperKeyM = "getoperatorM"
  final val crimpGetMappingKeyM = "getmappingM"
  final val cHeapElemKeyM = "cHeapElemM"
  final val trigDelKey1KeyM = "triggerDeleteKey1M"
  final val trigDelBlockKeyM = "triggerDeleteBlockM"
//  final val exhaleCrimpSetKeyM = "exhaleCrimpSetM"
  final val getFieldIDKeyM = "getFieldIDM"
  final val skExtKeyM = "skExtM"
  final val trigExtKeyM = "triggerExtM"

  final val applyCrimpFuelEqAxiomS = "applyCrimpFuelEqS"
  final val invAxCrimpAxiomS = "_invAxCrimpS"
  final val singletonAxiomS = "_singletonS"
  final val dropOne1AxiomS = "_dropOne1S"
  final val loseManyAxiomS = "_loseManyS"
  final val setExtEqAxiomS = "_setExtEqS"
  final val disjUnionAxiomS = "_disjUnionS"
  final val trigExtensionalityAxiomS = "_trigExtensionalityS"
  final val extensionalityAxiomS = "_extensionalityS"
  final val crimpDKeyS = "CrimpS"
  final val crimpConstructKeyS = "hcrimpS"
  final val crimpApplyKeyS = "hcrimpApplyS"
  final val crimpApplyDummyKeyS = "hcrimpApplyDummyS"
  final val setEqDummyKeyS = "setEqDummyS"
  final val crimpGetRecvKeyS = "getreceiverS"
  final val crimpGetOperKeyS = "getoperatorS"
  final val crimpGetMappingKeyS = "getmappingS"
  final val cHeapElemKeyS = "cHeapElemS"
  final val trigDelKey1KeyS = "triggerDeleteKey1S"
  final val trigDelBlockKeyS = "triggerDeleteBlockS"
//  final val exhaleCrimpSetKeyS = "exhaleCrimpSetS"
  final val getFieldIDKeyS = "getFieldIDS"
  final val skExtKeyS = "skExtS"
  final val trigExtKeyS = "triggerExtS"

  final val recApplyKey = "recApply"
  final val recInvKey = "recInv"
  final val opApplyKey = "opApply"
  final val opIdenKey = "opGetIden"
  final val mapApplyKey = "mapApply"
  final val mapIdenKey = "mapIdentity"
  final val disjUnionKey = "disjUnionEq"

  final val filterRecvGoodKey = "filterReceiverGood"
  final val subsetNotInRefsKey = "subsetNotInRefs"
  final val idxNotInRefsKey = "idxNotInRefs"
  final val setDeleteKey = "setDelete"

  final val fuelDKey = "Fuel"
  final val fuelSKey = "succ"
  final val fuelZKey = "zero"

  final val recDKey = "Receiver"
  final val mapDKey = "Mapping"
  final val opDKey = "Operator"

  def fuelDomainString(): String = {
    val fuelOut =
      s"""domain $fuelDKey {
         |
         |    function $fuelSKey(f: $fuelDKey): $fuelDKey
         |    function $fuelZKey(): $fuelDKey
         |
         |}\n """.stripMargin
    fuelOut
  }

  def receiverDomainString(): String = {
    val receiverOut =
      s"""domain $recDKey[$crimpDTV0] {
         |    function $recApplyKey(r:$recDKey[$crimpDTV0], a:$crimpDTV0): Ref
         |    function $recInvKey(rec:$recDKey[$crimpDTV0], ref:Ref): $crimpDTV0
         |    function $filterRecvGoodKey(f: Set[$crimpDTV0], r: $recDKey[$crimpDTV0]): Bool
         |
         |    function $subsetNotInRefsKey(f1: Set[$crimpDTV0], r: $recDKey[$crimpDTV0], lostR: Set[Ref]): Set[$crimpDTV0]
         |    function $idxNotInRefsKey(a: $crimpDTV0, r: $recDKey[$crimpDTV0], domR: Set[Ref]): Bool
         |
         |    axiom _inverse_receiver {
         |        forall ${prefix}a : $crimpDTV0, ${prefix}f: Set[$crimpDTV0], ${prefix}r: $recDKey[$crimpDTV0]
         |        :: { $recApplyKey(${prefix}r,${prefix}a), $filterRecvGoodKey(${prefix}f,${prefix}r) }
         |           { $filterRecvGoodKey(${prefix}f,${prefix}r), ${prefix}a in ${prefix}f }
         |        $filterRecvGoodKey(${prefix}f,${prefix}r) && ${prefix}a in ${prefix}f ==>
         |        $filterRecvGoodKey(${prefix}f,${prefix}r) &&
         |        ${prefix}a in ${prefix}f && $recInvKey(${prefix}r,$recApplyKey(${prefix}r,${prefix}a)) == ${prefix}a
         |    }
         |
         |    axiom _inverse_receiver1 {
         |        forall ${prefix}ref: Ref, ${prefix}f: Set[$crimpDTV0], ${prefix}r:$recDKey[$crimpDTV0]
         |        :: { $filterRecvGoodKey(${prefix}f, ${prefix}r), $recInvKey(${prefix}r, ${prefix}ref) }
         |        $filterRecvGoodKey(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f ==>
         |        $filterRecvGoodKey(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f &&
         |        $recApplyKey(${prefix}r,$recInvKey(${prefix}r,${prefix}ref)) == ${prefix}ref
         |    }
         |
         |    axiom _smallerF {
         |        forall ${prefix}f1: Set[$crimpDTV0], ${prefix}f2: Set[$crimpDTV0], ${prefix}r:$recDKey[$crimpDTV0] ::
         |        { ${prefix}f2 subset ${prefix}f1, $filterRecvGoodKey(${prefix}f1,${prefix}r) }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) && ${prefix}f2 subset ${prefix}f1 ==>
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |          ${prefix}f2 subset ${prefix}f1 && $filterRecvGoodKey(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _smallerFDelete {
         |        forall ${prefix}f1: Set[$crimpDTV0], ${prefix}f2: Set[$crimpDTV0], ${prefix}r:$recDKey[$crimpDTV0] ::
         |        { $filterRecvGoodKey(${prefix}f1,${prefix}r), ${prefix}f1 setminus ${prefix}f2 }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) ==> $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |        $filterRecvGoodKey(${prefix}f1 setminus ${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _unionF {
         |        forall ${prefix}f1: Set[$crimpDTV0], ${prefix}f2: Set[$crimpDTV0], ${prefix}r:$recDKey[$crimpDTV0] ::
         |        { $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) }
         |        $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) ==>
         |        $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) &&
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) && $filterRecvGoodKey(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _subsetNotInRefsAxiom {
         |        forall ${prefix}a: $crimpDTV0, ${prefix}fs: Set[$crimpDTV0], ${prefix}r: $recDKey[$crimpDTV0],
         |          ${prefix}lostR: Set[Ref] ::
         |        { ${prefix}a in $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) }
         |            ${prefix}a in $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) <==>
         |                (${prefix}a in ${prefix}fs && !($recApplyKey(${prefix}r, ${prefix}a) in ${prefix}lostR))
         |    }
         |
         |    axiom _subsetNotInRefsSubset {
         |        forall ${prefix}fs: Set[$crimpDTV0], ${prefix}r: $recDKey[$crimpDTV0], ${prefix}lostR: Set[Ref] ::
         |          { $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) }
         |        $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) subset ${prefix}fs
         |    }
         |
         |    axiom _idxNotInRefSetAxiom {
         |       (forall ${prefix}a: $crimpDTV0, ${prefix}recv: $recDKey[$crimpDTV0], ${prefix}domR: Set[Ref] ::
         |         { ($idxNotInRefsKey(${prefix}a, ${prefix}recv, ${prefix}domR): Bool) }
         |       !((recApply(${prefix}recv, ${prefix}a): Ref) in ${prefix}domR) ==>
         |           $idxNotInRefsKey(${prefix}a, ${prefix}recv, ${prefix}domR))
         |    }
         |
         |}\n """.stripMargin
    receiverOut
  }

  def mappingDomainString(): String = {
    val mappingOut =
      s"""domain $mapDKey[$crimpDTV1,$crimpDTV2] {
         |
         |    function $mapApplyKey(m: $mapDKey[$crimpDTV1,$crimpDTV2], _mInput:$crimpDTV1): $crimpDTV2
         |
         |    function $mapIdenKey(): $mapDKey[$crimpDTV1,$crimpDTV1]
         |
         |    axiom {
         |      forall __v: $crimpDTV1 :: { $mapApplyKey($mapIdenKey() ,__v) }
         |      $mapApplyKey($mapIdenKey() , __v) == __v
         |    }
         |
         |}\n """.stripMargin
    mappingOut
  }

  def opDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val opOut =
      s"""domain $opDKey[$crimpDTV2] {
         |
         |    function _noTrigOp(out: $crimpDTV2): Bool
         |    function $opApplyKey(op: $opDKey[$crimpDTV2], val1:$crimpDTV2, val2:$crimpDTV2): $crimpDTV2
         |    function $opIdenKey(op: $opDKey[$crimpDTV2]): $crimpDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    opOut
  }

  private def emptyCrimpAxiom(): String = {
    s"""
    axiom $emptyCrimpAxiomM {
      forall ${prefix}f: $fuelDKey, ${prefix}rh: $intKey,
      ${prefix}c: $crimpDKeyM[$crimpDTV0,$crimpDTV1,$crimpDTV2],
      ${prefix}fs: Set[$crimpDTV0] ::
        { ($crimpApplyKeyM(${prefix}f, ${prefix}rh, ${prefix}c, ${prefix}fs): $crimpDTV2) }
      ${prefix}fs == Set[$crimpDTV0]() ==>
        ${prefix}fs == Set[$crimpDTV0]() &&
        $crimpApplyKeyM(${prefix}f, ${prefix}rh, ${prefix}c, ${prefix}fs) == $opIdenKey($crimpGetOperKeyM(${prefix}c))
    }

    """
  }

  private def dropOneAxiomWithoutId(): String = {
    s"""axiom $dropOne1AxiomS {
        forall ${prefix}f: $fuelDKey,
               ${prefix}rh: $intKey,
               ${prefix}c: $crimpDKeyS[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs: Set[$crimpDTV0],
               ${prefix}key: $crimpDTV0 ::
        { ($trigDelKey1KeyS($crimpApplyKeyS($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}key): Bool),
          ($cHeapElemKeyS(${prefix}rh, ${prefix}c, ${prefix}key): $crimpDTV2) }
        (${prefix}key in ${prefix}fs && (${prefix}fs != Set(${prefix}key))) ==>
        (${prefix}key in ${prefix}fs && (${prefix}fs != Set(${prefix}key))) &&
        $crimpApplyKeyS($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($crimpGetOperKeyS(${prefix}c),
          $crimpApplyKeyS(${prefix}f, ${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, Set(${prefix}key))),
          $cHeapElemKeyS(${prefix}rh, ${prefix}c, ${prefix}key))
    }"""
  }

  private def dropOneAxiom(): String = {
    s"""axiom $dropOne1AxiomM {
        forall ${prefix}f: $fuelDKey,
               ${prefix}rh: $intKey,
               ${prefix}c: $crimpDKeyM[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs: Set[$crimpDTV0],
               ${prefix}key: $crimpDTV0 ::
        { ($trigDelKey1KeyM($crimpApplyKeyM($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}key): Bool),
          ($cHeapElemKeyM(${prefix}rh, ${prefix}c, ${prefix}key): $crimpDTV2) }
        (${prefix}key in ${prefix}fs) ==>
        (${prefix}key in ${prefix}fs) &&
        $crimpApplyKeyM($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($crimpGetOperKeyM(${prefix}c),
          $crimpApplyKeyM(${prefix}f, ${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, Set(${prefix}key))),
          $cHeapElemKeyM(${prefix}rh, ${prefix}c, ${prefix}key))
    }"""
  }

  private def loseManyAxiomWithoutId(): String = {
    s"""axiom $loseManyAxiomS {
        forall ${prefix}f: $fuelDKey,
               ${prefix}rh: $intKey,
               ${prefix}c: $crimpDKeyS[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs: Set[$crimpDTV0],
               ${prefix}keys: Set[$crimpDTV0] ::
        { $trigDelBlockKeyS($crimpApplyKeyS($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}keys) }
        (${prefix}keys subset ${prefix}fs && (${prefix}keys != ${prefix}fs)) ==>
        (${prefix}keys subset ${prefix}fs && (${prefix}keys != ${prefix}fs)) &&
        $crimpApplyKeyS($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($crimpGetOperKeyS(${prefix}c),
          $crimpApplyKeyS(${prefix}f, ${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, ${prefix}keys)),
          $crimpApplyKeyS(${prefix}f, ${prefix}rh, ${prefix}c, ${prefix}keys))
    }"""
  }

  private def loseManyAxiom(): String = {
    s"""axiom $loseManyAxiomM {
        forall ${prefix}f: $fuelDKey,
               ${prefix}rh: $intKey,
               ${prefix}c: $crimpDKeyM[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs: Set[$crimpDTV0],
               ${prefix}keys: Set[$crimpDTV0] ::
        { $trigDelBlockKeyM($crimpApplyKeyM($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}keys) }
        (${prefix}keys subset ${prefix}fs) ==>
        (${prefix}keys subset ${prefix}fs) &&
        $crimpApplyKeyM($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($crimpGetOperKeyM(${prefix}c),
          $crimpApplyKeyM(${prefix}f, ${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, ${prefix}keys)),
          $crimpApplyKeyM(${prefix}f, ${prefix}rh, ${prefix}c, ${prefix}keys))
    }"""
  }

  private def disjUnionAxiomWithoutId(): String = {
    s"""axiom $disjUnionAxiomS {
        forall ${prefix}f1: $fuelDKey,
               ${prefix}f2: $fuelDKey,
               ${prefix}rh: $intKey,
               ${prefix}c: $crimpDKeyS[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs1: Set[$crimpDTV0],
               ${prefix}fs2: Set[$crimpDTV0],
               ${prefix}dus: Set[$crimpDTV0] ::
        { ($crimpApplyKeyS(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}fs1): $crimpDTV2),
          ($crimpApplyKeyS(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}fs2): $crimpDTV2),
          ($disjUnionKey(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) }
        (($disjUnionKey(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) &&
         (${prefix}fs1 != Set()) && (${prefix}fs2 != Set())) ==>
          (($crimpApplyKeyS(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}dus): $crimpDTV2) ==
          ($opApplyKey($crimpGetOperKeyS(${prefix}c),
            ($crimpApplyKeyS(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}fs1): $crimpDTV2),
            ($crimpApplyKeyS(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}fs2): $crimpDTV2)): $crimpDTV2)) &&
          (($crimpApplyKeyS(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}dus): $crimpDTV2) ==
          ($opApplyKey($crimpGetOperKeyS(${prefix}c),
            ($crimpApplyKeyS(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}fs1): $crimpDTV2),
            ($crimpApplyKeyS(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}fs2): $crimpDTV2)): $crimpDTV2))
    }"""
  }

  private def disjUnionAxiom(): String = {
    s"""axiom $disjUnionAxiomM {
        forall ${prefix}f1: $fuelDKey,
               ${prefix}f2: $fuelDKey,
               ${prefix}rh: $intKey,
               ${prefix}c: $crimpDKeyM[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs1: Set[$crimpDTV0],
               ${prefix}fs2: Set[$crimpDTV0],
               ${prefix}dus: Set[$crimpDTV0] ::
        { ($crimpApplyKeyM(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}fs1): $crimpDTV2),
          ($crimpApplyKeyM(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}fs2): $crimpDTV2),
          ($disjUnionKey(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) }
        ($disjUnionKey(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) ==>
          (($crimpApplyKeyM(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}dus): $crimpDTV2) ==
          ($opApplyKey($crimpGetOperKeyM(${prefix}c),
            ($crimpApplyKeyM(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}fs1): $crimpDTV2),
            ($crimpApplyKeyM(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}fs2): $crimpDTV2)): $crimpDTV2)) &&
          (($crimpApplyKeyM(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}dus): $crimpDTV2) ==
          ($opApplyKey($crimpGetOperKeyM(${prefix}c),
            ($crimpApplyKeyM(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}fs1): $crimpDTV2),
            ($crimpApplyKeyM(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}fs2): $crimpDTV2)): $crimpDTV2))
    }"""
  }

  private def extensionalityAxiomWithoutId(): String = {
    s"""axiom $extensionalityAxiomS {
        forall ${prefix}f1: $fuelDKey,
               ${prefix}f2: $fuelDKey,
               ${prefix}rh_old: $intKey,
               ${prefix}rh_new: $intKey,
               ${prefix}c: $crimpDKeyS[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs: Set[$crimpDTV0] ::
        { ($trigExtKeyS(($crimpApplyKeyS(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs): $crimpDTV2),
                       ($crimpApplyKeyS(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs): $crimpDTV2)): Bool) }
        (${prefix}rh_old < ${prefix}rh_new) ==>
        (($crimpApplyKeyS(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs) == $crimpApplyKeyS(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs)) ||
        (((${prefix}fs != Set()) && ($skExtKeyS(${prefix}c, $crimpApplyKeyS(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs), $crimpApplyKeyS(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs)) in ${prefix}fs ==>
            (($cHeapElemKeyS(${prefix}rh_old, ${prefix}c, $skExtKeyS(${prefix}c, $crimpApplyKeyS(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs), $crimpApplyKeyS(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs))): $crimpDTV2)) ==
            (($cHeapElemKeyS(${prefix}rh_new, ${prefix}c, $skExtKeyS(${prefix}c, $crimpApplyKeyS(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs), $crimpApplyKeyS(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs))): $crimpDTV2))))
        ==>
        ($crimpApplyKeyS(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs) == $crimpApplyKeyS(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs))))
    }"""
  }

  private def extensionalityAxiom(): String = {
    s"""axiom $extensionalityAxiomM {
        forall ${prefix}f1: $fuelDKey,
               ${prefix}f2: $fuelDKey,
               ${prefix}rh_old: $intKey,
               ${prefix}rh_new: $intKey,
               ${prefix}c: $crimpDKeyM[$crimpDTV0,$crimpDTV1,$crimpDTV2],
               ${prefix}fs: Set[$crimpDTV0] ::
        { ($trigExtKeyM(($crimpApplyKeyM(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs): $crimpDTV2),
                       ($crimpApplyKeyM(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs): $crimpDTV2)): Bool) }
        (${prefix}rh_old < ${prefix}rh_new) ==>
        (($crimpApplyKeyM(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs) == $crimpApplyKeyM(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs)) ||
        (($skExtKeyM(${prefix}c, $crimpApplyKeyM(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs), $crimpApplyKeyM(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs)) in ${prefix}fs ==>
            (($cHeapElemKeyM(${prefix}rh_old, ${prefix}c, $skExtKeyM(${prefix}c, $crimpApplyKeyM(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs), $crimpApplyKeyM(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs))): $crimpDTV2)) ==
            (($cHeapElemKeyM(${prefix}rh_new, ${prefix}c, $skExtKeyM(${prefix}c, $crimpApplyKeyM(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs), $crimpApplyKeyM(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs))): $crimpDTV2)))
        ==>
        ($crimpApplyKeyM(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs) == $crimpApplyKeyM(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs))))
    }"""
  }

  private def crimpDomainStringSorM(domainName: String,
                                     crimpConstructKey: String,
                                     crimpApplyKey: String,
                                     crimpApplyDummyKey: String,
                                     setEqDummyKey: String,
                                     crimpGetRecvKey: String,
                                     crimpGetOperKey: String,
                                     crimpGetMappingKey: String,
                                     cHeapElemKey: String,
                                     trigDelKey1Key: String,
                                     trigDelBlockKey: String,
                                     getFieldIDKey: String,
                                     skExtKey: String,
                                     trigExtKey: String,
                                     emptyAxiom: String,
                                     dropAxiom: String,
                                     loseAxiom: String,
                                     disjAxiom: String,
                                     extAxiom: String,
                                     applyCrimpFuelEqAxiom: String,
                                     invAxCrimpAxiom: String,
                                     singletonAxiom: String,
                                     setExtEqAxiom: String,
                                     trigExtensionalityAxiom: String): String = {
    val crimpOut =
      s"""domain $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2] {
         |
         |    function $crimpConstructKey(r: $recDKey[$crimpDTV0], m: $mapDKey[$crimpDTV1,$crimpDTV2], op: $opDKey[$crimpDTV2]): $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2]
         |    function $crimpApplyKey(f: $fuelDKey, rh: $intKey, c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2], fs: Set[$crimpDTV0]): $crimpDTV2
         |    function $crimpApplyDummyKey(a: $crimpDTV2): Bool
         |    function $setEqDummyKey(b: Bool): Bool
         |
         |    axiom $applyCrimpFuelEqAxiom {
         |        forall ${prefix}f: $fuelDKey, ${prefix}rh: $intKey, ${prefix}c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2], ${prefix}fs: Set[$crimpDTV0] ::
         |            { ($crimpApplyKey($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs): $crimpDTV2) }
         |        $crimpApplyKey($fuelSKey(${prefix}f), ${prefix}rh, ${prefix}c, ${prefix}fs) == $crimpApplyKey(${prefix}f, ${prefix}rh, ${prefix}c, ${prefix}fs)
         |    }
         |
         |    function $crimpGetRecvKey(c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2]): $recDKey[$crimpDTV0]
         |    function $crimpGetOperKey(c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2]): $opDKey[$crimpDTV2]
         |    function $crimpGetMappingKey(c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2]): $mapDKey[$crimpDTV1,$crimpDTV2]
         |
         |    function $cHeapElemKey(rh: $intKey, c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2], a: $crimpDTV0): $crimpDTV2
         |
         |    function $trigDelBlockKey(applyC: $crimpDTV2, block: Set[$crimpDTV0]): Bool
         |    function $trigDelKey1Key(applyC: $crimpDTV2, key: $crimpDTV0): Bool
         |
         |    function $getFieldIDKey(c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2]): Int
         |
         |    axiom $invAxCrimpAxiom {
         |        forall ${prefix}r: $recDKey[$crimpDTV0],
         |               ${prefix}m: $mapDKey[$crimpDTV1,$crimpDTV2],
         |               ${prefix}o: $opDKey[$crimpDTV2] ::
         |        { ($crimpConstructKey(${prefix}r, ${prefix}m, ${prefix}o): $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2]) }
         |        $crimpGetRecvKey($crimpConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}r &&
         |        $crimpGetMappingKey($crimpConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}m &&
         |        $crimpGetOperKey($crimpConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}o
         |    }
         |    $emptyAxiom
         |    axiom $singletonAxiom {
         |        forall ${prefix}f: $fuelDKey,
         |               ${prefix}rh: $intKey,
         |               ${prefix}c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2],
         |               ${prefix}elem: $crimpDTV0 ::
         |        { ($crimpApplyKey(${prefix}f, ${prefix}rh, ${prefix}c, Set(${prefix}elem)): $crimpDTV2),
         |          ($cHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}elem): $crimpDTV2) }
         |        $crimpApplyKey(${prefix}f, ${prefix}rh, ${prefix}c, Set(${prefix}elem)) == $cHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}elem)
         |    }
         |
         |    $dropAxiom
         |
         |    $loseAxiom
         |
         |    axiom $setExtEqAxiom {
         |        forall ${prefix}f1: $fuelDKey,
         |               ${prefix}f2: $fuelDKey,
         |               ${prefix}rh: $intKey,
         |               ${prefix}c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2],
         |               ${prefix}fs1: Set[$crimpDTV0],
         |               ${prefix}fs2: Set[$crimpDTV0] ::
         |        { ($crimpApplyKey(${prefix}f1, ${prefix}rh, ${prefix}c, ${prefix}fs1): $crimpDTV2),
         |          ($crimpApplyKey(${prefix}f2, ${prefix}rh, ${prefix}c, ${prefix}fs2): $crimpDTV2) }
         |        $setEqDummyKey(${prefix}fs1 == ${prefix}fs2)
         |    }
         |
         |    $disjAxiom
         |
         |    function $skExtKey(c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2], hfA1: $crimpDTV2, hfA2: $crimpDTV2): $crimpDTV0
         |    function $trigExtKey(hfA1: $crimpDTV2, hfA2: $crimpDTV2): Bool
         |
         |    axiom $trigExtensionalityAxiom {
         |        forall ${prefix}f1: $fuelDKey,
         |               ${prefix}f2: $fuelDKey,
         |               ${prefix}rh_old: $intKey,
         |               ${prefix}rh_new: $intKey,
         |               ${prefix}c: $domainName[$crimpDTV0,$crimpDTV1,$crimpDTV2],
         |               ${prefix}fs: Set[$crimpDTV0] ::
         |        { ($crimpApplyKey(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs): $crimpDTV2),
         |          ($crimpApplyKey(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs): $crimpDTV2) }
         |        ($trigExtKey(($crimpApplyKey(${prefix}f1, ${prefix}rh_old, ${prefix}c, ${prefix}fs): $crimpDTV2),
         |                     ($crimpApplyKey(${prefix}f2, ${prefix}rh_new, ${prefix}c, ${prefix}fs): $crimpDTV2)))
         |    }
         |
         |    $extAxiom
         |}\n """.stripMargin
    crimpOut
  }

  def crimpDomainStringNoId(): String =
    crimpDomainStringSorM(
      crimpDKeyS,
      crimpConstructKeyS,
      crimpApplyKeyS,
      crimpApplyDummyKeyS,
      setEqDummyKeyS,
      crimpGetRecvKeyS,
      crimpGetOperKeyS,
      crimpGetMappingKeyS,
      cHeapElemKeyS,
      trigDelKey1KeyS,
      trigDelBlockKeyS,
      getFieldIDKeyS,
      skExtKeyS,
      trigExtKeyS,
      s"""""",
      dropOneAxiomWithoutId(),
      loseManyAxiomWithoutId(),
      disjUnionAxiomWithoutId(),
      extensionalityAxiomWithoutId(),
      applyCrimpFuelEqAxiomS,
      invAxCrimpAxiomS,
      singletonAxiomS,
      setExtEqAxiomS,
      trigExtensionalityAxiomS
    )

  def crimpDomainString(): String =
    crimpDomainStringSorM(
      crimpDKeyM,
      crimpConstructKeyM,
      crimpApplyKeyM,
      crimpApplyDummyKeyM,
      setEqDummyKeyM,
      crimpGetRecvKeyM,
      crimpGetOperKeyM,
      crimpGetMappingKeyM,
      cHeapElemKeyM,
      trigDelKey1KeyM,
      trigDelBlockKeyM,
      getFieldIDKeyM,
      skExtKeyM,
      trigExtKeyM,
      emptyCrimpAxiom(),
      dropOneAxiom(),
      loseManyAxiom(),
      disjUnionAxiom(),
      extensionalityAxiom(),
      applyCrimpFuelEqAxiomM,
      invAxCrimpAxiomM,
      singletonAxiomM,
      setExtEqAxiomM,
      trigExtensionalityAxiomM
    )

  def setEditDomainString(): String = {
    val setOut =
      s"""domain SetEdit[$crimpDTV0] {
         |    function $setDeleteKey(m: Set[$crimpDTV0], e: Set[$crimpDTV0]): Set[$crimpDTV0]
         |    function $disjUnionKey(s1: Set[$crimpDTV0], s2: Set[$crimpDTV0], s3: Set[$crimpDTV0]): Bool
         |
         |    axiom _disjUnionEqDef {
         |        (forall ${prefix}s1: Set[$crimpDTV0], ${prefix}s2: Set[$crimpDTV0], ${prefix}s3: Set[$crimpDTV0] ::
         |            { ($disjUnionKey(${prefix}s1, ${prefix}s2, ${prefix}s3): Bool) }
         |        ($disjUnionKey(${prefix}s1, ${prefix}s2, ${prefix}s3): Bool) ==
         |        ((${prefix}s1 intersection ${prefix}s2) == Set[$crimpDTV0]() &&
         |          (${prefix}s1 union ${prefix}s2) == ${prefix}s3))
         |    }
         |
         |    axiom _setDeleteAxiom {
         |        (forall ${prefix}s: Set[$crimpDTV0], ${prefix}e: Set[$crimpDTV0] ::
         |            { ($setDeleteKey(${prefix}s, ${prefix}e): Set[$crimpDTV0]) }
         |        ($setDeleteKey(${prefix}s, ${prefix}e): Set[$crimpDTV0]) == ${prefix}s setminus ${prefix}e)
         |    }
         |
         |    axiom _setDeleteSubset {
         |        (forall ${prefix}s: Set[$crimpDTV0], ${prefix}e: Set[$crimpDTV0] ::
         |            { ($setDeleteKey(${prefix}s, ${prefix}e): Set[$crimpDTV0]) }
         |        ($setDeleteKey(${prefix}s, ${prefix}e): Set[$crimpDTV0]) subset ${prefix}s)
         |    }
         |}
         |
         |
         |
         |\n """.stripMargin
    setOut
  }

  def parseDomainString(input: String): PDomain = {
    val fp = new FastParser()
    fp._line_offset = Array(0)

    def myParserToPDomain(implicit ctx: P[_]): P[PDomain] =
      fp.annotated(
        fp.reservedKwMany(
          StringIn("domain"),
          str => pos => str match {
            case "domain" => fp.domainDecl.map(_(PReserved(PKw.Domain)(pos)))
          }
        )
      )

    fastparse.parse(input, myParserToPDomain(_)) match {
      case Parsed.Success(newDomain, _) =>
        val d = changePosRecursive(newDomain.asInstanceOf[PNode], (NoPosition, NoPosition))
        d.asInstanceOf[PDomain]
      case fail: Parsed.Failure =>
        // This should not happen
        val trace = fail.trace()
        val fullStack = fastparse.Parsed.Failure.formatStack(trace.input, trace.stack)
        val msg = s"${trace.aggregateMsg}. Occurred while parsing: $fullStack"
        throw ParseException(msg, (NoPosition, NoPosition))
    }
  }

  // Copied from MacroExpander.scala
  def changePosRecursive(body: PNode, pos: (Position, Position)): PNode = {
    val children = body.children.map {
      case node: PNode => changePosRecursive(node, pos)
      case child => child
    }
    body.withChildren(children, Some(pos), forceRewrite = true)
  }
}
