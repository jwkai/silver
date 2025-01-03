package viper.silver.plugin.hreduce

import fastparse.{P, Parsed, StringIn}
import viper.silver.ast.{NoPosition, Position}
import viper.silver.parser.{FastParser, PDomain, PKw, PNode, PReserved}

case class ParseException(msg: String, pos: (Position, Position)) extends Exception

object DomainsGenerator {
  final val intKey = "Int"
  final val reduceDKeyM = "ReduceM"
  final val reduceDTV0 = "A"
  final val reduceDTV1 = "V"
  final val reduceDTV2 = "B"
  final val prefix = "__reduce_"

  final val reduceConstructKeyM = "hreduceM"
  final val reduceApplyKeyM = "hreduceApplyM"
  final val reduceApplyPrimeKeyM = "hreduceApply1M"
  final val reduceApplyDummyKeyM = "hreduceApplyDummyM"
  final val setEqDummyKeyM = "setEqDummyM"
  final val reduceGetRecvKeyM = "getreceiverM"
  final val reduceGetOperKeyM = "getoperatorM"
  final val reduceGetMappingKeyM = "getmappingM"
  final val rHeapElemKeyM = "rHeapElemM"
  final val trigDelKey1KeyM = "triggerDeleteKey1M"
  final val trigDelBlockKeyM = "triggerDeleteBlockM"
  final val exhaleReduceSetKeyM = "exhaleReduceSetM"
  final val getFieldIDKeyM = "getFieldIDM"
  final val skExtKeyM = "skExtM"
  final val trigExtKeyM = "triggerExtM"

  final val reduceDKeyS = "ReduceS"
  final val reduceConstructKeyS = "hreduceS"
  final val reduceApplyKeyS = "hreduceApplyS"
  final val reduceApplyPrimeKeyS = "hreduceApply1S"
  final val reduceApplyDummyKeyS = "hreduceApplyDummyS"
  final val setEqDummyKeyS = "setEqDummyS"
  final val reduceGetRecvKeyS = "getreceiverS"
  final val reduceGetOperKeyS = "getoperatorS"
  final val reduceGetMappingKeyS = "getmappingS"
  final val rHeapElemKeyS = "rHeapElemS"
  final val trigDelKey1KeyS = "triggerDeleteKey1S"
  final val trigDelBlockKeyS = "triggerDeleteBlockS"
  final val exhaleReduceSetKeyS = "exhaleReduceSetS"
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

  final val recDKey = "Receiver"
  final val mapDKey = "Mapping"
  final val opDKey = "Operator"

  def receiverDomainString(): String = {
    val receiverOut =
      s"""domain $recDKey[$reduceDTV0] {
         |    function $recApplyKey(r:$recDKey[$reduceDTV0], a:$reduceDTV0): Ref
         |    function $recInvKey(rec:$recDKey[$reduceDTV0], ref:Ref): $reduceDTV0
         |    function $filterRecvGoodKey(f: Set[$reduceDTV0], r: $recDKey[$reduceDTV0]): Bool
         |
         |    function $subsetNotInRefsKey(f1: Set[$reduceDTV0], r: $recDKey[$reduceDTV0], lostR: Set[Ref]): Set[$reduceDTV0]
         |    function $idxNotInRefsKey(a: $reduceDTV0, r: $recDKey[$reduceDTV0], domR: Set[Ref]): Bool
         |
         |    axiom _inverse_receiver {
         |        forall ${prefix}a : $reduceDTV0, ${prefix}f: Set[$reduceDTV0], ${prefix}r: $recDKey[$reduceDTV0]
         |        :: { $recApplyKey(${prefix}r,${prefix}a), $filterRecvGoodKey(${prefix}f,${prefix}r) }
         |           { $filterRecvGoodKey(${prefix}f,${prefix}r), ${prefix}a in ${prefix}f }
         |        $filterRecvGoodKey(${prefix}f,${prefix}r) && ${prefix}a in ${prefix}f ==>
         |        $filterRecvGoodKey(${prefix}f,${prefix}r) &&
         |        ${prefix}a in ${prefix}f && $recInvKey(${prefix}r,$recApplyKey(${prefix}r,${prefix}a)) == ${prefix}a
         |    }
         |
         |    axiom _inverse_receiver1 {
         |        forall ${prefix}ref: Ref, ${prefix}f: Set[$reduceDTV0], ${prefix}r:$recDKey[$reduceDTV0]
         |        :: { $filterRecvGoodKey(${prefix}f, ${prefix}r), $recInvKey(${prefix}r, ${prefix}ref) }
         |        $filterRecvGoodKey(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f ==>
         |        $filterRecvGoodKey(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f &&
         |        $recApplyKey(${prefix}r,$recInvKey(${prefix}r,${prefix}ref)) == ${prefix}ref
         |    }
         |
         |    axiom _smallerF {
         |        forall ${prefix}f1: Set[$reduceDTV0], ${prefix}f2: Set[$reduceDTV0], ${prefix}r:$recDKey[$reduceDTV0] ::
         |        { ${prefix}f2 subset ${prefix}f1, $filterRecvGoodKey(${prefix}f1,${prefix}r) }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) && ${prefix}f2 subset ${prefix}f1 ==>
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |          ${prefix}f2 subset ${prefix}f1 && $filterRecvGoodKey(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _smallerFDelete {
         |        forall ${prefix}f1: Set[$reduceDTV0], ${prefix}f2: Set[$reduceDTV0], ${prefix}r:$recDKey[$reduceDTV0] ::
         |        { $filterRecvGoodKey(${prefix}f1,${prefix}r), ${prefix}f1 setminus ${prefix}f2 }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) ==> $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |        $filterRecvGoodKey(${prefix}f1 setminus ${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _unionF {
         |        forall ${prefix}f1: Set[$reduceDTV0], ${prefix}f2: Set[$reduceDTV0], ${prefix}r:$recDKey[$reduceDTV0] ::
         |        { $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) }
         |        $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) ==>
         |        $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) &&
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) && $filterRecvGoodKey(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _subsetNotInRefsAxiom {
         |        forall ${prefix}a: $reduceDTV0, ${prefix}fs: Set[$reduceDTV0], ${prefix}r: $recDKey[$reduceDTV0],
         |          ${prefix}lostR: Set[Ref] ::
         |        { ${prefix}a in $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) }
         |            ${prefix}a in $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) <==>
         |                (${prefix}a in ${prefix}fs && !($recApplyKey(${prefix}r, ${prefix}a) in ${prefix}lostR))
         |    }
         |
         |    axiom _subsetNotInRefsSubset {
         |        forall ${prefix}fs: Set[$reduceDTV0], ${prefix}r: $recDKey[$reduceDTV0], ${prefix}lostR: Set[Ref] ::
         |          { $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) }
         |        $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) subset ${prefix}fs
         |    }
         |
         |    axiom _idxNotInRefSetAxiom {
         |       (forall ${prefix}a: $reduceDTV0, ${prefix}recv: $recDKey[$reduceDTV0], ${prefix}domR: Set[Ref] ::
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
      s"""domain $mapDKey[$reduceDTV1,$reduceDTV2] {
         |
         |    function $mapApplyKey(m: $mapDKey[$reduceDTV1,$reduceDTV2], _mInput:$reduceDTV1): $reduceDTV2
         |
         |    function $mapIdenKey(): $mapDKey[$reduceDTV1,$reduceDTV1]
         |
         |    axiom {
         |      forall __v: $reduceDTV1 :: { $mapApplyKey($mapIdenKey() ,__v) }
         |      $mapApplyKey($mapIdenKey() , __v) == __v
         |    }
         |
         |}\n """.stripMargin
    mappingOut
  }

  def opDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val opOut =
      s"""domain $opDKey[$reduceDTV2] {
         |
         |    function _noTrigOp(out: $reduceDTV2): Bool
         |    function $opApplyKey(op: $opDKey[$reduceDTV2], val1:$reduceDTV2, val2:$reduceDTV2): $reduceDTV2
         |    function $opIdenKey(op: $opDKey[$reduceDTV2]): $reduceDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    opOut
  }

  private def emptyReduceAxiom(): String = {
    s"""
    axiom _emptyReduce {
      forall ${prefix}rh: $intKey,
      ${prefix}c: $reduceDKeyM[$reduceDTV0,$reduceDTV1,$reduceDTV2],
      ${prefix}fs: Set[$reduceDTV0] ::
        { ($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs): $reduceDTV2) }
      ${prefix}fs == Set[$reduceDTV0]() ==>
        ${prefix}fs == Set[$reduceDTV0]() &&
        $reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs) == $opIdenKey($reduceGetOperKeyM(${prefix}c))
    }

    """
  }

  private def dropOneAxiomWithoutId(): String = {
    s"""axiom _dropOne1 {
        forall ${prefix}rh: $intKey,
               ${prefix}c: $reduceDKeyS[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs: Set[$reduceDTV0],
               ${prefix}key: $reduceDTV0 ::
        { ($trigDelKey1KeyS($reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}key): Bool),
          ($rHeapElemKeyS(${prefix}rh, ${prefix}c, ${prefix}key): $reduceDTV2) }
        (${prefix}key in ${prefix}fs && (${prefix}fs != Set(${prefix}key))) ==>
        (${prefix}key in ${prefix}fs && (${prefix}fs != Set(${prefix}key))) &&
        $reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($reduceGetOperKeyS(${prefix}c),
          $reduceApplyPrimeKeyS(${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, Set(${prefix}key))),
          $rHeapElemKeyS(${prefix}rh, ${prefix}c, ${prefix}key))
    }"""
  }

  private def dropOneAxiom(): String = {
    s"""axiom _dropOne1 {
        forall ${prefix}rh: $intKey,
               ${prefix}c: $reduceDKeyM[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs: Set[$reduceDTV0],
               ${prefix}key: $reduceDTV0 ::
        { ($trigDelKey1KeyM($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}key): Bool),
          ($rHeapElemKeyM(${prefix}rh, ${prefix}c, ${prefix}key): $reduceDTV2) }
        (${prefix}key in ${prefix}fs) ==>
        (${prefix}key in ${prefix}fs) &&
        $reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($reduceGetOperKeyM(${prefix}c),
          $reduceApplyPrimeKeyM(${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, Set(${prefix}key))),
          $rHeapElemKeyM(${prefix}rh, ${prefix}c, ${prefix}key))
    }"""
  }

  private def loseManyAxiomWithoutId(): String = {
    s"""axiom _loseMany {
        forall ${prefix}rh: $intKey,
               ${prefix}c: $reduceDKeyS[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs: Set[$reduceDTV0],
               ${prefix}keys: Set[$reduceDTV0] ::
        { $trigDelBlockKeyS($reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}keys) }
        (${prefix}keys subset ${prefix}fs && (${prefix}keys != ${prefix}fs)) ==>
        (${prefix}keys subset ${prefix}fs && (${prefix}keys != ${prefix}fs)) &&
        $reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($reduceGetOperKeyS(${prefix}c),
          $reduceApplyPrimeKeyS(${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, ${prefix}keys)),
          $reduceApplyPrimeKeyS(${prefix}rh, ${prefix}c, ${prefix}keys))
    }"""
  }

  private def loseManyAxiom(): String = {
    s"""axiom _loseMany {
        forall ${prefix}rh: $intKey,
               ${prefix}c: $reduceDKeyM[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs: Set[$reduceDTV0],
               ${prefix}keys: Set[$reduceDTV0] ::
        { $trigDelBlockKeyM($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}keys) }
        (${prefix}keys subset ${prefix}fs) ==>
        (${prefix}keys subset ${prefix}fs) &&
        $reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs) ==
        $opApplyKey($reduceGetOperKeyM(${prefix}c),
          $reduceApplyPrimeKeyM(${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, ${prefix}keys)),
          $reduceApplyPrimeKeyM(${prefix}rh, ${prefix}c, ${prefix}keys))
    }"""
  }

  private def disjUnionAxiomWithoutId(): String = {
    s"""axiom _disjUnion {
        forall ${prefix}rh: $intKey,
               ${prefix}c: $reduceDKeyS[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs1: Set[$reduceDTV0],
               ${prefix}fs2: Set[$reduceDTV0],
               ${prefix}dus: Set[$reduceDTV0] ::
        { ($reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
          ($reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2),
          (disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) }
        ((disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) &&
         (${prefix}fs1 != Set()) && (${prefix}fs2 != Set())) ==>
          ($reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}dus): $reduceDTV2) ==
          ($opApplyKey($reduceGetOperKeyS(${prefix}c),
            ($reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
            ($reduceApplyKeyS(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2)): $reduceDTV2)
    }"""
  }

  private def disjUnionAxiom(): String = {
    s"""axiom _disjUnion {
        forall ${prefix}rh: $intKey,
               ${prefix}c: $reduceDKeyM[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs1: Set[$reduceDTV0],
               ${prefix}fs2: Set[$reduceDTV0],
               ${prefix}dus: Set[$reduceDTV0] ::
        { ($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
          ($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2),
          (disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) }
        (disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) ==>
          ($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}dus): $reduceDTV2) ==
          ($opApplyKey($reduceGetOperKeyM(${prefix}c),
            ($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
            ($reduceApplyKeyM(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2)): $reduceDTV2)
    }"""
  }

  private def extensionalityAxiomWithoutId(): String = {
    s"""axiom _extensionality {
        forall ${prefix}rh_old: $intKey,
               ${prefix}rh_new: $intKey,
               ${prefix}c: $reduceDKeyS[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs: Set[$reduceDTV0] ::
        { ($trigExtKeyS(($reduceApplyPrimeKeyS(${prefix}rh_old, ${prefix}c, ${prefix}fs): $reduceDTV2),
                       ($reduceApplyPrimeKeyS(${prefix}rh_new, ${prefix}c, ${prefix}fs): $reduceDTV2)): Bool) }
        ($reduceApplyKeyS(${prefix}rh_old, ${prefix}c, ${prefix}fs) == $reduceApplyKeyS(${prefix}rh_new, ${prefix}c, ${prefix}fs)) ||
        (((${prefix}fs != Set()) && ($skExtKeyS(${prefix}c, $reduceApplyPrimeKeyS(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKeyS(${prefix}rh_new, ${prefix}c, ${prefix}fs)) in ${prefix}fs ==>
            (($rHeapElemKeyS(${prefix}rh_old, ${prefix}c, $skExtKeyS(${prefix}c, $reduceApplyPrimeKeyS(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKeyS(${prefix}rh_new, ${prefix}c, ${prefix}fs))): $reduceDTV2)) ==
            (($rHeapElemKeyS(${prefix}rh_new, ${prefix}c, $skExtKeyS(${prefix}c, $reduceApplyPrimeKeyS(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKeyS(${prefix}rh_new, ${prefix}c, ${prefix}fs))): $reduceDTV2))))
        ==>
        ($reduceApplyPrimeKeyS(${prefix}rh_old, ${prefix}c, ${prefix}fs) == $reduceApplyPrimeKeyS(${prefix}rh_new, ${prefix}c, ${prefix}fs)))
    }"""
  }

  private def extensionalityAxiom(): String = {
    s"""axiom _extensionality {
        forall ${prefix}rh_old: $intKey,
               ${prefix}rh_new: $intKey,
               ${prefix}c: $reduceDKeyM[$reduceDTV0,$reduceDTV1,$reduceDTV2],
               ${prefix}fs: Set[$reduceDTV0] ::
        { ($trigExtKeyM(($reduceApplyPrimeKeyM(${prefix}rh_old, ${prefix}c, ${prefix}fs): $reduceDTV2),
                       ($reduceApplyPrimeKeyM(${prefix}rh_new, ${prefix}c, ${prefix}fs): $reduceDTV2)): Bool) }
        ($reduceApplyKeyM(${prefix}rh_old, ${prefix}c, ${prefix}fs) == $reduceApplyKeyM(${prefix}rh_new, ${prefix}c, ${prefix}fs)) ||
        (($skExtKeyM(${prefix}c, $reduceApplyPrimeKeyM(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKeyM(${prefix}rh_new, ${prefix}c, ${prefix}fs)) in ${prefix}fs ==>
            (($rHeapElemKeyM(${prefix}rh_old, ${prefix}c, $skExtKeyM(${prefix}c, $reduceApplyPrimeKeyM(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKeyM(${prefix}rh_new, ${prefix}c, ${prefix}fs))): $reduceDTV2)) ==
            (($rHeapElemKeyM(${prefix}rh_new, ${prefix}c, $skExtKeyM(${prefix}c, $reduceApplyPrimeKeyM(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKeyM(${prefix}rh_new, ${prefix}c, ${prefix}fs))): $reduceDTV2)))
        ==>
        ($reduceApplyPrimeKeyM(${prefix}rh_old, ${prefix}c, ${prefix}fs) == $reduceApplyPrimeKeyM(${prefix}rh_new, ${prefix}c, ${prefix}fs)))
    }"""
  }

  private def reduceDomainStringSorM(domainName: String,
                                     reduceConstructKey: String,
                                     reduceApplyKey: String,
                                     reduceApplyPrimeKey: String,
                                     reduceApplyDummyKey: String,
                                     setEqDummyKey: String,
                                     reduceGetRecvKey: String,
                                     reduceGetOperKey: String,
                                     reduceGetMappingKey: String,
                                     rHeapElemKey: String,
                                     trigDelKey1Key: String,
                                     trigDelBlockKey: String,
                                     exhaleReduceSetKey: String,
                                     getFieldIDKey: String,
                                     skExtKey: String,
                                     trigExtKey: String,
                                     emptyAxiom: String,
                                     dropAxiom: String,
                                     loseAxiom: String,
                                     disjAxiom: String,
                                     extAxiom: String): String = {
    val reduceOut =
      s"""domain $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2] {
         |
         |    function $reduceConstructKey(r: $recDKey[$reduceDTV0], m: $mapDKey[$reduceDTV1,$reduceDTV2], op: $opDKey[$reduceDTV2]): $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2]
         |    function $reduceApplyKey(rh: $intKey, c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2], fs: Set[$reduceDTV0]): $reduceDTV2
         |    function $reduceApplyPrimeKey(rh: $intKey, c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2], fs: Set[$reduceDTV0]): $reduceDTV2
         |    function $reduceApplyDummyKey(a: $reduceDTV2): Bool
         |    function $setEqDummyKey(b: Bool): Bool
         |
         |    axiom applyReduce1Eq {
         |        forall ${prefix}rh: $intKey, ${prefix}c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2], ${prefix}fs: Set[$reduceDTV0] ::
         |            { ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs): $reduceDTV2) }
         |        $reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs) == $reduceApplyPrimeKey(${prefix}rh, ${prefix}c, ${prefix}fs)
         |    }
         |
         |    function $reduceGetRecvKey(c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2]): $recDKey[$reduceDTV0]
         |    function $reduceGetOperKey(c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2]): $opDKey[$reduceDTV2]
         |    function $reduceGetMappingKey(c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2]): $mapDKey[$reduceDTV1,$reduceDTV2]
         |
         |    function $rHeapElemKey(rh: $intKey, c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2], a: $reduceDTV0): $reduceDTV2
         |
         |    function $trigDelBlockKey(applyC: $reduceDTV2, block: Set[$reduceDTV0]): Bool
         |    function $trigDelKey1Key(applyC: $reduceDTV2, key: $reduceDTV0): Bool
         |
         |    function $exhaleReduceSetKey(rh: $intKey,
         |                           c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |                           fs: Set[$reduceDTV0],
         |                           fieldID: Int): Bool
         |
         |    function $getFieldIDKey(c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2]): Int
         |
         |    axiom _invAxReduce {
         |        forall ${prefix}r: $recDKey[$reduceDTV0],
         |               ${prefix}m: $mapDKey[$reduceDTV1,$reduceDTV2],
         |               ${prefix}o: $opDKey[$reduceDTV2] ::
         |        { ($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o): $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2]) }
         |        $reduceGetRecvKey($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}r &&
         |        $reduceGetMappingKey($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}m &&
         |        $reduceGetOperKey($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}o
         |    }
         |    $emptyAxiom
         |    axiom _singleton {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}elem: $reduceDTV0 ::
         |        { ($reduceApplyKey(${prefix}rh, ${prefix}c, Set(${prefix}elem)): $reduceDTV2),
         |          ($rHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}elem): $reduceDTV2) }
         |        $reduceApplyKey(${prefix}rh, ${prefix}c, Set(${prefix}elem)) == $rHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}elem)
         |    }
         |
         |    $dropAxiom
         |
         |    $loseAxiom
         |
         |    axiom _setExtEq {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs1: Set[$reduceDTV0],
         |               ${prefix}fs2: Set[$reduceDTV0] ::
         |        { ($reduceApplyPrimeKey(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
         |          ($reduceApplyPrimeKey(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2) }
         |        $setEqDummyKey(${prefix}fs1 == ${prefix}fs2)
         |    }
         |
         |    $disjAxiom
         |
         |    function $skExtKey(c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2], hfA1: $reduceDTV2, hfA2: $reduceDTV2): $reduceDTV0
         |    function $trigExtKey(hfA1: $reduceDTV2, hfA2: $reduceDTV2): Bool
         |
         |    axiom _trigExtensionality {
         |        forall ${prefix}rh_old: $intKey,
         |               ${prefix}rh_new: $intKey,
         |               ${prefix}c: $domainName[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs: Set[$reduceDTV0] ::
         |        { ($reduceApplyKey(${prefix}rh_old, ${prefix}c, ${prefix}fs): $reduceDTV2),
         |          ($reduceApplyKey(${prefix}rh_new, ${prefix}c, ${prefix}fs): $reduceDTV2) }
         |        ($trigExtKey(($reduceApplyPrimeKey(${prefix}rh_old, ${prefix}c, ${prefix}fs): $reduceDTV2),
         |                  ($reduceApplyPrimeKey(${prefix}rh_new, ${prefix}c, ${prefix}fs): $reduceDTV2)))
         |    }
         |
         |    $extAxiom
         |}\n """.stripMargin
    reduceOut
  }

  def reduceDomainStringNoId(): String =
    reduceDomainStringSorM(
      reduceDKeyS,
      reduceConstructKeyS,
      reduceApplyKeyS,
      reduceApplyPrimeKeyS,
      reduceApplyDummyKeyS,
      setEqDummyKeyS,
      reduceGetRecvKeyS,
      reduceGetOperKeyS,
      reduceGetMappingKeyS,
      rHeapElemKeyS,
      trigDelKey1KeyS,
      trigDelBlockKeyS,
      exhaleReduceSetKeyS,
      getFieldIDKeyS,
      skExtKeyS,
      trigExtKeyS,
      s"""""",
      dropOneAxiomWithoutId(),
      loseManyAxiomWithoutId(),
      disjUnionAxiomWithoutId(),
      extensionalityAxiomWithoutId()
    )

  def reduceDomainString(): String =
    reduceDomainStringSorM(
      reduceDKeyM,
      reduceConstructKeyM,
      reduceApplyKeyM,
      reduceApplyPrimeKeyM,
      reduceApplyDummyKeyM,
      setEqDummyKeyM,
      reduceGetRecvKeyM,
      reduceGetOperKeyM,
      reduceGetMappingKeyM,
      rHeapElemKeyM,
      trigDelKey1KeyM,
      trigDelBlockKeyM,
      exhaleReduceSetKeyM,
      getFieldIDKeyM,
      skExtKeyM,
      trigExtKeyM,
      emptyReduceAxiom(),
      dropOneAxiom(),
      loseManyAxiom(),
      disjUnionAxiom(),
      extensionalityAxiom()
    )

  def setEditDomainString(): String = {
    val setOut =
      s"""domain SetEdit[$reduceDTV0] {
         |    function $setDeleteKey(m: Set[$reduceDTV0], e: Set[$reduceDTV0]): Set[$reduceDTV0]
         |    function disjUnionEq(s1: Set[$reduceDTV0], s2: Set[$reduceDTV0], s3: Set[$reduceDTV0]): Bool
         |
         |    axiom _disjUnionEqDef {
         |        (forall ${prefix}s1: Set[$reduceDTV0], ${prefix}s2: Set[$reduceDTV0], ${prefix}s3: Set[$reduceDTV0] ::
         |            { (disjUnionEq(${prefix}s1, ${prefix}s2, ${prefix}s3): Bool) }
         |        (disjUnionEq(${prefix}s1, ${prefix}s2, ${prefix}s3): Bool) ==
         |        ((${prefix}s1 intersection ${prefix}s2) == Set[$reduceDTV0]() &&
         |          (${prefix}s1 union ${prefix}s2) == ${prefix}s3))
         |    }
         |
         |    axiom _setDeleteAxiom {
         |        (forall ${prefix}s: Set[$reduceDTV0], ${prefix}e: Set[$reduceDTV0] ::
         |            { ($setDeleteKey(${prefix}s, ${prefix}e): Set[$reduceDTV0]) }
         |        ($setDeleteKey(${prefix}s, ${prefix}e): Set[$reduceDTV0]) == ${prefix}s setminus ${prefix}e)
         |    }
         |
         |    axiom _setDeleteSubset {
         |        (forall ${prefix}s: Set[$reduceDTV0], ${prefix}e: Set[$reduceDTV0] ::
         |            { ($setDeleteKey(${prefix}s, ${prefix}e): Set[$reduceDTV0]) }
         |        ($setDeleteKey(${prefix}s, ${prefix}e): Set[$reduceDTV0]) subset ${prefix}s)
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
        changePosRecursive(newDomain, (NoPosition, NoPosition)).asInstanceOf[PDomain]
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
    body.withChildren(children, Some(pos))
  }
}
