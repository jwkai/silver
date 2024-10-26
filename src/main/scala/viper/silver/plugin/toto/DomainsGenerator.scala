package viper.silver.plugin.toto

import fastparse.{P, Parsed, StringIn}
import viper.silver.ast.{NoPosition, Position}
import viper.silver.parser.{FastParser, PDomain, PKw, PNode, PReserved}

case class ParseException(msg: String, pos: (Position, Position)) extends Exception

object DomainsGenerator {
  final val intKey = "Int"
  final val compDKey = "Fold"
  final val compDTV0 = "A"
  final val compDTV1 = "V"
  final val compDTV2 = "B"
  final val prefix = "__fold_"

  final val compConstructKey = "hfold"
  final val compApplyKey = "hfoldApply"
  final val compApplyPrimeKey = "hfoldApply1"
  final val compApplyDummyKey = "hfoldApplyDummy"
  final val compGetRecvKey = "getreceiver"
  final val compGetOperKey = "getoperator"
  final val compGetMappingKey = "getmapping"
  final val fHeapElemKey = "fHeapElem"
//  final val fHeapIdxKey = "heapIdx"
//  final val fHeapSKey = "fHeapSucc"
//  final val fHeapSTKey = "fHeapSuccTransitive"
  final val recApplyKey = "recApply"
  final val recInvKey = "recInv"
  final val opApplyKey = "opApply"
  final val opIdenKey = "opGetIden"
  final val mapApplyKey = "mapApply"
  final val mapIdenKey = "mapIdentity"
  final val disjUnionKey = "disjUnionEq"
  final val exhaleFoldSetKey = "exhaleFoldSet"
  final val trigDelKey1Key = "triggerDeleteKey1"
  final val trigDelBlockKey = "triggerDeleteBlock"
  final val trigExtKey = "triggerExt"
  final val getFieldIDKey = "getFieldID"

  final val filterRecvGoodKey = "filterReceiverGood"
  final val subsetNotInRefsKey = "subsetNotInRefs"
  final val idxNotInRefsKey = "idxNotInRefs"
  final val setDeleteKey = "setDelete"

//  final val fHeapKey = "fHeap"
  final val recDKey = "Receiver"
  final val mapDKey = "Mapping"
  final val opDKey = "Operator"

//  def fHeapDomainString(): String = {
//    val fHeapOut =
//      s"""domain $fHeapKey {
//         |    function $fHeapIdxKey(h: $fHeapKey): Int
//         |    function $fHeapSKey(h1: $fHeapKey, h2: $fHeapKey): Bool
//         |    function $fHeapSTKey(h1: $fHeapKey, h2: $fHeapKey): Bool
//         |
//         |    axiom _iso {
//         |        forall ${prefix}h1: fHeap, ${prefix}h2: fHeap ::
//         |            { $fHeapIdxKey(${prefix}h1), $fHeapIdxKey(${prefix}h2) }
//         |            $fHeapIdxKey(${prefix}h1) == $fHeapIdxKey(${prefix}h2) <==> ${prefix}h1 == ${prefix}h2
//         |    }
//         |
//         |    axiom _idxSucc {
//         |        forall ${prefix}h1: fHeap, ${prefix}h2: fHeap ::
//         |            { $fHeapIdxKey(${prefix}h1), $fHeapIdxKey(${prefix}h2) }
//         |            { $fHeapSKey(${prefix}h1, ${prefix}h2) }
//         |            $fHeapIdxKey(${prefix}h2) == $fHeapIdxKey(${prefix}h1) + 1 ==>
//         |                $fHeapSKey(${prefix}h1, ${prefix}h2)
//         |    }
//         |
//         |    axiom _succIsIrreflexive {
//         |        forall ${prefix}h:fHeap :: { $fHeapSKey(${prefix}h, ${prefix}h) }
//         |            !$fHeapSKey(${prefix}h, ${prefix}h)
//         |    }
//         |
//         |    axiom _transIsIrreflexive {
//         |        forall ${prefix}h:fHeap :: { $fHeapSTKey(${prefix}h, ${prefix}h) }
//         |            !$fHeapSTKey(${prefix}h, ${prefix}h)
//         |    }
//         |
//         |    axiom _succIsTransitive {
//         |        forall ${prefix}h1: fHeap, ${prefix}h2: fHeap ::
//         |            { $fHeapSKey(${prefix}h1, ${prefix}h2) }
//         |            $fHeapSKey(${prefix}h1, ${prefix}h2) ==> $fHeapSTKey(${prefix}h1, ${prefix}h2)
//         |    }
//         |
//         |    axiom _transitive {
//         |        forall ${prefix}h1: fHeap, ${prefix}h2: fHeap, ${prefix}h3: fHeap ::
//         |            { $fHeapSTKey(${prefix}h1, ${prefix}h2), $fHeapSTKey(${prefix}h2, ${prefix}h3) }
//         |            $fHeapSTKey(${prefix}h1, ${prefix}h2) && $fHeapSTKey(${prefix}h2, ${prefix}h3) ==>
//         |                $fHeapSTKey(${prefix}h1, ${prefix}h3)
//         |    }
//         |}\n """.stripMargin
//    fHeapOut
//  }

  def receiverDomainString(): String = {
    val receiverOut =
      s"""domain $recDKey[$compDTV0] {
         |    function $recApplyKey(r:$recDKey[$compDTV0], a:$compDTV0): Ref
         |    function $recInvKey(rec:$recDKey[$compDTV0], ref:Ref): $compDTV0
         |    function $filterRecvGoodKey(f: Set[$compDTV0], r: $recDKey[$compDTV0]): Bool
         |
         |    function $subsetNotInRefsKey(f1: Set[$compDTV0], r: $recDKey[$compDTV0], lostR: Set[Ref]): Set[$compDTV0]
         |    function $idxNotInRefsKey(a: $compDTV0, r: $recDKey[$compDTV0], domR: Set[Ref]): Bool
         |
         |    axiom _inverse_receiver {
         |        forall ${prefix}a : $compDTV0, ${prefix}f: Set[$compDTV0], ${prefix}r: $recDKey[$compDTV0]
         |        :: { $recApplyKey(${prefix}r,${prefix}a), $filterRecvGoodKey(${prefix}f,${prefix}r) }
         |           { $filterRecvGoodKey(${prefix}f,${prefix}r), ${prefix}a in ${prefix}f }
         |        $filterRecvGoodKey(${prefix}f,${prefix}r) && ${prefix}a in ${prefix}f ==>
         |        $filterRecvGoodKey(${prefix}f,${prefix}r) &&
         |        ${prefix}a in ${prefix}f && $recInvKey(${prefix}r,$recApplyKey(${prefix}r,${prefix}a)) == ${prefix}a
         |    }
         |
         |    axiom _inverse_receiver1 {
         |        forall ${prefix}ref: Ref, ${prefix}f: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0]
         |        :: { $filterRecvGoodKey(${prefix}f, ${prefix}r), $recInvKey(${prefix}r, ${prefix}ref) }
         |        $filterRecvGoodKey(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f ==>
         |        $filterRecvGoodKey(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f &&
         |        $recApplyKey(${prefix}r,$recInvKey(${prefix}r,${prefix}ref)) == ${prefix}ref
         |    }
         |
         |    axiom smallerF {
         |        forall ${prefix}f1: Set[$compDTV0], ${prefix}f2: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0] ::
         |        { ${prefix}f2 subset ${prefix}f1, $filterRecvGoodKey(${prefix}f1,${prefix}r) }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) && ${prefix}f2 subset ${prefix}f1 ==>
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |          ${prefix}f2 subset ${prefix}f1 && $filterRecvGoodKey(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom smallerFDelete {
         |        forall ${prefix}f1: Set[$compDTV0], ${prefix}f2: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0] ::
         |        { $filterRecvGoodKey(${prefix}f1,${prefix}r), ${prefix}f1 setminus ${prefix}f2 }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) ==> $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |        $filterRecvGoodKey(${prefix}f1 setminus ${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom unionF {
         |        forall ${prefix}f1: Set[$compDTV0], ${prefix}f2: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0] ::
         |        { $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) }
         |        $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) ==>
         |        $filterRecvGoodKey(${prefix}f1 union ${prefix}f2,${prefix}r) &&
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) && $filterRecvGoodKey(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _subsetNotInRefsAxiom {
         |        forall ${prefix}a: $compDTV0, ${prefix}fs: Set[$compDTV0], ${prefix}r: $recDKey[$compDTV0],
         |          ${prefix}lostR: Set[Ref] ::
         |        { ${prefix}a in $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) }
         |            ${prefix}a in $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) <==>
         |                (${prefix}a in ${prefix}fs && !($recApplyKey(${prefix}r, ${prefix}a) in ${prefix}lostR))
         |    }
         |
         |    axiom _subsetNotInRefsSubset {
         |        forall ${prefix}fs: Set[$compDTV0], ${prefix}r: $recDKey[$compDTV0], ${prefix}lostR: Set[Ref] ::
         |          { $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) }
         |        $subsetNotInRefsKey(${prefix}fs, ${prefix}r, ${prefix}lostR) subset ${prefix}fs
         |    }
         |
         |    axiom _idxNotInRefSetAxiom {
         |       (forall ${prefix}a: $compDTV0, ${prefix}recv: $recDKey[$compDTV0], ${prefix}domR: Set[Ref] ::
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
      s"""domain $mapDKey[$compDTV1,$compDTV2] {
         |
         |    function $mapApplyKey(m: $mapDKey[$compDTV1,$compDTV2], _mInput:$compDTV1): $compDTV2
         |
         |    function $mapIdenKey(): $mapDKey[$compDTV1,$compDTV1]
         |
         |    axiom {
         |      forall __v: $compDTV1 :: { $mapApplyKey($mapIdenKey() ,__v) }
         |      $mapApplyKey($mapIdenKey() , __v) == __v
         |    }
         |
         |}\n """.stripMargin
    mappingOut
  }

  def opDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val opOut =
      s"""domain $opDKey[$compDTV2] {
         |
         |    function _noTrigOp(out: $compDTV2): Bool
         |    function $opApplyKey(op: $opDKey[$compDTV2], val1:$compDTV2, val2:$compDTV2): $compDTV2
         |    function $opIdenKey(op: $opDKey[$compDTV2]): $compDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    opOut
  }

  def compDomainString(): String = {
    val compOut =
      s"""domain $compDKey[$compDTV0,$compDTV1,$compDTV2] {
         |
         |    function $compConstructKey(r:$recDKey[$compDTV0], m: $mapDKey[$compDTV1,$compDTV2], op: $opDKey[$compDTV2]): $compDKey[$compDTV0,$compDTV1,$compDTV2]
         |    function $compApplyKey(fh: $intKey, c: $compDKey[$compDTV0,$compDTV1,$compDTV2], fs: Set[$compDTV0]): $compDTV2
         |    function $compApplyPrimeKey(fh: $intKey, c: $compDKey[$compDTV0,$compDTV1,$compDTV2], fs: Set[$compDTV0]): $compDTV2
         |
         |    axiom applyComp1Eq {
         |        forall ${prefix}fh: $intKey, ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2], ${prefix}fs: Set[$compDTV0] ::
         |            { ($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs): $compDTV2) }
         |        $compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs) == $compApplyPrimeKey(${prefix}fh, ${prefix}c, ${prefix}fs)
         |    }
         |
         |    function $compGetRecvKey(c:$compDKey[$compDTV0,$compDTV1,$compDTV2]): $recDKey[$compDTV0]
         |    function $compGetOperKey(c:$compDKey[$compDTV0,$compDTV1,$compDTV2]): $opDKey[$compDTV2]
         |    function $compGetMappingKey(c:$compDKey[$compDTV0,$compDTV1,$compDTV2]): $mapDKey[$compDTV1,$compDTV2]
         |
         |    function $compApplyDummyKey(a:$compDTV2): Bool
         |    function setEqDummy(b: Bool): Bool
         |    function $fHeapElemKey(c: $compDKey[$compDTV0,$compDTV1,$compDTV2], h: $intKey, a: $compDTV0): $compDTV2
         |
         |    function $trigDelBlockKey(applyC: $compDTV2, block: Set[$compDTV0]): Bool
         |    function $trigDelKey1Key(applyC: $compDTV2, key: $compDTV0): Bool
         |
         |    function $exhaleFoldSetKey(fh: $intKey,
         |                           c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |                           fs: Set[$compDTV0],
         |                           fieldID: Int): Bool
         |
         |    function $getFieldIDKey(c: $compDKey[$compDTV0,$compDTV1,$compDTV2]): Int
         |
         |    axiom _invAxFold {
         |        forall ${prefix}r: $recDKey[$compDTV0],
         |               ${prefix}m: $mapDKey[$compDTV1,$compDTV2],
         |               ${prefix}o: $opDKey[$compDTV2] ::
         |        { ($compConstructKey(${prefix}r, ${prefix}m, ${prefix}o): $compDKey[$compDTV0,$compDTV1,$compDTV2]) }
         |        $compGetRecvKey($compConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}r &&
         |        $compGetMappingKey($compConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}m &&
         |        $compGetOperKey($compConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}o
         |    }
         |
         |    axiom _emptyFold {
         |        forall ${prefix}fh: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}fs: Set[$compDTV0] ::
         |        { ($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs): $compDTV2) }
         |        ${prefix}fs == Set[$compDTV0]() ==>
         |        ${prefix}fs == Set[$compDTV0]() &&
         |        $compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs) == $opIdenKey($compGetOperKey(${prefix}c))
         |    }
         |
         |    axiom _singleton {
         |        forall ${prefix}fh: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}elem: $compDTV0 ::
         |        { ($compApplyKey(${prefix}fh, ${prefix}c, Set(${prefix}elem)): $compDTV2),
         |          ($fHeapElemKey(${prefix}c, ${prefix}fh, ${prefix}elem): $compDTV2) }
         |        $compApplyKey(${prefix}fh, ${prefix}c, Set(${prefix}elem)) == $fHeapElemKey(${prefix}c, ${prefix}fh, ${prefix}elem)
         |    }
         |
         |    axiom _dropOne1 {
         |        forall ${prefix}fh: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}fs: Set[$compDTV0],
         |               ${prefix}key: $compDTV0 ::
         |        { ($trigDelKey1Key($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs), ${prefix}key): Bool),
         |          ($fHeapElemKey(${prefix}c, ${prefix}fh, ${prefix}key): $compDTV2) }
         |        (${prefix}key in ${prefix}fs) ==>
         |        (${prefix}key in ${prefix}fs) &&
         |        $compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs) ==
         |        $opApplyKey($compGetOperKey(${prefix}c),
         |          $compApplyPrimeKey(${prefix}fh, ${prefix}c, $setDeleteKey(${prefix}fs, Set(${prefix}key))),
         |          $fHeapElemKey(${prefix}c, ${prefix}fh, ${prefix}key))
         |    }
         |
         |    axiom _loseMany {
         |        forall ${prefix}fh: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}fs: Set[$compDTV0],
         |               ${prefix}keys: Set[$compDTV0] ::
         |        { $trigDelBlockKey($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs), ${prefix}keys) }
         |        (${prefix}keys subset ${prefix}fs) ==>
         |        (${prefix}keys subset ${prefix}fs) &&
         |        $compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs) ==
         |        $opApplyKey($compGetOperKey(${prefix}c),
         |          $compApplyPrimeKey(${prefix}fh, ${prefix}c, $setDeleteKey(${prefix}fs, ${prefix}keys)),
         |          $compApplyPrimeKey(${prefix}fh, ${prefix}c, ${prefix}keys))
         |    }
         |
         |    axiom _setExtEq {
         |        forall ${prefix}fh: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}fs1: Set[$compDTV0],
         |               ${prefix}fs2: Set[$compDTV0] ::
         |        { ($compApplyPrimeKey(${prefix}fh, ${prefix}c, ${prefix}fs1): $compDTV2),
         |          ($compApplyPrimeKey(${prefix}fh, ${prefix}c, ${prefix}fs2): $compDTV2) }
         |        setEqDummy(${prefix}fs1 == ${prefix}fs2)
         |    }
         |
         |    axiom _disjUnion {
         |        forall ${prefix}fh: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}fs1: Set[$compDTV0],
         |               ${prefix}fs2: Set[$compDTV0],
         |               ${prefix}dus: Set[$compDTV0] ::
         |        { ($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs1): $compDTV2),
         |          ($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs2): $compDTV2),
         |          (disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) }
         |        (disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) ==>
         |          ($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}dus): $compDTV2) ==
         |          ($opApplyKey($compGetOperKey(${prefix}c),
         |            ($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs1): $compDTV2),
         |            ($compApplyKey(${prefix}fh, ${prefix}c, ${prefix}fs2): $compDTV2)): $compDTV2)
         |    }
         |
         |    function _skExt(c: $compDKey[$compDTV0,$compDTV1,$compDTV2], hfA1: $compDTV2, hfA2: $compDTV2): $compDTV0
         |    function $trigExtKey(hfA1: $compDTV2, hfA2: $compDTV2): Bool
         |
         |    axiom _trigExtensionality {
         |        forall ${prefix}fh_old: $intKey,
         |               ${prefix}fh_new: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}fs: Set[$compDTV0] ::
         |        { ($compApplyKey(${prefix}fh_old, ${prefix}c, ${prefix}fs): $compDTV2),
         |          ($compApplyKey(${prefix}fh_new, ${prefix}c, ${prefix}fs): $compDTV2) }
         |        ($trigExtKey(($compApplyPrimeKey(${prefix}fh_old, ${prefix}c, ${prefix}fs): $compDTV2),
         |                  ($compApplyPrimeKey(${prefix}fh_new, ${prefix}c, ${prefix}fs): $compDTV2)))
         |    }
         |
         |    axiom _extensionality {
         |        forall ${prefix}fh_old: $intKey,
         |               ${prefix}fh_new: $intKey,
         |               ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}fs: Set[$compDTV0] ::
         |        { ($trigExtKey(($compApplyPrimeKey(${prefix}fh_old, ${prefix}c, ${prefix}fs): $compDTV2),
         |                       ($compApplyPrimeKey(${prefix}fh_new, ${prefix}c, ${prefix}fs): $compDTV2)): Bool) }
         |        ($compApplyKey(${prefix}fh_old, ${prefix}c, ${prefix}fs) == $compApplyKey(${prefix}fh_new, ${prefix}c, ${prefix}fs)) ||
         |        ((_skExt(${prefix}c, $compApplyPrimeKey(${prefix}fh_old, ${prefix}c, ${prefix}fs), $compApplyPrimeKey(${prefix}fh_new, ${prefix}c, ${prefix}fs)) in ${prefix}fs ==>
         |            (($fHeapElemKey(${prefix}c, ${prefix}fh_old, _skExt(${prefix}c, $compApplyPrimeKey(${prefix}fh_old, ${prefix}c, ${prefix}fs), $compApplyPrimeKey(${prefix}fh_new, ${prefix}c, ${prefix}fs))): $compDTV2)) ==
         |            (($fHeapElemKey(${prefix}c, ${prefix}fh_new, _skExt(${prefix}c, $compApplyPrimeKey(${prefix}fh_old, ${prefix}c, ${prefix}fs), $compApplyPrimeKey(${prefix}fh_new, ${prefix}c, ${prefix}fs))): $compDTV2)))
         |        ==>
         |        ($compApplyPrimeKey(${prefix}fh_old, ${prefix}c, ${prefix}fs) == $compApplyPrimeKey(${prefix}fh_new, ${prefix}c, ${prefix}fs)))
         |    }
         |}
         |
         |
         |
         |
         |}\n """.stripMargin
    compOut
  }

  def setEditDomainString(): String = {
    val setOut =
      s"""domain SetEdit[$compDTV0] {
         |    function $setDeleteKey(m: Set[$compDTV0], e: Set[$compDTV0]): Set[$compDTV0]
         |    function disjUnionEq(s1: Set[$compDTV0], s2: Set[$compDTV0], s3: Set[$compDTV0]): Bool
         |
         |    axiom _disjUnionEqDef {
         |        (forall ${prefix}s1: Set[$compDTV0], ${prefix}s2: Set[$compDTV0], ${prefix}s3: Set[$compDTV0] ::
         |            { (disjUnionEq(${prefix}s1, ${prefix}s2, ${prefix}s3): Bool) }
         |        (disjUnionEq(${prefix}s1, ${prefix}s2, ${prefix}s3): Bool) ==
         |        ((${prefix}s1 intersection ${prefix}s2) == Set[$compDTV0]() &&
         |          (${prefix}s1 union ${prefix}s2) == ${prefix}s3))
         |    }
         |
         |    axiom _setDeleteAxiom {
         |        (forall ${prefix}s: Set[$compDTV0], ${prefix}e: Set[$compDTV0] ::
         |            { ($setDeleteKey(${prefix}s, ${prefix}e): Set[$compDTV0]) }
         |        ($setDeleteKey(${prefix}s, ${prefix}e): Set[$compDTV0]) == ${prefix}s setminus ${prefix}e)
         |    }
         |
         |    axiom _setDeleteSubset {
         |        (forall ${prefix}s: Set[$compDTV0], ${prefix}e: Set[$compDTV0] ::
         |            { ($setDeleteKey(${prefix}s, ${prefix}e): Set[$compDTV0]) }
         |        ($setDeleteKey(${prefix}s, ${prefix}e): Set[$compDTV0]) subset ${prefix}s)
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
