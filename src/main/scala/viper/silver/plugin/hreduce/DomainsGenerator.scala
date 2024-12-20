package viper.silver.plugin.hreduce

import fastparse.{P, Parsed, StringIn}
import viper.silver.ast.{NoPosition, Position}
import viper.silver.parser.{FastParser, PDomain, PKw, PNode, PReserved}

case class ParseException(msg: String, pos: (Position, Position)) extends Exception

object DomainsGenerator {
  final val intKey = "Int"
  final val reduceDKey = "Reduce"
  final val reduceDTV0 = "A"
  final val reduceDTV1 = "V"
  final val reduceDTV2 = "B"
  final val prefix = "__reduce_"

  final val reduceConstructKey = "hreduce"
  final val reduceApplyKey = "hreduceApply"
  final val reduceApplyPrimeKey = "hreduceApply1"
  final val reduceApplyDummyKey = "hreduceApplyDummy"
  final val reduceGetRecvKey = "getreceiver"
  final val reduceGetOperKey = "getoperator"
  final val reduceGetMappingKey = "getmapping"
  final val rHeapElemKey = "rHeapElem"
  final val recApplyKey = "recApply"
  final val recInvKey = "recInv"
  final val opApplyKey = "opApply"
  final val opIdenKey = "opGetIden"
  final val mapApplyKey = "mapApply"
  final val mapIdenKey = "mapIdentity"
  final val disjUnionKey = "disjUnionEq"
  final val exhaleReduceSetKey = "exhaleReduceSet"
  final val trigDelKey1Key = "triggerDeleteKey1"
  final val trigDelBlockKey = "triggerDeleteBlock"
  final val trigExtKey = "triggerExt"
  final val getFieldIDKey = "getFieldID"

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
         |    axiom smallerF {
         |        forall ${prefix}f1: Set[$reduceDTV0], ${prefix}f2: Set[$reduceDTV0], ${prefix}r:$recDKey[$reduceDTV0] ::
         |        { ${prefix}f2 subset ${prefix}f1, $filterRecvGoodKey(${prefix}f1,${prefix}r) }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) && ${prefix}f2 subset ${prefix}f1 ==>
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |          ${prefix}f2 subset ${prefix}f1 && $filterRecvGoodKey(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom smallerFDelete {
         |        forall ${prefix}f1: Set[$reduceDTV0], ${prefix}f2: Set[$reduceDTV0], ${prefix}r:$recDKey[$reduceDTV0] ::
         |        { $filterRecvGoodKey(${prefix}f1,${prefix}r), ${prefix}f1 setminus ${prefix}f2 }
         |        $filterRecvGoodKey(${prefix}f1,${prefix}r) ==> $filterRecvGoodKey(${prefix}f1,${prefix}r) &&
         |        $filterRecvGoodKey(${prefix}f1 setminus ${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom unionF {
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

  def reduceDomainString(): String = {
    val reduceOut =
      s"""domain $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2] {
         |
         |    function $reduceConstructKey(r:$recDKey[$reduceDTV0], m: $mapDKey[$reduceDTV1,$reduceDTV2], op: $opDKey[$reduceDTV2]): $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2]
         |    function $reduceApplyKey(rh: $intKey, c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2], fs: Set[$reduceDTV0]): $reduceDTV2
         |    function $reduceApplyPrimeKey(rh: $intKey, c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2], fs: Set[$reduceDTV0]): $reduceDTV2
         |
         |    axiom applyReduce1Eq {
         |        forall ${prefix}rh: $intKey, ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2], ${prefix}fs: Set[$reduceDTV0] ::
         |            { ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs): $reduceDTV2) }
         |        $reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs) == $reduceApplyPrimeKey(${prefix}rh, ${prefix}c, ${prefix}fs)
         |    }
         |
         |    function $reduceGetRecvKey(c:$reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2]): $recDKey[$reduceDTV0]
         |    function $reduceGetOperKey(c:$reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2]): $opDKey[$reduceDTV2]
         |    function $reduceGetMappingKey(c:$reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2]): $mapDKey[$reduceDTV1,$reduceDTV2]
         |
         |    function $reduceApplyDummyKey(a:$reduceDTV2): Bool
         |    function setEqDummy(b: Bool): Bool
         |    function $rHeapElemKey(h: $intKey, c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2], a: $reduceDTV0): $reduceDTV2
         |
         |    function $trigDelBlockKey(applyC: $reduceDTV2, block: Set[$reduceDTV0]): Bool
         |    function $trigDelKey1Key(applyC: $reduceDTV2, key: $reduceDTV0): Bool
         |
         |    function $exhaleReduceSetKey(rh: $intKey,
         |                           c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |                           fs: Set[$reduceDTV0],
         |                           fieldID: Int): Bool
         |
         |    function $getFieldIDKey(c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2]): Int
         |
         |    axiom _invAxReduce {
         |        forall ${prefix}r: $recDKey[$reduceDTV0],
         |               ${prefix}m: $mapDKey[$reduceDTV1,$reduceDTV2],
         |               ${prefix}o: $opDKey[$reduceDTV2] ::
         |        { ($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o): $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2]) }
         |        $reduceGetRecvKey($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}r &&
         |        $reduceGetMappingKey($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}m &&
         |        $reduceGetOperKey($reduceConstructKey(${prefix}r, ${prefix}m, ${prefix}o)) == ${prefix}o
         |    }
         |
         |    axiom _emptyReduce {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs: Set[$reduceDTV0] ::
         |        { ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs): $reduceDTV2) }
         |        ${prefix}fs == Set[$reduceDTV0]() ==>
         |        ${prefix}fs == Set[$reduceDTV0]() &&
         |        $reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs) == $opIdenKey($reduceGetOperKey(${prefix}c))
         |    }
         |
         |    axiom _singleton {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}elem: $reduceDTV0 ::
         |        { ($reduceApplyKey(${prefix}rh, ${prefix}c, Set(${prefix}elem)): $reduceDTV2),
         |          ($rHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}elem): $reduceDTV2) }
         |        $reduceApplyKey(${prefix}rh, ${prefix}c, Set(${prefix}elem)) == $rHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}elem)
         |    }
         |
         |    axiom _dropOne1 {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs: Set[$reduceDTV0],
         |               ${prefix}key: $reduceDTV0 ::
         |        { ($trigDelKey1Key($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}key): Bool),
         |          ($rHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}key): $reduceDTV2) }
         |        (${prefix}key in ${prefix}fs) ==>
         |        (${prefix}key in ${prefix}fs) &&
         |        $reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs) ==
         |        $opApplyKey($reduceGetOperKey(${prefix}c),
         |          $reduceApplyPrimeKey(${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, Set(${prefix}key))),
         |          $rHeapElemKey(${prefix}rh, ${prefix}c, ${prefix}key))
         |    }
         |
         |    axiom _loseMany {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs: Set[$reduceDTV0],
         |               ${prefix}keys: Set[$reduceDTV0] ::
         |        { $trigDelBlockKey($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs), ${prefix}keys) }
         |        (${prefix}keys subset ${prefix}fs) ==>
         |        (${prefix}keys subset ${prefix}fs) &&
         |        $reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs) ==
         |        $opApplyKey($reduceGetOperKey(${prefix}c),
         |          $reduceApplyPrimeKey(${prefix}rh, ${prefix}c, $setDeleteKey(${prefix}fs, ${prefix}keys)),
         |          $reduceApplyPrimeKey(${prefix}rh, ${prefix}c, ${prefix}keys))
         |    }
         |
         |    axiom _setExtEq {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs1: Set[$reduceDTV0],
         |               ${prefix}fs2: Set[$reduceDTV0] ::
         |        { ($reduceApplyPrimeKey(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
         |          ($reduceApplyPrimeKey(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2) }
         |        setEqDummy(${prefix}fs1 == ${prefix}fs2)
         |    }
         |
         |    axiom _disjUnion {
         |        forall ${prefix}rh: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs1: Set[$reduceDTV0],
         |               ${prefix}fs2: Set[$reduceDTV0],
         |               ${prefix}dus: Set[$reduceDTV0] ::
         |        { ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
         |          ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2),
         |          (disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) }
         |        (disjUnionEq(${prefix}fs1, ${prefix}fs2, ${prefix}dus): Bool) ==>
         |          ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}dus): $reduceDTV2) ==
         |          ($opApplyKey($reduceGetOperKey(${prefix}c),
         |            ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs1): $reduceDTV2),
         |            ($reduceApplyKey(${prefix}rh, ${prefix}c, ${prefix}fs2): $reduceDTV2)): $reduceDTV2)
         |    }
         |
         |    function _skExt(c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2], hfA1: $reduceDTV2, hfA2: $reduceDTV2): $reduceDTV0
         |    function $trigExtKey(hfA1: $reduceDTV2, hfA2: $reduceDTV2): Bool
         |
         |    axiom _trigExtensionality {
         |        forall ${prefix}rh_old: $intKey,
         |               ${prefix}rh_new: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs: Set[$reduceDTV0] ::
         |        { ($reduceApplyKey(${prefix}rh_old, ${prefix}c, ${prefix}fs): $reduceDTV2),
         |          ($reduceApplyKey(${prefix}rh_new, ${prefix}c, ${prefix}fs): $reduceDTV2) }
         |        ($trigExtKey(($reduceApplyPrimeKey(${prefix}rh_old, ${prefix}c, ${prefix}fs): $reduceDTV2),
         |                  ($reduceApplyPrimeKey(${prefix}rh_new, ${prefix}c, ${prefix}fs): $reduceDTV2)))
         |    }
         |
         |    axiom _extensionality {
         |        forall ${prefix}rh_old: $intKey,
         |               ${prefix}rh_new: $intKey,
         |               ${prefix}c: $reduceDKey[$reduceDTV0,$reduceDTV1,$reduceDTV2],
         |               ${prefix}fs: Set[$reduceDTV0] ::
         |        { ($trigExtKey(($reduceApplyPrimeKey(${prefix}rh_old, ${prefix}c, ${prefix}fs): $reduceDTV2),
         |                       ($reduceApplyPrimeKey(${prefix}rh_new, ${prefix}c, ${prefix}fs): $reduceDTV2)): Bool) }
         |        ($reduceApplyKey(${prefix}rh_old, ${prefix}c, ${prefix}fs) == $reduceApplyKey(${prefix}rh_new, ${prefix}c, ${prefix}fs)) ||
         |        ((_skExt(${prefix}c, $reduceApplyPrimeKey(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKey(${prefix}rh_new, ${prefix}c, ${prefix}fs)) in ${prefix}fs ==>
         |            (($rHeapElemKey(${prefix}rh_old, ${prefix}c, _skExt(${prefix}c, $reduceApplyPrimeKey(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKey(${prefix}rh_new, ${prefix}c, ${prefix}fs))): $reduceDTV2)) ==
         |            (($rHeapElemKey(${prefix}rh_new, ${prefix}c, _skExt(${prefix}c, $reduceApplyPrimeKey(${prefix}rh_old, ${prefix}c, ${prefix}fs), $reduceApplyPrimeKey(${prefix}rh_new, ${prefix}c, ${prefix}fs))): $reduceDTV2)))
         |        ==>
         |        ($reduceApplyPrimeKey(${prefix}rh_old, ${prefix}c, ${prefix}fs) == $reduceApplyPrimeKey(${prefix}rh_new, ${prefix}c, ${prefix}fs)))
         |    }
         |}
         |
         |
         |
         |
         |}\n """.stripMargin
    reduceOut
  }

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
