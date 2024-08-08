package viper.silver.plugin.toto

import fastparse.Parsed
import viper.silver.ast.{FilePosition, NoPosition, Position, VirtualPosition}
import viper.silver.parser.{PDomain, PNode, ParseException}


object DomainsGenerator {
  final val compDKey = "Fold"
  final val compDTV0 = "A"
  final val compDTV1 = "V"
  final val compDTV2 = "B"
  final val prefix = "__fold_"


  final val compConstructKey = "hfold"
  final val compApplyKey = "hfoldApply"
  final val compApplyPrimeKey = "hfoldApply1"
  final val recApplyKey = "recApply"
  final val recInvKey = "recInv"
  final val opApplyKey = "opApply"
  final val opIdenKey = "opGetIden"
  final val mapApplyKey = "mapApply"
  final val mapIdenKey = "mapIdentity"
  final val disjUnionKey = "disjUnionEq"

  final val recDKey = "Receiver"
  final val mapDKey = "Mapping"
  final val opDKey = "Operator"

  def receiverDomainString(): String = {
//    val axioms: Seq[String] = Seq()
    val receiverOut =
      s"""domain $recDKey[$compDTV0] {
         |    function $recApplyKey(r:$recDKey[$compDTV0], a:$compDTV0) : Ref
         |    function $recInvKey(rec:$recDKey[$compDTV0], ref:Ref) : $compDTV0
         |    function filterReceiverGood(f: Set[$compDTV0], r: $recDKey[$compDTV0]) : Bool
         |
         |    function filterNotLost(f1: Set[$compDTV0], r: $recDKey[$compDTV0], lostR: Set[Ref]): Set[$compDTV0]
         |
         |    axiom _inverse_receiver {
         |        forall ${prefix}a : $compDTV0, ${prefix}f: Set[$compDTV0], ${prefix}r: $recDKey[$compDTV0]
         |        :: {$recApplyKey(${prefix}r,${prefix}a), filterReceiverGood(${prefix}f,${prefix}r)}
         |          {filterReceiverGood(${prefix}f,${prefix}r), ${prefix}a in ${prefix}f}
         |        filterReceiverGood(${prefix}f,${prefix}r) && ${prefix}a in ${prefix}f ==>
         |        filterReceiverGood(${prefix}f,${prefix}r) &&
         |        ${prefix}a in ${prefix}f && $recInvKey(${prefix}r,$recApplyKey(${prefix}r,${prefix}a)) == ${prefix}a
         |    }
         |
         |    axiom _inverse_receiver1 {
         |        forall ${prefix}ref: Ref, ${prefix}f: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0]
         |        ::{filterReceiverGood(${prefix}f, ${prefix}r), $recInvKey(${prefix}r, ${prefix}ref)}
         |        filterReceiverGood(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f ==>
         |        filterReceiverGood(${prefix}f, ${prefix}r) && $recInvKey(${prefix}r, ${prefix}ref) in ${prefix}f &&
         |        $recApplyKey(${prefix}r,$recInvKey(${prefix}r,${prefix}ref)) == ${prefix}ref
         |    }
         |
         |    axiom smallerF {
         |        forall ${prefix}f1: Set[$compDTV0], ${prefix}f2: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0] ::
         |        {${prefix}f2 subset ${prefix}f1, filterReceiverGood(${prefix}f1,${prefix}r)}
         |        filterReceiverGood(${prefix}f1,${prefix}r) && ${prefix}f2 subset ${prefix}f1 ==>
         |        filterReceiverGood(${prefix}f1,${prefix}r) &&
         |          ${prefix}f2 subset ${prefix}f1 && filterReceiverGood(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom smallerFDelete {
         |        forall ${prefix}f1: Set[$compDTV0], ${prefix}f2: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0] ::
         |        {filterReceiverGood(${prefix}f1,${prefix}r), ${prefix}f1 setminus ${prefix}f2}
         |        filterReceiverGood(${prefix}f1,${prefix}r) ==> filterReceiverGood(${prefix}f1,${prefix}r) &&
         |        filterReceiverGood(${prefix}f1 setminus ${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom unionF {
         |        forall ${prefix}f1: Set[$compDTV0], ${prefix}f2: Set[$compDTV0], ${prefix}r:$recDKey[$compDTV0] ::
         |        {filterReceiverGood(${prefix}f1 union ${prefix}f2,${prefix}r)}
         |        filterReceiverGood(${prefix}f1 union ${prefix}f2,${prefix}r) ==>
         |        filterReceiverGood(${prefix}f1 union ${prefix}f2,${prefix}r) &&
         |        filterReceiverGood(${prefix}f1,${prefix}r) && filterReceiverGood(${prefix}f2,${prefix}r)
         |    }
         |
         |    axiom _filterNotLostAxiom {
         |        forall ${prefix}a: $compDTV0, ${prefix}fs: Set[$compDTV0], ${prefix}r: $recDKey[$compDTV0],
         |          ${prefix}lostR: Set[Ref] ::
         |        {${prefix}a in filterNotLost(${prefix}fs, ${prefix}r, ${prefix}lostR)}
         |            ${prefix}a in filterNotLost(${prefix}fs, ${prefix}r, ${prefix}lostR) <==>
         |                (${prefix}a in ${prefix}fs && !($recApplyKey(${prefix}r, ${prefix}a) in ${prefix}lostR))
         |    }
         |
         |    axiom _filterNotLostSubset {
         |        forall ${prefix}fs: Set[$compDTV0], ${prefix}r: $recDKey[$compDTV0], ${prefix}lostR: Set[Ref] ::
         |          {filterNotLost(${prefix}fs, ${prefix}r, ${prefix}lostR)}
         |        filterNotLost(${prefix}fs, ${prefix}r, ${prefix}lostR) subset ${prefix}fs
         |    }
         |
         |
         |}\n """.stripMargin
    receiverOut
  }

  def mappingDomainString(): String = {
    val mappingOut =
      s"""domain $mapDKey[$compDTV1,$compDTV2] {
         |
         |    function $mapApplyKey(m: $mapDKey[$compDTV1,$compDTV2], _mInput:$compDTV1) : $compDTV2
         |
         |    function $mapIdenKey() : $mapDKey[$compDTV1,$compDTV1]
         |
         |    axiom {
         |      forall __v: $compDTV1 :: {$mapApplyKey($mapIdenKey() ,__v)}
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
         |
         |    function $opApplyKey(op: $opDKey[$compDTV2], val1:$compDTV2, val2:$compDTV2) : $compDTV2
         |
         |    function $opIdenKey(op: $opDKey[$compDTV2]) : $compDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    opOut
  }

  def compDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val compOut =
      s"""domain $compDKey[$compDTV0,$compDTV1,$compDTV2] {
         |
         |    function $compConstructKey(r:$recDKey[$compDTV0], m: $mapDKey[$compDTV1,$compDTV2],
         |        op: $opDKey[$compDTV2]) : $compDKey[$compDTV0,$compDTV1,$compDTV2]
         |
         |    function $compApplyKey(c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |        snap: Map[$compDTV0,$compDTV2]) : $compDTV2
         |
         |    function $compApplyPrimeKey(c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |        snap: Map[$compDTV0,$compDTV2]) : $compDTV2
         |
         |
         |    axiom applyComp1Eq {
         |        forall
         |        ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |        ${prefix}snap: Map[$compDTV0,$compDTV2] ::
         |        {$compApplyKey(${prefix}c, ${prefix}snap)}
         |        $compApplyKey(${prefix}c, ${prefix}snap) == $compApplyPrimeKey(${prefix}c,${prefix}snap)
         |    }
         |
         |
         |    function getreceiver(c:$compDKey[$compDTV0,$compDTV1,$compDTV2]): $recDKey[$compDTV0]
         |    function getoperator(c:$compDKey[$compDTV0,$compDTV1,$compDTV2]): $opDKey[$compDTV2]
         |    function getmapping(c:$compDKey[$compDTV0,$compDTV1,$compDTV2]): $mapDKey[$compDTV1,$compDTV2]
         |
         |    function dummy1(a:$compDTV2): Bool
         |    function _triggerDeleteBlock(applyC: $compDTV2, block: Set[$compDTV0]): Bool
         |    function _triggerDeleteKey1(applyC: $compDTV2, key: $compDTV0): Bool
         |
         |    function exhaleCompMap(c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |                           m: Map[$compDTV0, $compDTV2],
         |                           fieldID: Int): Bool
         |
         |    function getSnapFieldID(m: Map[$compDTV0, $compDTV2]): Int
         |
         |    axiom _invAxFold {
         |      forall
         |        ${prefix}r: $recDKey[$compDTV0],
         |        ${prefix}m: $mapDKey[$compDTV1,$compDTV2],
         |        ${prefix}o: $opDKey[$compDTV2]
         |        :: {$compConstructKey(${prefix}r,${prefix}m,${prefix}o)}
         |        getreceiver($compConstructKey(${prefix}r,${prefix}m,${prefix}o)) == ${prefix}r &&
         |        getmapping($compConstructKey(${prefix}r,${prefix}m,${prefix}o)) == ${prefix}m &&
         |        getoperator($compConstructKey(${prefix}r,${prefix}m,${prefix}o)) == ${prefix}o
         |    }
         |
         |    axiom _emptyFold {
         |        forall ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}snap: Map[$compDTV0, $compDTV2] ::
         |        {$compApplyKey(${prefix}c, ${prefix}snap)}
         |            domain(${prefix}snap) == Set() ==>  domain(${prefix}snap) == Set() &&
         |                $compApplyKey(${prefix}c, ${prefix}snap) == $opIdenKey(getoperator(${prefix}c))
         |    }
         |
         |    axiom _singleton {
         |        forall ${prefix}c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}snap: Map[$compDTV0, $compDTV2],
         |               ${prefix}elem: $compDTV0 ::
         |        {$compApplyKey(${prefix}c, ${prefix}snap), Set(${prefix}elem)}
         |            domain(${prefix}snap) == Set(${prefix}elem) ==>
         |            domain(${prefix}snap) == Set(${prefix}elem) &&
         |                $compApplyKey(${prefix}c, ${prefix}snap) == ${prefix}snap[${prefix}elem]
         |    }
         |
         |    axiom _dropOne1 {
         |        forall ${prefix}c:$compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}snap1: Map[$compDTV0, $compDTV2],
         |               ${prefix}key: $compDTV0 ::
         |        {_triggerDeleteKey1($compApplyKey(${prefix}c,${prefix}snap1),${prefix}key)}
         |            (${prefix}key in domain(${prefix}snap1)) ==>
         |            (${prefix}key in domain(${prefix}snap1))  &&
         |               $compApplyKey(${prefix}c,${prefix}snap1) ==
         |               $opApplyKey(getoperator(${prefix}c),
         |                $compApplyPrimeKey(${prefix}c,
         |                mapDelete(${prefix}snap1, Set(${prefix}key))), ${prefix}snap1[${prefix}key])
         |    }
         |
         |    axiom loseMany {
         |        forall ${prefix}c:$compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               ${prefix}snap1:Map[$compDTV0, $compDTV2],
         |               ${prefix}keys: Set[$compDTV0] ::
         |        {_triggerDeleteBlock($compApplyKey(${prefix}c,${prefix}snap1),${prefix}keys)}
         |            (${prefix}keys subset domain(${prefix}snap1)) ==>
         |            (${prefix}keys subset domain(${prefix}snap1)) &&
         |               $compApplyKey(${prefix}c,${prefix}snap1) == $opApplyKey(getoperator(${prefix}c),
         |                    $compApplyPrimeKey(${prefix}c,mapDelete(${prefix}snap1, ${prefix}keys)),
         |                    $compApplyPrimeKey(${prefix}c,mapSubmap(${prefix}snap1, ${prefix}keys)))
         |    }
         |
         |
         |
         |
         |
         |
         |
         |}\n """.stripMargin
    compOut
  }

  def setFuncDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val setOut =
      s"""domain setFunc[A] {
         |
         |    axiom setminusAssoc {
         |        forall ${prefix}s1: Set[A], ${prefix}s2: Set[A], ${prefix}s3: Set[A] ::
         |        {(${prefix}s1 setminus ${prefix}s2) setminus ${prefix}s3}
         |            (${prefix}s1 setminus ${prefix}s2) setminus ${prefix}s3 ==
         |            (${prefix}s1 setminus ${prefix}s3) setminus ${prefix}s2
         |    }
         |
         |    axiom setminusRepeated {
         |        forall ${prefix}s1: Set[A], ${prefix}s2: Set[A] ::
         |        {(${prefix}s1 setminus ${prefix}s2) setminus ${prefix}s2}
         |            (${prefix}s1 setminus ${prefix}s2) setminus ${prefix}s2 == (${prefix}s1 setminus ${prefix}s2)
         |    }
         |
         |    axiom _emptySubset {
         |        forall ${prefix}s1: Set[A], ${prefix}s2: Set[A] :: {${prefix}s2 subset ${prefix}s1}
         |            (${prefix}s1 == Set()) ==>  ((${prefix}s2 subset ${prefix}s1) <==> ${prefix}s2 == Set())
         |    }
         |}
         |
         |
         |
         |\n """.stripMargin
    setOut
  }

  def mapCustomDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val mapCustomOut =
      s"""domain MapEdit[$compDTV0,$compDTV2] {
         |    function mapDelete(m: Map[$compDTV0,$compDTV2], e: Set[$compDTV0]): Map[$compDTV0,$compDTV2]
         |    function mapSubmap(m: Map[$compDTV0,$compDTV2], es: Set[$compDTV0]): Map[$compDTV0,$compDTV2]
         |
         |    function $disjUnionKey(s1: Set[$compDTV0], s2: Set[$compDTV0], s3: Set[$compDTV0]) : Bool
         |    axiom disjUnionEqDef {
         |        forall ${prefix}s1: Set[$compDTV0], ${prefix}s2: Set[$compDTV0], ${prefix}s3: Set[$compDTV0] ::
         |        {$disjUnionKey(${prefix}s1,${prefix}s2,${prefix}s3)}
         |        $disjUnionKey(${prefix}s1,${prefix}s2,${prefix}s3) <==>
         |        ${prefix}s1 intersection ${prefix}s2 == Set() && ${prefix}s1 union ${prefix}s2  == ${prefix}s3
         |    }
         |
         |}\n """.stripMargin
    mapCustomOut
  }

//  def dummyDomainString(): String = {
//    val axioms: Seq[String] = Seq()
//    val dummyOut =
//      s"""domain Dummy {
//         |    function dummy() : Bool
//         |
//         |    ${axioms.mkString("\n")}
//         |}\n """.stripMargin
//    dummyOut
//  }


  def parseDomainString(input: String): PDomain = {
    val fp = new DummyParser();
    fp._line_offset = Array();
    fastparse.parse(input, fp.domainDecl(_)) match {
      case Parsed.Success(newDomain, index) =>
        changePosRecursive(newDomain,
          (FilePosition(null, 0, 0), FilePosition(null, 0, 0))).asInstanceOf[PDomain]
//          (VirtualPosition(s"Generated ${newDomain.idndef.name} domain start"),
//          VirtualPosition(s"Generated ${newDomain.idndef.name} domain end"))).asInstanceOf[PDomain]
      case fail: Parsed.Failure =>
        // This should not happen
        val trace = fail.trace()
        val fullStack = fastparse.Parsed.Failure.formatStack(trace.input, trace.stack)
        val msg = s"${trace.aggregateMsg}. Occurred while parsing: $fullStack"
//        val (line, col) = lineCol.getPos(trace.index)
//        val pos = FilePosition(_file, line, col)
        throw ParseException(msg, (NoPosition, NoPosition))
    }
  }



  // Copied from MacroExpander.scala
  def changePosRecursive(body: PNode, pos: (Position, Position)): PNode = {
    val children = body.children.map { child => if (child.isInstanceOf[PNode]) changePosRecursive(child.asInstanceOf[PNode], pos) else child }
    body.withChildren(children, Some(pos))
  }

}
