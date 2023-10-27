package viper.silver.plugin.toto

import fastparse.Parsed
import viper.silver.ast.{NoPosition, Position, VirtualPosition}
import viper.silver.parser.{PDomain, PNode, ParseException}


object DomainsGenerator {
  final val compDKey = "Comp"
  final val compDTV0 = "A"
  final val compDTV1 = "V"
  final val compDTV2 = "B"


  final val compConstructKey = "comp"
  final val compApplyKey = "compApply"
  final val compApplyPrimeKey = "compApply1"
  final val recApplyKey = "recApply"
  final val recInvKey = "recInv"
  final val opApplyKey = "opApply"
  final val opUnitKey = "opGetUnit"
  final val mapApplyKey = "mapApply"
  final val mapIdenKey = "mapIdentity"
  final val disjUnionKey = "disjUnionEq"

  final val recDKey = "Receiver"
  final val mapDKey = "Mapping"
  final val opDKey = "Operator"

  def receiverDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val receiverOut =
      s"""domain $recDKey[$compDTV0] {
         |    function $recApplyKey(r:$recDKey[$compDTV0], a:$compDTV0) : Ref
         |    function $recInvKey(rec:$recDKey[$compDTV0], ref:Ref) : $compDTV0
         |    function filterReceiverGood(f: Set[$compDTV0], r: $recDKey[$compDTV0]) : Bool
         |
         |    function filterNotLost(f1: Set[$compDTV0], r: $recDKey[$compDTV0], lostR: Set[Ref]): Set[$compDTV0]
         |
         |    axiom _inverse_receiver {
         |        forall a : $compDTV0, f: Set[$compDTV0], r: $recDKey[$compDTV0]
         |        :: {$recApplyKey(r,a), filterReceiverGood(f,r)} // {filterReceiverGood(f,r), a in f}
         |        filterReceiverGood(f,r) && a in f ==> filterReceiverGood(f,r) &&
         |        a in f && $recInvKey(r,$recApplyKey(r,a)) == a
         |    }
         |
         |    axiom _inverse_receiver1 {
         |        forall ref: Ref, f: Set[$compDTV0], r:$recDKey[$compDTV0]
         |        ::{filterReceiverGood(f,r), $recInvKey(r,ref)}
         |        filterReceiverGood(f,r) && $recInvKey(r,ref) in f ==>
         |        filterReceiverGood(f,r) && $recInvKey(r,ref) in f && $recApplyKey(r,$recInvKey(r,ref)) == ref
         |    }
         |
         |    axiom smallerF {
         |        forall f1: Set[$compDTV0], f2: Set[$compDTV0], r:$recDKey[$compDTV0] ::
         |        {f2 subset f1, filterReceiverGood(f1,r)}
         |        filterReceiverGood(f1,r) && f2 subset f1 ==>
         |        filterReceiverGood(f1,r) && f2 subset f1 && filterReceiverGood(f2,r)
         |    }
         |
         |    axiom smallerFDelete {
         |        forall f1: Set[$compDTV0], f2: Set[$compDTV0], r:$recDKey[$compDTV0] ::
         |        {filterReceiverGood(f1,r), f1 setminus f2}
         |        filterReceiverGood(f1,r) ==> filterReceiverGood(f1,r) && filterReceiverGood(f1 setminus f2,r)
         |    }
         |
         |    axiom unionF {
         |        forall f1: Set[$compDTV0], f2: Set[$compDTV0], r:$recDKey[$compDTV0] ::
         |        {filterReceiverGood(f1 union f2,r)}
         |        filterReceiverGood(f1 union f2,r) ==>
         |        filterReceiverGood(f1 union f2,r) &&  filterReceiverGood(f1,r) && filterReceiverGood(f2,r)
         |    }
         |
         |    axiom _filterNotLostAxiom {
         |        forall a: $compDTV0, fs: Set[$compDTV0], r: $recDKey[$compDTV0], lostR: Set[Ref] ::
         |        {a in filterNotLost(fs, r, lostR)}
         |            a in filterNotLost(fs, r, lostR) <==>
         |                (a in fs && !($recApplyKey(r, a) in lostR))
         |    }
         |
         |    axiom _filterNotLostSubset {
         |        forall fs: Set[$compDTV0], r: $recDKey[$compDTV0], lostR: Set[Ref] :: {filterNotLost(fs, r, lostR)}
         |        filterNotLost(fs, r, lostR) subset fs
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
         |    function $opApplyKey(op: $opDKey[$compDTV2], val1:$compDTV2, val2:$compDTV2) : $compDTV2
         |
         |    function $opUnitKey(op: $opDKey[$compDTV2]) : $compDTV2
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
         |        forall c: $compDKey[$compDTV0,$compDTV1,$compDTV2], snap: Map[$compDTV0,$compDTV2] ::
         |        {$compApplyKey(c, snap)}
         |        $compApplyKey(c, snap) == $compApplyPrimeKey(c,snap)
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
         |
         |
         |    axiom _singleton {
         |        forall c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               snap: Map[$compDTV0, $compDTV2], elem: $compDTV0 ::
         |        {$compApplyKey(c, snap), Set(elem)}
         |            domain(snap) == Set(elem) ==>  domain(snap) == Set(elem) &&
         |                $compApplyKey(c, snap) == snap[elem]
         |    }
         |
         |    axiom _dropOne1 {
         |        forall c:$compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               snap1: Map[$compDTV0, $compDTV2], key: $compDTV0 ::
         |        {_triggerDeleteKey1($compApplyKey(c,snap1),Set(key))}
         |            (key in domain(snap1)) ==>  (key in domain(snap1))  &&
         |               $compApplyKey(c,snap1) ==
         |               $opApplyKey(getoperator(c),$compApplyPrimeKey(c,
         |                                            mapDelete(snap1, Set(key))), snap1[key])
         |    }
         |
         |    axiom loseMany {
         |        forall c:$compDKey[$compDTV0,$compDTV1,$compDTV2],
         |               snap1:Map[$compDTV0, $compDTV2], keys: Set[$compDTV0] ::
         |        {_triggerDeleteBlock($compApplyKey(c,snap1),keys)}
         |            (keys subset domain(snap1)) ==>  (keys subset domain(snap1)) &&
         |               $compApplyKey(c,snap1) == $opApplyKey(getoperator(c),
         |                    $compApplyPrimeKey(c,mapDelete(snap1, keys)),
         |                    $compApplyPrimeKey(c,mapSubmap(snap1,keys)))
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

  def mapCustomDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val mapCustomOut =
      s"""domain MapEdit[$compDTV0,$compDTV2] {
         |    function mapDelete(m: Map[$compDTV0,$compDTV2], e: Set[$compDTV0]): Map[$compDTV0,$compDTV2]
         |    function mapSubmap(m: Map[$compDTV0,$compDTV2], es: Set[$compDTV0]): Map[$compDTV0,$compDTV2]
         |
         |    function $disjUnionKey(s1: Set[$compDTV0], s2: Set[$compDTV0], s3: Set[$compDTV0]) : Bool
         |    axiom disjUnionEqDef {
         |        forall s1: Set[$compDTV0], s2: Set[$compDTV0], s3: Set[$compDTV0] :: {$disjUnionKey(s1,s2,s3)}
         |        $disjUnionKey(s1,s2,s3) <==>  s1 intersection s2 == Set() && s1 union s2  == s3
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
    fastparse.parse[PDomain](input, fp.domainDecl(_)) match {
      case Parsed.Success(newDomain, index) =>
        changePosRecursive(newDomain,
          (VirtualPosition(s"Generated ${newDomain.idndef.name} domain start"),
          VirtualPosition(s"Generated ${newDomain.idndef.name} domain end"))).asInstanceOf[PDomain]
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
