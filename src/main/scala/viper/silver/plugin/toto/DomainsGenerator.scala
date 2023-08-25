package viper.silver.plugin.toto

import fastparse.{P, Parsed}
import viper.silver.ast.{NoPosition, Position, VirtualPosition}
import viper.silver.parser.{FastParser, FastParserCompanion, PDomain, PNode, ParseException}


object DomainsGenerator {
  final val compDKey = "Comp"
  final val compDTV0 = "A"
  final val compDTV1 = "V"
  final val compDTV2 = "B"


  final val compFKey = "comp"
  final val compEvalKey = "evalComp"
  final val recEvalKey = "eval"
  final val opEvalKey = "operApply"
  final val opUnitKey = "operGetUnit"
  final val mapEvalKey = "applyMap"

  final val recDKey = "Receiver"
  final val mapDKey = "Mapping"
  final val opDKey = "Operator"

  def receiverDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val receiverOut =
      s"""domain $recDKey[$compDTV0] {
         |    function $recEvalKey(r:$recDKey[$compDTV0], a:$compDTV0) : Ref
         |    function invers$recEvalKey(rec:$recDKey[$compDTV0], ref:Ref) : $compDTV0
         |    function filterReceiverGood(f: Set[$compDTV0], r: $recDKey[$compDTV0]) : Bool
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    receiverOut
  }

  def mappingDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val mappingOut =
      s"""domain $mapDKey[$compDTV1,$compDTV2] {
         |    function $mapEvalKey(m: $mapDKey[$compDTV1,$compDTV2], _mInput:$compDTV1) : $compDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    mappingOut
  }

  def opDomainString(): String = {
    val axioms: Seq[String] = Seq()
    val opOut =
      s"""domain $opDKey[$compDTV2] {
         |    function $opEvalKey(op: $opDKey[$compDTV2], val1:$compDTV2, val2:$compDTV2) : $compDTV2
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
         |    function $compFKey(r:$recDKey[$compDTV0], m: $mapDKey[$compDTV1,$compDTV2],
         |        op: $opDKey[$compDTV2],u: $compDTV2) : $compDKey[$compDTV0,$compDTV1,$compDTV2]
         |    function $compEvalKey(c: $compDKey[$compDTV0,$compDTV1,$compDTV2],
         |        snap: Map[$compDTV0,$compDTV2]) : $compDTV2
         |
         |    ${axioms.mkString("\n")}
         |}\n """.stripMargin
    compOut
  }


  def parseDomainString(input: String): PDomain = {
    val fp = new DummyParser();
    fp._line_offset = Array();
    fastparse.parse(input, fp.domainDecl(_)) match {
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
