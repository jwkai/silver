// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.utility.Expressions
import viper.silver.ast.{DomainFuncApp, DomainType, Exp, ExtensionExp, Forall, IntLit, LocalVar, LocalVarAssign, NamedDomainAxiom, Program, Ref, SetType, TypeVar}
import viper.silver.frontend.{SilFrontend, SilFrontendConfig}
import viper.silver.parser.FastParser
import viper.silver.plugin.SilverPluginManager
import viper.silver.plugin.crimp.{DecompDepth, DomainsGenerator}
import viper.silver.plugin.crimp.ast.{CrHeap, CrHeapMap, CrimpApp, CrimpTripleWithId, CrimpTripleWithoutId, HeapKey}
import viper.silver.plugin.crimp.util.AxiomHelper
import viper.silver.reporter.{NoopReporter, Reporter, StdIOReporter}
import viper.silver.verifier._

import java.nio.file.Paths

class CrimpTests extends AnyFunSuite {
  // Inputs the frontend (parsing, resolution/type checking, translation, consistency check) must accept.
  val inputfiles: Seq[String] = Seq(
    "crimp/arraySwap.vpr",
    "crimp/arraySwapMax.vpr",
    "crimp/arraySum-i1.vpr",
    "crimp/generic-filter.vpr",
    "crimp/component-decl-forward-ref.vpr",
    "crimp/user-import.vpr",
    "crimp/two-fields.vpr",
    "crimp/footprints.vpr",
  )
  // Inputs the frontend must reject with exactly these errors, in particular without an additional internal error.
  val badInputfiles: Seq[(String, Seq[String])] = Seq(
    "crimp/bad/operator-arity.vpr" -> Seq("Operator body should have exactly two arguments."),
    "crimp/bad/mapping-arity.vpr" -> Seq("Mapping body should have exactly one argument."),
    "crimp/bad/component-body-crimp.vpr" -> Seq("Crimp outside a method is not supported. (component-body-crimp.vpr@25."),
    "crimp/bad/recursive-mapping.vpr" -> Seq(recursive("rec", "recursive-mapping.vpr@25.")),
    "crimp/bad/recursive-mutual.vpr" -> Seq(recursive("ping", "recursive-mutual.vpr@27.")),
    "crimp/bad/recursive-operator-unit.vpr" -> Seq(recursive("addU", "recursive-operator-unit.vpr@26.")),
    "crimp/bad/unfolding-component.vpr" -> unfolding("unfolding-component.vpr@25.20"),
    "crimp/bad/call-arity.vpr" ->
      Seq("wrong number of arguments (call-arity.vpr@26.", "wrong number of arguments (call-arity.vpr@29.")
  )
  def unfolding(at: String): Seq[String] = Seq(s"specified location is not a field nor a predicate ($at",
    s"expected predicate access ($at", s"found incompatible type `<impure>`, expected `<predicate>` ($at")
  def recursive(component: String, at: String): String = s"Recursive use of crimp component `$component` ($at"
  val plugins: Seq[String] = Seq(
//    "TestPluginAllCalled",
    "viper.silver.plugin.crimp.CrimpPlugin"
  )

  var result: VerificationResult = Success

  def runFrontend(plugin: String, inputfile: String): MockPluginFrontend = {
    val resource = getClass.getResource(inputfile)
    assert(resource != null, s"File $inputfile not found")
    val file = Paths.get(resource.toURI)
    val frontend = new MockPluginFrontend
    val instance = SilverPluginManager.resolve(plugin, NoopReporter, null, null,new FastParser())
    assert(instance.isDefined)
    result = instance.get match {
      case p: FakeResult => p.result()
      case _ => Success
    }
    frontend.execute(Seq("--plugin", plugin, file.toString))
    frontend
  }

  def testOne(plugin: String, inputfile: String): Unit = {
    val frontend = runFrontend(plugin, inputfile)
    // The frontend must accept the input; otherwise e.g. a type-checker error in the plugin would go unnoticed.
    assert(frontend.errors.isEmpty,
      s"$inputfile: frontend reported errors:\n" + frontend.errors.map(_.readableMessage).mkString("\n"))
    assert(frontend.plugins.plugins.size == 1 + frontend.defaultPluginCount)
    // Every crimp is lowered before verification: no CrimpApp or CrimpTriple (ExtensionExp) reaches the verifier.
    val unlowered = frontend.program.toSeq.flatMap(_.deepCollect { case e: ExtensionExp => e.getClass.getSimpleName })
    assert(unlowered.isEmpty, s"$inputfile: not lowered before verification: ${unlowered.mkString(", ")}")
    frontend.plugins.plugins.foreach {
      case p: TestPlugin => assert(p.test(), p.getClass.getName)
      case _ =>
    }
  }

  def testBad(plugin: String, inputfile: String, expected: Seq[String]): Unit = {
    val messages = runFrontend(plugin, inputfile).errors.map(_.readableMessage)
    val report = s"$inputfile: frontend reported:\n" + messages.mkString("\n")
    assert(messages.size == expected.size, report)
    expected.foreach(e => assert(messages.exists(_.contains(e)), s"missing `$e`; " + report))
    assert(!messages.exists(_.contains("internal error")), report)
  }

  for (p <- plugins; f <- inputfiles) test(s"$p $f")(testOne(p, f))
  for (p <- plugins; (f, expected) <- badInputfiles) test(s"$p $f (rejected)")(testBad(p, f, expected))

  test("CrimpPlugin: only an operator with an identity element uses the with-identity encoding") {
    val frontend = runFrontend("viper.silver.plugin.crimp.CrimpPlugin", "crimp/arraySwapMax.vpr")
    assert(frontend.errors.isEmpty, frontend.errors.map(_.readableMessage).mkString("\n"))
    // arraySwapMax.vpr uses msSum (unit Multiset[Int]()) and maxOp (no unit). Only strings are compared and reported.
    val withId = classOf[CrimpTripleWithId].getSimpleName
    val withoutId = classOf[CrimpTripleWithoutId].getSimpleName
    val encodings: Seq[(String, String)] = frontend.translatedProgram.get.deepCollect {
      case c: CrimpApp =>
        val op = c.reduction.op match {
          case d: DomainFuncApp => d.funcname
          case o => o.getClass.getSimpleName
        }
        op -> c.reduction.getClass.getSimpleName
    }
    val ops = encodings.map(_._1).toSet
    assert(ops.contains("msSum") && ops.contains("maxOp"), s"operators found: ${ops.mkString(", ")}")
    val wrong = encodings.filter {
      case ("msSum", enc) => enc != withId
      case ("maxOp", enc) => enc != withoutId
      case _ => false
    }.map { case (op, enc) => s"$op: $enc" }
    assert(wrong.isEmpty, s"wrong encodings: ${wrong.mkString(", ")}")
  }

  test("CrimpPlugin: the imported crimp domains declare every name the crimp code looks up") {
    // arraySwapMax.vpr uses operators with and without a unit, so crimp.vpr, crimpM.vpr and crimpS.vpr are imported
      val frontend = runFrontend("viper.silver.plugin.crimp.CrimpPlugin", "crimp/arraySwapMax.vpr")
      assert(frontend.errors.isEmpty, frontend.errors.map(_.readableMessage).mkString("\n"))
      val p = frontend.translatedProgram.get
      import viper.silver.plugin.crimp.DomainsGenerator._
      val domainOf: Seq[(String, String)] =
        Seq(crimpConstructKeyM, crimpApplyKeyM, crimpApplyDummyKeyM, setEqDummyKeyM, crimpGetRecvKeyM, crimpGetOperKeyM,
            crimpGetMappingKeyM, crHeapElemKeyM, trigDelKey1KeyM, trigDelBlockKeyM, getFieldIDKeyM, skExtKeyM,
            trigExtKeyM).map(_ -> crimpDKeyM) ++
        Seq(crimpConstructKeyS, crimpApplyKeyS, crimpApplyDummyKeyS, setEqDummyKeyS, crimpGetRecvKeyS, crimpGetOperKeyS,
            crimpGetMappingKeyS, crHeapElemKeyS, trigDelKey1KeyS, trigDelBlockKeyS, getFieldIDKeyS, skExtKeyS,
            trigExtKeyS).map(_ -> crimpDKeyS) ++
        Seq(fuelSKey, fuelZKey).map(_ -> fuelDKey) ++
        Seq(recApplyKey, filterRecvGoodKey, preimgElemKey, subsetNotInRefsKey,
          idxNotInRefsKey).map(_ -> recDKey) ++
        Seq(opApplyKey, opIdenKey).map(_ -> opDKey) ++
        Seq(mapApplyKey, mapIdenKey).map(_ -> mapDKey) ++
        Seq(setDeleteKey, disjUnionKey).map(_ -> "SetEdit") ++
        Seq(extLinkKey).map(_ -> extLinkDKey)
      val declared: Map[String, String] = p.domains.flatMap(d => d.functions.map(_.name -> d.name)).toMap
      val wrong = domainOf.filterNot { case (f, d) => declared.get(f).contains(d) }
        .map { case (f, d) => s"$f (expected in $d, found in ${declared.getOrElse(f, "no domain")})" }
      assert(wrong.isEmpty, s"names not declared as expected: ${wrong.mkString(", ")}")

    // The translation term builders must find their domain and functions, and build applications that match the
    // declarations (arity, argument and result types).
    val fuel = new AxiomHelper(p, 2).fuelDefaultExp
    val apps = p.deepCollect { case c: CrimpApp => c }
    val n = apps.size
    assert(n == 4, "arraySwapMax.vpr has four crimp terms")
    val bad = apps.flatMap { c =>
      c.toViper(p, fuel, CrHeap(0)) match {
        case t @ DomainFuncApp(evalName, Seq(_, _, cons: DomainFuncApp, _), _)
          if evalName == c.reduction.crimpEvalFuncName() && cons.funcname == c.reduction.crimpConstructKeyName() &&
            conforms(p, t) && conforms(p, cons) => None
        case t => Some(t.toString)
      }
    }
    assert(bad.isEmpty, s"ill-formed crimp terms: ${bad.mkString("; ")}")
    // The link term of two crimp-heap indices (extensionality trigger).
    val link = new AxiomHelper(p, 2).extLinkApply(IntLit(0)(), IntLit(1)())
    assert(link.typ == viper.silver.ast.Bool && conforms(p, link), s"ill-formed link term: $link")
  }

  test("CrimpApp.toViper: crimps over different fields differ only in the field identifier") {
    // two-fields.vpr declares the fields w, v, vv (field identifiers 0, 1, 2) and applies an operator with a unit
    // (crimpM) and one without (crimpS) to arrayRec(a).v and to arrayRec(a).vv.
    val frontend = runFrontend("viper.silver.plugin.crimp.CrimpPlugin", "crimp/two-fields.vpr")
    assert(frontend.errors.isEmpty, frontend.errors.map(_.readableMessage).mkString("\n"))
    val p = frontend.translatedProgram.get
    val helper = new AxiomHelper(p, 2)
    val fuel = helper.fuelDefaultExp
    val fid = Map("w" -> 0, "v" -> 1, "vv" -> 2)
    assert(fid.forall { case (f, i) => AxiomHelper.fieldID(p, f) == i }, "fieldID is the position in program.fields")
    val apps = p.deepCollect { case c: CrimpApp => c }
    val n = apps.size
    assert(n == 4, "two-fields.vpr has four crimp terms")

    // Only strings and Booleans are compared and reported (see above).
    val problems = apps.flatMap { c =>
      val hasID = c.reduction.isInstanceOf[CrimpTripleWithId]
      val t = c.toViper(p, fuel, CrHeap(3)).asInstanceOf[DomainFuncApp]
      val t2 = c.toViper(p, fuel, CrHeap(4)).asInstanceOf[DomainFuncApp]
      val guard = helper.fieldIDGuard(t.args(2), c.fieldName)(hasID)
      val checks: Seq[(Boolean, String)] = t match {
        case DomainFuncApp(_, Seq(_, IntLit(ch), cons: DomainFuncApp, _), _) => Seq(
          (ch == 3, "crimp-heap index argument"),
          (cons.args.size == 4 && cons.args(3) == IntLit(fid(c.fieldName))(), "fid argument"),
          (conforms(p, t) && conforms(p, cons), "matches the declarations"),
          // toViper is pure: another index changes only the index argument, and the node keeps no state
          (t2.args.updated(1, IntLit(3)()) == t.args && c.toViper(p, fuel, CrHeap(3)) == t, "pure"),
          (guard.left match {
            case g: DomainFuncApp => g.funcname == (if (hasID) DomainsGenerator.getFieldIDKeyM
              else DomainsGenerator.getFieldIDKeyS) && g.args == Seq(cons) && conforms(p, g)
            case _ => false
          }, "getFieldID guard"),
          (guard.right == IntLit(fid(c.fieldName))(), "guard literal"),
          (c.heapKey == HeapKey(c.reduction.receiver, c.fieldName), "heap key"))
        case _ => Seq((false, "shape"))
      }
      checks.collect { case (false, what) => s"${c.fieldName}/${if (hasID) "M" else "S"}: $what" }
    }
    assert(problems.isEmpty, problems.mkString(", "))

    // Per encoding, the v and vv terms are equal except for the fid argument of the constructor.
    val byEncoding = apps.groupBy(_.reduction.isInstanceOf[CrimpTripleWithId]).values.toSeq
    val pairsDiffer = byEncoding.map { cs =>
      val Seq(v, vv) = cs.sortBy(_.fieldName).map(_.toViper(p, fuel, CrHeap(0)).asInstanceOf[DomainFuncApp])
      val (cv, cvv) = (v.args(2).asInstanceOf[DomainFuncApp], vv.args(2).asInstanceOf[DomainFuncApp])
      cv.args.init == cvv.args.init && cv.args.last != cvv.args.last &&
        v.args.updated(2, cvv) == vv.args
    }
    assert(byEncoding.size == 2 && pairsDiffer.forall(identity), "the v and vv terms differ only in the fid")

    // Heap keys: receiver instance plus field; the M and S terms over one field share a key.
    val keys = apps.map(_.heapKey).toSet
    val initial = CrHeapMap.of(keys, CrHeap(0))
    val shown = initial.toString
    assert(keys.size == 2 && initial.fields == Set("v", "vv") && shown == "v:0 vv:0", shown)
    val advanced = initial.withField("v", CrHeap(1))
    val advancedShown = advanced.toString
    assert(advanced.ofField("v") == CrHeap(1) && advanced.ofField("vv") == CrHeap(0) &&
      apps.forall(c => advanced(c.heapKey) == (if (c.fieldName == "v") CrHeap(1) else CrHeap(0))), advancedShown)
    // A receiver instance that is not in the map has the index of its field (lockstep); keys over one field at
    // different indices are an internal error. `b` stands in for another receiver instance.
    val other = HeapKey(LocalVar("b", Ref)(), "v")
    assert(advanced(other) == CrHeap(1), advancedShown)
    intercept[IllegalStateException](CrHeapMap(advanced.m + (other -> CrHeap(2))).ofField("v"))
  }

  test("CrimpPlugin: the extensionality witness depends on the two indices and the filter") {
    // arraySwapMax.vpr imports crimpM.vpr and crimpS.vpr.
    val frontend = runFrontend("viper.silver.plugin.crimp.CrimpPlugin", "crimp/arraySwapMax.vpr")
    assert(frontend.errors.isEmpty, frontend.errors.map(_.readableMessage).mkString("\n"))
    val p = frontend.translatedProgram.get
    import DomainsGenerator._
    val encodings = Seq((crimpDKeyM, skExtKeyM, extensionalityAxiomM), (crimpDKeyS, skExtKeyS, extensionalityAxiomS))
    val wrong = encodings.flatMap { case (dn, sk, ax) =>
      val d = p.domains.find(_.name == dn).get
      val f = d.functions.find(_.name == sk).get
      val sig = f.formalArgs.map(_.typ) match {
        case Seq(c: DomainType, viper.silver.ast.Int, viper.silver.ast.Int, SetType(_: TypeVar)) => c.domainName == dn
        case _ => false
      }
      val q = d.axioms.collectFirst { case a: NamedDomainAxiom if a.name == ax => a }.get.exp.asInstanceOf[Forall]
      val byName = q.variables.map(v => v.name -> v.localVar).toMap
      val expected = Seq("c", "crh_old", "crh_new", "fs").map(n => byName(s"__crimp_$n"))
      val apps = q.deepCollect { case a: DomainFuncApp if a.funcname == sk => a.args }
      (if (sig) Seq() else Seq(s"$sk(${f.formalArgs.map(_.typ).mkString(", ")})")) ++
        (if (apps.nonEmpty && apps.forall(_ == expected)) Seq() else Seq(s"$ax applies $sk to ${apps.map(_.mkString(", ")).distinct}"))
    }
    assert(wrong.isEmpty, wrong.mkString("; "))
  }

  test("CrimpPlugin: index footprints are preimages; the imported receiver domain has no receiver inverse") {
    // two-fields.vpr imports crimp.vpr, crimpM.vpr and crimpS.vpr.
    val frontend = runFrontend("viper.silver.plugin.crimp.CrimpPlugin", "crimp/two-fields.vpr")
    assert(frontend.errors.isEmpty, frontend.errors.map(_.readableMessage).mkString("\n"))
    val p = frontend.translatedProgram.get
    import DomainsGenerator._
    val recv = p.domains.find(_.name == recDKey).get
    // No global inverse of a receiver (FR-8): neither the function nor its axioms.
    val inverse = recv.functions.map(_.name).filter(_.toLowerCase.contains("inv")) ++
      recv.axioms.collect { case a: NamedDomainAxiom if a.name.startsWith("_inverse_receiver") => a.name }
    assert(inverse.isEmpty, s"receiver inverse: ${inverse.mkString(", ")}")
    // The per-filter element of a block, with its signature; no preimage set (it need not be finite).
    assert(!recv.functions.exists(_.name == "preimg"), "preimg declared")
    val expected = Map(
      preimgElemKey -> "Receiver[I], Set[I], Ref -> I")
    val sigs = recv.functions.collect { case f if expected.contains(f.name) =>
      f.name -> s"${f.formalArgs.map(_.typ).mkString(", ")} -> ${f.typ}" }.toMap
    assert(sigs == expected, s"signatures: $sigs")
    val axiomNames = recv.axioms.collect { case a: NamedDomainAxiom => a.name }.toSet
    assert(axiomNames.contains("_preimgElemInv") && !axiomNames.contains("_preimg"), s"axioms: $axiomNames")
    // The helpers build applications that match the declarations, for a crimp term of each encoding.
    val helper = new AxiomHelper(p, 2)
    val fuel = helper.fuelDefaultExp
    val loc = LocalVar("l", Ref)()
    val bad = p.deepCollect { case c: CrimpApp => c }.flatMap { c =>
      val hasID = c.reduction.isInstanceOf[CrimpTripleWithId]
      val t = c.toViper(p, fuel, CrHeap(0)).asInstanceOf[DomainFuncApp]
      val (cons, fs) = (t.args(2), t.args(3))
      val elem = helper.preimgElemApply(cons, fs, loc)(hasID)
      val apps = Seq(elem)
      val guard = helper.witnessReaches(elem, fs, cons, loc)(hasID)
      (apps.filterNot(conforms(p, _)).map(_.toString) ++
        Seq(guard).filterNot(g => g.typ == viper.silver.ast.Bool && Expressions.isPure(g)).map(_.toString))
        .map(s => s"${c.fieldName}: $s")
    }
    assert(bad.isEmpty, s"ill-formed applications: ${bad.mkString("; ")}")
  }

  test("AxiomHelper: field footprints of statements") {
    // footprints.vpr states each method's expected footprint in a comment.
    val frontend = runFrontend("viper.silver.plugin.crimp.CrimpPlugin", "crimp/footprints.vpr")
    assert(frontend.errors.isEmpty, frontend.errors.map(_.readableMessage).mkString("\n"))
    val p = frontend.translatedProgram.get
    val helper = new AxiomHelper(p, 2)
    val all = Set("v", "vv", "w", "u")
    val expected: Map[String, Set[String]] = Map(
      "m_write" -> Set("v"), "m_pred" -> Set("v", "vv"), "m_cycle" -> Set("u"), "m_abstract" -> all,
      "m_package" -> Set("vv", "w"), "m_call" -> Set("w"), "m_new" -> Set("u"), "m_new_all" -> all,
      "m_loop" -> Set("vv"), "m_quasihavoc" -> Set("v"), "m_fold_pure" -> Set())
    val wrong = expected.toSeq.sortBy(_._1).flatMap { case (m, fs) =>
      val got = helper.modifiedFields(p.findMethod(m).body.get)
      if (got == fs) None else Some(s"$m: ${got.toSeq.sorted.mkString(",")} (expected ${fs.toSeq.sorted.mkString(",")})")
    }
    assert(wrong.isEmpty, wrong.mkString("; "))
    // Resources directly: a predicate instance contributes its body's footprint, transitively.
    val q = p.findMethod("m_pred").pres.head
    val a = p.findMethod("m_abstract").pres.head
    assert(helper.footprintFields(q) == Set("v", "vv") && helper.footprintFields(a) == all)
  }

  test("CrimpPlugin: decomposition depths from @decompDepth annotations and -Dcrimp.decompDepth") {
    // Only strings and numbers are compared and reported (see above).
    def depths(): Either[String, Map[String, Int]] = {
      val frontend = runFrontend("viper.silver.plugin.crimp.CrimpPlugin", "crimp/decomp-depth.vpr")
      if (frontend.errors.nonEmpty) Left(frontend.errors.map(_.readableMessage).mkString("\n"))
      else {
        def depth(e: Exp): Int = e match {
          case DomainFuncApp(DomainsGenerator.fuelSKey, Seq(f), _) => 1 + depth(f)
          case _ => 0
        }
        Right(frontend.program.get.findMethod("m").body.get.deepCollect {
          case LocalVarAssign(LocalVar(v, _), d: DomainFuncApp)
            if d.funcname == DomainsGenerator.crimpApplyKeyM || d.funcname == DomainsGenerator.crimpApplyKeyS =>
            v -> depth(d.args.head)
        }.toMap)
      }
    }
    val expected = Map("s1" -> 1, "s2" -> 2, "s3" -> 3, "s4" -> 4, "s5" -> 3)
    assert(depths() == Right(expected))
    try {
      sys.props(DecompDepth.property) = "5"
      assert(depths() == Right(expected.updated("s2", 5)), "the property sets the default")
      sys.props(DecompDepth.property) = "0"
      val bad = depths()
      assert(bad.left.exists(_.contains("-Dcrimp.decompDepth=0: expected a positive integer")), bad.toString)
    } finally sys.props -= DecompDepth.property
  }

  /** `app` matches its declaration in `p`: arity, argument types and result type. */
  def conforms(p: Program, app: DomainFuncApp): Boolean = {
    val f = p.findDomainFunction(app.funcname)
    f.formalArgs.size == app.args.size &&
      f.formalArgs.map(_.typ.substitute(app.typVarMap)) == app.args.map(_.typ) &&
      f.typ.substitute(app.typVarMap) == app.typ
  }

  class MockPluginFrontend extends SilFrontend {

    protected var instance: MockPluginVerifier = _

    /** The program as translated and consistency-checked, before the plugins' beforeVerify. */
    var translatedProgram: Option[Program] = None

    override def verification(): Unit = {
      translatedProgram = _program
      super.verification()
    }

    override def createVerifier(fullCmd: String): Verifier = {
      instance = new MockPluginVerifier
      instance
    }

    override def configureVerifier(args: Seq[String]): SilFrontendConfig = {
      instance.parseCommandLine(args)
      instance.config
    }
  }

  class MockPluginVerifier extends Verifier {

    private var _config: MockPluginConfig = _

    def config: MockPluginConfig = _config

    override def name: String = "MockPluginVerifier"

    override def version: String = "3.14"

    override def buildVersion: String = "2.71"

    override def copyright: String = "(c) Copyright ETH Zurich 2012 - 2021"

    override def debugInfo(info: Seq[(String, Any)]): Unit = {}

    override def dependencies: Seq[Dependency] = Seq()

    override def parseCommandLine(args: Seq[String]): Unit = {
      _config = new MockPluginConfig(args)
    }

    override def start(): Unit = {}

    override def verify(program: Program): VerificationResult = {
      result
    }

    override def stop(): Unit = {}

    override def reporter: Reporter = StdIOReporter()
  }

  class MockPluginConfig(args: Seq[String]) extends SilFrontendConfig(args, "MockPluginVerifier"){
    verify()
  }
}
