// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.{DomainFuncApp, Program}
import viper.silver.frontend.{SilFrontend, SilFrontendConfig}
import viper.silver.parser.FastParser
import viper.silver.plugin.SilverPluginManager
import viper.silver.plugin.crimp.ast.{CrHeap, CrimpApp, CrimpTripleWithId, CrimpTripleWithoutId}
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
    "crimp/domain-return-type.vpr",
    "crimp/user-import.vpr"
  )
  // Inputs the frontend must reject with exactly these errors (message substrings), in particular without an
  // additional internal error.
  val badInputfiles: Seq[(String, Seq[String])] = Seq(
    "crimp/bad/operator-arity.vpr" -> Seq(
      "Operator body should have exactly two arguments."
    ),
    "crimp/bad/mapping-arity.vpr" -> Seq(
      "Mapping body should have exactly one argument."
    ),
    "crimp/bad/return-type-mismatch.vpr" -> Seq(
      "found incompatible type `Int`, expected `Bool`",
      "found incompatible type `Mapping[Int, Int]`, expected `Mapping[Int, Bool]`")
  )
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
        Seq(recApplyKey, recInvKey, filterRecvGoodKey, subsetNotInRefsKey, idxNotInRefsKey).map(_ -> recDKey) ++
        Seq(opApplyKey, opIdenKey).map(_ -> opDKey) ++
        Seq(mapApplyKey, mapIdenKey).map(_ -> mapDKey) ++
        Seq(setDeleteKey, disjUnionKey).map(_ -> "SetEdit")
      val declared: Map[String, String] = p.domains.flatMap(d => d.functions.map(_.name -> d.name)).toMap
      val wrong = domainOf.filterNot { case (f, d) => declared.get(f).contains(d) }
        .map { case (f, d) => s"$f (expected in $d, found in ${declared.getOrElse(f, "no domain")})" }
      assert(wrong.isEmpty, s"names not declared as expected: ${wrong.mkString(", ")}")

      // The term builders must find their domain and functions, and applications must match the
      // declarations (arity, argument and result types).
        def conforms(app: DomainFuncApp): Boolean = {
          val f = p.findDomainFunction(app.funcname)
          f.formalArgs.size == app.args.size &&
              f.formalArgs.map(_.typ.substitute(app.typVarMap)) == app.args.map(_.typ) &&
              f.typ.substitute(app.typVarMap) == app.typ
        }
      val fuel = new AxiomHelper(p, true).fuelDefaultExp
      val apps = p.deepCollect { case c: CrimpApp => c }
      val n = apps.size
      assert(n == 4, "arraySwapMax.vpr has four crimp terms")
      val bad = apps.flatMap { c =>
        c.fuelExp = Some(fuel)
        c.cHeap = Some(CrHeap(0))
        c.toViper(p) match {
          case t @ DomainFuncApp(evalName, Seq(_, _, cons: DomainFuncApp, _), _)
              if evalName == c.reduction.crimpEvalFuncName() && cons.funcname == c.reduction.crimpConstructKeyName() &&
                conforms(t) && conforms(cons) => None
            case t => Some(t.toString)
          }
      }
      assert(bad.isEmpty, s"ill-formed crimp terms: ${bad.mkString("; ")}")
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
