// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.{ExtensionExp, Program}
import viper.silver.frontend.{DefaultStates, SilFrontend, SilFrontendConfig}
import viper.silver.parser.FastParser
import viper.silver.plugin.SilverPluginManager
import viper.silver.reporter.{NoopReporter, Reporter, StdIOReporter}
import viper.silver.verifier._

import java.nio.file.Paths

class CrimpTypingTests extends AnyFunSuite {
  val plugin = "viper.silver.plugin.crimp.CrimpPlugin"
  val dir = "crimp/typing/"

  // Inputs the frontend (parsing, resolution/type checking, translation, consistency check, plugins) must accept.
  val inputfiles: Seq[String] = Seq(
    "mapargs_ok.vpr",
    "specs_ok.vpr",
    "op_unit_call_ok.vpr",
    "box_of_crimp_ok.vpr",
    "generic_filter_ok.vpr",
    "domain_return_type_ok.vpr",
  )
  // Inputs the type checker must reject with exactly these errors (message substrings), in particular without an
  // additional internal error and not only in the consistency check.
  val badInputfiles: Seq[(String, Seq[String])] = Seq(
    "assign_bad.vpr" -> Seq("found incompatible type `Int`, expected `Bool`"),
    "call_bad.vpr" -> Seq("found incompatible type `Int`, expected `Bool`"),
    "eq_bad.vpr" -> Seq("found incompatible type `Int`, expected `Multiset[Int]`"),
    "field_bad.vpr" -> Seq("found incompatible type `Mapping[Int, Int]`, expected `Mapping[Bool, Int]`"),
    "filter_bad.vpr" -> Seq("found incompatible type `Receiver[Int]`, expected `Receiver[Bool]`"),
    "map_bad.vpr" -> Seq("found incompatible type `Mapping[Int, Multiset[Int]]`, expected `Mapping[Int, Int]`"),
    "box_bad.vpr" -> Seq("found incompatible type `Int`, expected `Bool`"),
    "arith_bad.vpr" -> Seq("found incompatible type `Bool`, expected `Int`"),
    "nofield_bad.vpr" -> Seq("Field not found."),
    "nested_bad.vpr" -> Seq(nested("nested_bad.vpr@28.48")),
    "nested_receiver_arg_bad.vpr" -> Seq(nested("nested_receiver_arg_bad.vpr@29.27")),
    "func_bad.vpr" -> Seq(outside("func_bad.vpr@28.3")),
    "func_spec_bad.vpr" -> Seq(outside("func_spec_bad.vpr@28.12"), outside("func_spec_bad.vpr@29.21")),
    "predicate_bad.vpr" -> Seq(outside("predicate_bad.vpr@26.55")),
    "mapping_body_bad.vpr" -> Seq(outside("mapping_body_bad.vpr@26.49")),
    "axiom_bad.vpr" -> Seq(outside("axiom_bad.vpr@29.52")),
    "loop_decreases_bad.vpr" -> Seq(decreases("loop_decreases_bad.vpr@32.15")),
    "method_decreases_bad.vpr" -> Seq(decreases("method_decreases_bad.vpr@29.13")),
    "func_decreases_bad.vpr" -> Seq(decreases("func_decreases_bad.vpr@28.13")),
    "op_unit_bad.vpr" -> Seq(outside("op_unit_bad.vpr@28.58")),
    "decomp_depth_zero_bad.vpr" -> Seq("@decompDepth expects one positive integer, e.g. @decompDepth(\"1\"); found (\"0\")."),
    "decomp_depth_twice_bad.vpr" -> Seq("@decompDepth is given more than once."),
    "decomp_depth_mapping_bad.vpr" ->
      Seq("@decompDepth applies to operators, receivers and crimp expressions, not to a mapping."),
    "decomp_depth_expr_bad.vpr" -> Seq("@decompDepth expects one positive integer, e.g. @decompDepth(\"1\"); found (\"two\")."),
    "wand_bad.vpr" -> Seq(wand("wand_bad.vpr@26.52"), wand("wand_bad.vpr@28.49"), wand("wand_bad.vpr@34.50"),
      script("wand_bad.vpr@41.12")),
    "return_type_bad.vpr" -> Seq("found incompatible type `Int`, expected `Bool`"),
  ).map({b => ("bad/" ++ b._1, b._2) })

  def nested(at: String): String = s"Crimp inside another crimp is not supported. ($at"
  def outside(at: String): String = s"Crimp outside a method is not supported. ($at"
  def decreases(at: String): String = s"Crimp in a decreases clause is not supported. ($at"
  def wand(at: String): String = s"Crimp inside a magic wand is not supported. ($at"
  def script(at: String): String = s"Crimp in a package proof script is not supported. ($at"

  var result: VerificationResult = Success

  def runFrontend(inputfile: String): MockPluginFrontend = {
    val resource = getClass.getResource(dir + inputfile)
    assert(resource != null, s"File $dir$inputfile not found")
    val file = Paths.get(resource.toURI)
    val frontend = new MockPluginFrontend
    val instance = SilverPluginManager.resolve(plugin, NoopReporter, null, null, new FastParser())
    assert(instance.isDefined)
    result = instance.get match {
      case p: FakeResult => p.result()
      case _ => Success
    }
    frontend.execute(Seq("--plugin", plugin, file.toString))
    frontend
  }

  def testOk(inputfile: String): Unit = {
    val frontend = runFrontend(inputfile)
    assert(frontend.errors.isEmpty,
      s"$inputfile: frontend reported errors:\n" + frontend.errors.map(_.readableMessage).mkString("\n"))
    assert(frontend.state == DefaultStates.Verification, s"$inputfile: frontend stopped in state ${frontend.state}")
    // The program handed to the verifier (after the plugins' beforeVerify) must not contain a crimp that was not
    // translated: CrimpApp.verifyExtExp is not implemented.
    val untranslated = frontend.program.toSeq.flatMap(_.deepCollect { case e: ExtensionExp => e.toString })
    assert(untranslated.isEmpty, s"$inputfile: not translated before verification:\n" + untranslated.mkString("\n"))
  }

  def testBad(inputfile: String, expected: Seq[String]): Unit = {
    val frontend = runFrontend(inputfile)
    val messages = frontend.errors.map(_.readableMessage)
    val report = s"$inputfile: frontend stopped in state ${frontend.state} and reported:\n" + messages.mkString("\n")
    assert(frontend.state == DefaultStates.SemanticAnalysis, report)
    assert(messages.size == expected.size, report)
    expected.foreach(e => assert(messages.exists(_.contains(e)), s"missing `$e`; " + report))
    assert(!messages.exists(_.contains("internal error")), report)
  }

  for (f <- inputfiles) test(s"CrimpPlugin $dir$f")(testOk(f))
  for ((f, expected) <- badInputfiles) test(s"CrimpPlugin $dir$f (rejected by the type checker)")(testBad(f, expected))

  class MockPluginFrontend extends SilFrontend {

    protected var instance: MockPluginVerifier = _

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
