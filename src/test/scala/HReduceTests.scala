// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, SilFrontendConfig}
import viper.silver.parser.FastParser
import viper.silver.plugin.SilverPluginManager
import viper.silver.reporter.{NoopReporter, Reporter, StdIOReporter}
import viper.silver.verifier._

import java.nio.file.Paths

class HReduceTests extends AnyFunSuite {
//  val inputfile = "hreduce/arrayBubbleSort.vpr"
//  val inputfile = "hreduce/array-sum-i1.vpr"
//  val inputfile = "hreduce/array-sum-i2.vpr"
//  val inputfile = "hreduce/array-sum-fail1.vpr"
//  val inputfile = "hreduce/array-sum-fail2.vpr"
//  val inputfile = "hreduce/arraySwap.vpr"
//  val inputfile = "hreduce/arraySwapMax.vpr"
//  val inputfile = "hreduce/arrayBubbleSort.vpr"
//  val inputfile = "hreduce/coincidence-count.vpr"
//  val inputfile = "hreduce/coincidence-count-fail1.vpr"
//  val inputfile = "hreduce/coincidence-count-fail2.vpr"
//  val inputfile = "hreduce/quicksort-lomuto.vpr"
//  val inputfile = "hreduce/quickSort-perms.vpr"
//  val inputfile = "hreduce/quicksort-lomuto-max.vpr"
  val inputfile = "hreduce/graphs.vpr"
//  val inputfile = "hreduce/shearSort.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap2MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap3MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap4MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap5MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap6MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap7MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap8MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMS/arraySwap9MS.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap2Max.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap3Max.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap4Max.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap5Max.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap6Max.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap7Max.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap8Max.vpr"
//  val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap9Max.vpr"
//    val inputfile = "hreduce/arraySwapK/arraySwapKMax/arraySwap4Max-norotate.vpr"
  val plugins: Seq[String] = Seq(
//    "TestPluginAllCalled",
    "viper.silver.plugin.hreduce.HReducePlugin"
  )

  var result: VerificationResult = Success

  def testOne(plugin: String): Unit ={
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
    assert(frontend.plugins.plugins.size == 1 + frontend.defaultPluginCount)
    frontend.plugins.plugins.foreach {
      case p: TestPlugin => assert(p.test(), p.getClass.getName)
      case _ =>
    }
  }

  plugins.foreach(p => test(p)(testOne(p)))

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
