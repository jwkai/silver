package viper.silver.plugin.crimp

import fastparse.{NoCut, P}
import viper.silver.ast.pretty.FastPrettyPrinter.pretty
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.ast.{Assume, Infoed, Inhale, LabelledOld, Method, MethodCall, NoPosition, Node, Old, Position, Program}
import viper.silver.frontend.{DefaultStates, ViperPAstProvider}
import viper.silver.logger.SilentLogger
import viper.silver.parser.{FastParser, FastParserCompanion, PAccPred, PAnnotationsPosition, PCall, PCallable, PKwOp, PLocationAccess, PMaybePairArgument, PUnfolding, PDelimited, PDomain, PDomainType, PDomainTypeKinds, PExp, PFieldAccess, PGrouped, PIdnRef, PKw, PNode, PProgram, PReserved, PSetType, PSym, PType}
import viper.silver.plugin.crimp.CrimpPlugin.{addInlinedAxioms, defaultMappingIden}
import viper.silver.plugin.crimp.ast.{CrimpApp, CrHeapMap, crHeapInfo}
import viper.silver.plugin.crimp.DomainsGenerator.mapIdenKey
import viper.silver.plugin.crimp.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{AbstractError, VerificationResult}

import scala.annotation.unused
import scala.language.postfixOps

class CrimpPlugin(@unused reporter: viper.silver.reporter.Reporter,
                  @unused logger: ch.qos.logback.classic.Logger,
                  @unused config: viper.silver.frontend.SilFrontendConfig,
                  fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{ParserExtension, funcApp, exp, argList, formalArg, fieldAccess, foldPExp, idndef, idnref, typ, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, LeadingWhitespace, PositionParsing, reservedKw, reservedSym}

  private val fuelIsTwo: Boolean = true
  private var setOperators: Set[POperator] = Set()

  /** Parser for crimp statements. */
  def crimp[$: P]: P[PCrimp] =
    P((P(PCrimpKeyword) ~~~ funcApp.brackets.lw ~~~ crimpInner.brackets.lw ~~~ exp.parens.lw) map
      {
        case (k, op, mfr, filter) =>
            (k, op.inner, mfr.inner, filter.inner)
      } map (PCrimp.apply _).tupled
    ).pos

  def crimpInner[$:P]: P[PCrimpInner] = P(NoCut(recvApp) | mapRecvApp)

  def recvApp[$:P]: P[PCrimpInner] =
    P(
      (funcApp ~~ fieldAccess map { case (fa, ss) => foldPExp(fa, Seq(ss)) }) map {
        case p@PFieldAccess(rcv, _, idnref) => (
          defaultMappingIden(p.pos),
          idnref,
          rcv.asInstanceOf[PCall]
        )
      } map (PCrimpInner.apply _).tupled
    ).pos

  def mapRecvApp[$:P]: P[PCrimpInner] =
    P(
      (idnref[$, PCallable] ~~~ (recvApp ~~~ (P(",") ~~~ exp.lw.rep(sep = ",")).lw.?).parens.lw) map {
        case (mappingFunc, mappingFuncArgs) =>
          val pMappingFieldReceiver = mappingFuncArgs.inner._1
          val mappingCallArgs = mappingFuncArgs.inner._2
          pMappingFieldReceiver.copy(mapping =
            PCall(
              mappingFunc.retype(),
              PDelimited.impliedParenComma(mappingCallArgs.getOrElse(Seq())),
              None
            )(pMappingFieldReceiver.mapping.pos)
          )(pMappingFieldReceiver.pos)
      }
    )

  def inlineFunDef[$:P]: P[PFunInline] =
        P((P(PFunInlineKeyword) ~~~ argList(formalArg).lw ~~~ P(PSym.Colon).lw ~~~ typ.lw ~~~ P(PSym.ColonColon).lw ~~~ exp.lw)
          map (PFunInline.apply _).tupled).pos

  def componentBody[$:P] : P[PFunInline] = P(inlineFunDef.parens) map (_.inner)

//  def filterDef[$:P] : P[PAnnotationsPosition => PFilter] =
//    P(P(PFilterKeyword) ~~~ idndef.lw ~~~ argList(formalArg).lw ~~~ componentBody.lw) map {
//      case (kw, name, args, body) =>
//        ap: PAnnotationsPosition => {
//          PFilter(kw, name, args, Some(body))(ap.pos)
//        }
//    }

  def operatorDef[$:P] : P[PAnnotationsPosition => POperator] =
    P(P(POperatorKeyword) ~~~ idndef.lw ~~~ argList(formalArg).lw ~~~ (NoCut(componentBody.map((_, None))) | operatorBodyUnit).lw) map {
      case (kw, name, args, (body, None)) =>
        ap: PAnnotationsPosition => {
          POperator(kw, name, args, Some(body), body.returnType, None)(ap.pos)
        }
      case (kw, name, args, (body, Some(unit))) =>
        ap: PAnnotationsPosition => {
          POperator(kw, name, args, Some(body), body.returnType, Some(unit))(ap.pos)
        }
    }

  def operatorBodyUnit[$:P] : P[(PFunInline, Option[PExp])] = P((inlineFunDef ~~~ P(PSym.Comma).lw ~~~ exp.lw).parens) map {
    p =>
      p.inner match {
        case (fun, _, unit) => (fun, Some(unit))
      }
  }

  def mappingDef[$:P] : P[PAnnotationsPosition => PMapping] =
    P(P(PMappingKeyword) ~~~ idndef.lw ~~~ argList(formalArg).lw ~~~ componentBody.lw) map {
      case (kw, name, args, body) =>
        ap: PAnnotationsPosition => {
          PMapping(kw, name, args, Some(body), body.returnType)(ap.pos)
        }
    }

  def receiverDef[$:P] : P[PAnnotationsPosition => PReceiver] =
    P(P(PReceiverKeyword) ~~~ idndef.lw ~~~ argList(formalArg).lw ~~~ componentBody.lw) map {
      case (kw, name, args, body) =>
        ap: PAnnotationsPosition => {
          PReceiver(kw, name, args, Some(body))(ap.pos)
        }
    }

  /** Called before any processing happened.
   *
   * @param input Source code as read from file
   * @param isImported Whether the current input is an imported file or the main file
   * @return Modified source code
   */
  override def beforeParse(input: String, isImported: Boolean) : String = {
    ParserExtension.addNewDeclAtStart(operatorDef(_))
    ParserExtension.addNewDeclAtStart(mappingDef(_))
    ParserExtension.addNewDeclAtStart(receiverDef(_))
    ParserExtension.addNewExpAtStart(crimp(_))
    input
  }

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
   *
   * @param input Parse AST
   * @return Modified Parse AST
   */
  override def beforeResolve(input: PProgram) : PProgram = {
    if (!input.extensions.exists {
      case _: PReceiver | _: PMapping | _: POperator => true
      case _ => false
    }) {
      input
    } else {
      setOperators = input.deepCollect({
        case op: POperator => op
      }).toSet

      val importCrimpM = if (input.extensions.exists {
        case op: POperator => op.opUnit.isDefined
        case _ => false
      }) {
        Set("import <crimp/crimpM.vpr>")
      } else { Set() }

      val importCrimpS = if (input.extensions.exists {
        case op: POperator => op.opUnit.isEmpty
        case _ => false
      }) {
        Set("import <crimp/crimpS.vpr>")
      } else { Set() }

      // A program may import crimp's domains itself. Only the files the program does not import are added.
      val importedByProgram = input.imports.filterNot(_.local).map(i => s"import <${i.file.str}>").toSet
      val importStmts = (Set("import <crimp/crimp.vpr>") ++ importCrimpM ++ importCrimpS) -- importedByProgram

      val importOnlyProgram = importStmts.mkString("\n")
      val mergedProgram = if (importStmts.isEmpty) input else {
        val importPProgram = PAstProvider.generateViperPAst(importOnlyProgram).get.filterMembers(_.isInstanceOf[PDomain])
        PProgram(input.imported :+ importPProgram, input.members)(input.pos, input.localErrors, input.offsets, input.rawProgram)
      }
      val mergedProgramCCs = transformComponentCalls(mergedProgram)
      mergedProgramCCs.initProperties()
      val output = super.beforeTranslate(mergedProgramCCs)
      output
    }
  }

  /** Replaces calls to crimp components (receiver, operator, mapping), which are read by the parser as PCall instances,
   * with a PComponentCall to be typechecked and translated by the plugin.
   * This mimics the approach of the ADT plugin (e.g. PDescriptorCall and PDiscriminatorCall).
   * We handle `unfolding component(..) in e` manually, as the PComponentCall cannot extend this sealed trait*/
  private def transformComponentCalls(input: PProgram): PProgram = {
    val componentNames = input.extensions.collect { case c: PCrimpComponent => c.idndef.name }.toSet
    if (componentNames.isEmpty) input
    else StrategyBuilder.Slim[PNode]({
      case pu@PUnfolding(unfolding, pc@PCall(idnref, _, _), in, exp) if componentNames.contains(idnref.name) =>
        PUnfolding(unfolding, PAccPred(PReserved.implied(PKwOp.Acc), PGrouped.impliedParen(
          PMaybePairArgument[PLocationAccess, PExp](pc, None)(pc.pos)))(pc.pos), in, exp)(pu.pos)
      case pc@PCall(idnref, callArgs, typeAnnotated) if componentNames.contains(idnref.name) =>
        PComponentCall(idnref.retype(), callArgs, typeAnnotated)(pc.pos)
    }).recurseFunc({
      case n: PNode => n.children collect {case ar: AnyRef => ar}
    }).execute(input)
  }

  object PAstProvider extends ViperPAstProvider(NoopReporter, SilentLogger().get) {

    override val phases: Seq[Phase] = Seq(Parsing)
    override def result: VerificationResult = if (_errors.isEmpty) viper.silver.verifier.Success else viper.silver.verifier.Failure(_errors)

    def generateViperPAst(code: String): Option[PProgram] = {
      val code_id = code.hashCode.asInstanceOf[Short].toString
      _input = Some(code)
      execute(Seq("--ignoreFile", code_id))

      // we do not want the semantic analysis to be run here,
      // as we are adding domains to the program that must be resolved together with the original code
      if (errors.isEmpty) {
        Some(parsingResult)
      } else {
        None
      }
    }

    def setCode(code: String): Unit = {
      _input = Some(code)
    }

    override def reset(input: java.nio.file.Path): Unit = {
      if (state < DefaultStates.Initialized) sys.error("The translator has not been initialized.")
      _state = DefaultStates.InputSet
      _inputFile = Some(input)

      /** must be set by [[setCode]] */
      // _input = None
      _errors = Seq()
      _parsingResult = None
      _semanticAnalysisResult = None
      _verificationResult = None
      _program = None
      resetMessages()
    }
  }

//  /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
//   *
//   * @param input Parse AST
//   * @return Modified Parse AST
//   */
//  override def beforeTranslate(input: PProgram): PProgram = {
//    input
//  }

  /** Called after parse AST has been translated into the normal AST but before methods to verify are filtered.
   * In [[viper.silver.frontend.SilFrontend]] this step is confusingly called doTranslate.
   *
   * @param input AST
   * @return Modified AST
   */
  override def beforeMethodFilter(input: Program) : Program = {
    // Move new methods to here
    val newInput = addOpWelldefinednessMethods(input)
    newInput
  }

  def addOpWelldefinednessMethods(p: Program): Program = {
    val opMethods = setOperators.map(o => o.generatedOpWelldefinednessCheck(p)).toSeq
    p.copy(methods = opMethods ++ p.methods)(p.pos, p.info, p.errT)
  }

  /** Called after methods are filtered but before the verification by the backend happens: lowers the crimp
   * expressions (as HReducePlugin.beforeVerify, without its debug print). A program without crimp expressions is
   * returned unchanged (the lowering's AxiomHelper needs the imported crimp domains, which such a program may lack).
   *
   * @param input AST
   * @return Modified AST
   */
  override def beforeVerify(input: Program) : Program = {
    if (!input.existsDefined { case _: CrimpApp => }) return input
    var newInput = addInlinedAxioms(input, fuelIsTwo, reportError)
    newInput = newInput.transform({
      case e@Assume(a) => Inhale(a)(e.pos, e.info, e.errT)
    })
//    print(pretty(newInput) + "\n\n")
    newInput
  }

//  /** Called after the verification of an entity, which is used to stream verification results to the IDE
//   * (which happens as soon as a member has been verified). Error transformation should happen here.
//   * This will only be called if verification of `entity` took place.
//   *
//   * @param entity Entity to which `input` belongs
//   * @param input Result of verification
//   * @return Modified result
//   */
//  override def mapEntityVerificationResult(entity: Entity, input: VerificationResult): VerificationResult = ???

//  /** Called after the verification. Error transformation should happen here.
//   * This will only be called if verification took place.
//   *
//   * @param program Viper AST
//   * @param input Result of verification
//   * @return Modified result
//   */
//  override def mapVerificationResult(program: Program, input: VerificationResult): VerificationResult = ???

//  /** Called after the verification just before the result is printed. Will not be called in tests.
//   * This will also be called even if verification did not take place (i.e. an error during parsing/translation occurred).
//   *
//   * @param input Result of verification
//   * @return Modified result
//   */
//  override def beforeFinish(input: VerificationResult) : VerificationResult = ???

//  /** Can be called by the plugin to report an error while transforming the input.
//   *
//   * The reported error should correspond to the stage in which it is generated (e.g. no ParseError in beforeVerify)
//   *
//   * @param error The error to report
//   */
//  override def reportError(error: AbstractError): Unit = ???
}

object CrimpPlugin {

  /** `[a, b, c]` without positions: the type arguments of a generated domain type such as `Operator[Int]`. The
    * delimited list has no trailing delimiter (`end = None`), as the type arguments of a parsed domain type. */
  def impliedBracketComma[T <: PNode](inner: Seq[T]): PDelimited.Comma[PSym.Bracket, T] =
    PGrouped.impliedBracket(PDelimited[T, PSym.Comma](inner.headOption,
      inner.map((PReserved.implied(PSym.Comma), _)).drop(1), None)(NoPosition, NoPosition))

  def defaultMappingIden(tuple: (Position, Position)): PCall = {
    PCall(PIdnRef(mapIdenKey)(tuple), PDelimited.impliedParenComma(Seq()), None)(tuple)
  }

  def makeDomainType(name: String, typeArgs: Seq[PType]): PDomainType = {
    val noPosTuple = (NoPosition, NoPosition)
    val outType = PDomainType(PIdnRef(name)(noPosTuple), Some(impliedBracketComma(typeArgs)))(noPosTuple)
    outType.kind = PDomainTypeKinds.Domain
    outType
  }

  def makeSetType(typeArg: PType): PSetType = {
    val noPosTuple = (NoPosition, NoPosition)
    val outType = PSetType(PReserved.implied(PKw.Set), PGrouped.impliedBracket(typeArg))(noPosTuple)
    outType
  }

  def addInlinedAxioms(p: Program, fuelIsTwo: Boolean, reportError: AbstractError => Unit) : Program = {
    def modifyMethod(m: Method) : Method = {
      // If a method evaluates no reduction (neither itself nor through the specification of a method it calls), keep
      // the method the same
      if (!InlineAxiomGenerator.needsLowering(p, m)) { return m }

      val axiomGenerator = new InlineAxiomGenerator(p, m.name, fuelIsTwo, reportError)

      // Convert all method calls to inhales and exhales
      var outM: Method = m.transform({
        case e: MethodCall => axiomGenerator.convertMethodToInhaleExhale(e)
      })

      // The receivers are those of the reductions of the method after the conversion (body, specification, loop
      // invariants, and the callees' specifications).
      axiomGenerator.initReceivers(outM)

      // Add axioms for exhales, inhales and heap writes, tagging every statement with its crimp-heap indices
      outM = outM.body match {
        case Some(mBody) =>
          outM.copy(body =
            Some(axiomGenerator.lowerBody(mBody))
          )(outM.pos, outM.info, outM.errT)
        case None =>
          axiomGenerator.lowerMissingBody()
          outM
      }

//      // add axioms for heap reads, using bottom up traversal
//      // TODO: ensure that the correct crHeap annotations are observed by these axioms
//      outM = outM.transform({
//        case s: Stmt  =>
//          axiomGenerator.generateHeapReadAxioms(s, s match {
//            case NodeWithCHeapInfo(cHeapInfo(rh)) => rh
//            case _ => axiomGenerator.getCurrentCHeap
//          })
//      }, recurse = Traverse.BottomUp)

      // Now, transform CrimpApp nodes in context of cHeap annotations. A reduction is evaluated at the index of its
      // receiver (heapKey): in a statement, at the indices the statement is tagged with; inside old(e), at the method's
      // entry indices; inside old[L](e), at the indices recorded at label L. The old(..)/old[L](..) wrapper is kept, so
      // that Viper evaluates the reduction's receiver and filter arguments in that state, too.
      val fuel = axiomGenerator.getFuelExp
      def lowerReductions[N <: Node](n: N, rhInitial: CrHeapMap): N = n.transformWithContext[CrHeapMap]({
        case (s@NodeWithCrHeapInfo(crHeapInfo(rh)), _) =>
          (s, rh)
        case (o: Old, _) =>
          (o, axiomGenerator.getOldCrHeap)
        case (lo: LabelledOld, _) if InlineAxiomGenerator.hasCrimp(lo) =>
          (lo, axiomGenerator.getCrHeapFromUserLabel(lo.oldLabel, lo.pos))
        case (ra: CrimpApp, rh) =>
          (ra.toViper(p, fuel, rh(ra.heapKey)), rh)
      }, initialContext = rhInitial)

      outM = outM.body match {
        case Some(mBody) =>
          outM.copy(body =
            Some(lowerReductions(mBody, axiomGenerator.getOldCrHeap))
          )(outM.pos, outM.info, outM.errT)
        case None => outM
      }

      // TODO: figure out why this doesn't work...
//      def stripCHeapInfo(n: Node) = {
//        val nMeta = n.meta.copy(_2 = n.meta._2.removeUniqueInfo[cHeapInfo])
//        n.withMeta(nMeta)
//      }
//      outM = outM.body match {
//        case Some(mBody) =>
//          outM.copy(body =
//            Some(mBody.transform({
//              case n@NodeWithCHeapInfo(cHeapInfo(_)) =>
//                stripCHeapInfo(n)
//            }))
//          )(outM.pos, outM.info, outM.errT)
//        case None => outM
//      }

      // Add heap-dependent function to pre-/post-conditions. The invariants of the loops keep no reduction: the conjuncts
      // containing one are asserted and assumed in the loop body instead (InlineAxiomGenerator).
      outM = outM.copy(
        pres =
          outM.pres.map(pre => lowerReductions(pre, axiomGenerator.getOldCrHeap)),
        posts =
          outM.posts.map(post => lowerReductions(post, axiomGenerator.getCurrentCrHeap))
      )(outM.pos, outM.info, outM.errT)

      outM
    }

    // Modify all methods
    val outMethods = p.methods.map(m => modifyMethod(m))

    // Modify the program
    p.copy(methods = outMethods)(p.pos, p.info, p.errT)
  }
}

object NodeWithCrHeapInfo {
  def unapply(node : Node) : Option[crHeapInfo] = node match {
    case i: Infoed => i.info.getUniqueInfo[crHeapInfo]
    case _ => None
  }
}