package viper.silver.plugin.crimp

import fastparse.{NoCut, P}
import viper.silver.ast.pretty.FastPrettyPrinter.pretty
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.ast.{NoPosition, Position, Program}
import viper.silver.frontend.{DefaultStates, ViperPAstProvider}
import viper.silver.logger.SilentLogger
import viper.silver.parser.FastParserCompanion.{ExtendedParsing, LeadingWhitespace, PositionParsing, reservedKw, reservedSym}
import viper.silver.parser.PDelimited.Comma
import viper.silver.parser.{FastParser, FastParserCompanion, PAccPred, PAnnotationsPosition, PAssign, PCall, PCallable, PDelimited, PDomain, PDomainType, PDomainTypeKinds, PExp, PFieldAccess, PFormalArgDecl, PGrouped, PIdnDef, PIdnRef, PKw, PKwOp, PLocationAccess, PMaybePairArgument, PNode, PProgram, PReserved, PSetType, PSym, PType, PUnfolding}
import viper.silver.plugin.crimp.CrimpPlugin.defaultMappingIden
import viper.silver.plugin.crimp.DomainsGenerator.{crimpDomainString, crimpDomainStringNoId, fuelDomainString, mapDKey, mapIdenKey, mappingDomainString, opDKey, opDomainString, parseDomainString, recDKey, receiverDomainString, setEditDomainString}
import viper.silver.plugin.crimp.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.reporter.{Entity, NoopReporter}
import viper.silver.verifier.{AbstractError, VerificationResult}

import scala.annotation.unused
import scala.language.postfixOps

class CrimpPlugin(@unused reporter: viper.silver.reporter.Reporter,
                  @unused logger: ch.qos.logback.classic.Logger,
                  @unused config: viper.silver.frontend.SilFrontendConfig,
                  fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{ParserExtension, funcApp, exp, argList, formalArg, fieldAccess, foldPExp, idndef, idnref, typ, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, LeadingWhitespace, PositionParsing, reservedKw, reservedSym}

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

////    if (input.filterMembers {
////      case _: PCrimp | _: PReceiver | _: PMapping | _: PFilter | _: POperator => true
////      case _ => false
////    }.members.isEmpty) {
////      input
////    } else {
////      val reduceDomainWithID =
////        if (input.filterMembers {
////          case op: POperator => op.opUnit match {
////            case None => false
////            case Some(_) => true
////          }
////          case _ => false
////        }.members.nonEmpty) {
////          Seq(crimpDomainString())
////        } else {
////          Seq()
////        }
////      val reduceDomainWithoutID =
////        if (input.filterMembers {
////          case op: POperator => op.opUnit match {
////            case None => true
////            case Some(_) => false
////          }
////          case _ => false
////        }.members.nonEmpty) {
////          Seq(crimpDomainStringNoId())
////        } else {
////          Seq()
////        }
////      val domainsToAdd = (reduceDomainWithID ++ reduceDomainWithoutID ++ Seq(
////        fuelDomainString(),
////        receiverDomainString(),
////        opDomainString(),
////        mappingDomainString(),
////        setEditDomainString()
////      )).map(parseDomainString) // :+ convertUserDefs(input.extensions)
////
////      val newInput = input.copy(
////        members = input.members ++ domainsToAdd
////      )(input.pos, input.localErrors, input.offsets, input.rawProgram)
////      newInput
////    }
//  }

  /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
   *
   * @param input Parse AST
   * @return Modified Parse AST
   */
  override def beforeTranslate(input: PProgram): PProgram = {
//    if (input.filterMembers {
//      case _: PCrimp | _: PReceiver | _: PMapping | _: POperator => true
//      case _ => false
//    }.members.isEmpty) {
//      input
//    } else {
//      setOperators = input.deepCollect({
//        case op: POperator =>
//          op
//      }).toSet
//
//      val importCrimpM = if (input.filterMembers {
//        case op: POperator => op.opUnit match {
//          case None => false
//          case Some(_) => true
//        }
//        case _ => false
//      }.members.nonEmpty) {
//        Set("import <crimp/crimpM.vpr>")
//      } else { Set() }
//
//      val importCrimpS = if (input.filterMembers {
//        case op: POperator => op.opUnit match {
//          case None => true
//          case Some(_) => false
//        }
//        case _ => false
//      }.members.nonEmpty) {
//        Set("import <crimp/crimpS.vpr>")
//      } else { Set() }
//
//      val importStmts = Set("import <crimp/crimp.vpr>") ++ importCrimpM ++ importCrimpS
//
//      val importOnlyProgram = importStmts.mkString("\n")
//      val importPProgram = PAstProvider.generateViperPAst(importOnlyProgram).get.filterMembers(_.isInstanceOf[PDomain])
//      val mergedProgram = PProgram(input.imported :+ importPProgram, input.members)(input.pos, input.localErrors, input.offsets, input.rawProgram)
//      super.beforeTranslate(mergedProgram)
//    }
    input
  }

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
//
//  /** Called after methods are filtered but before the verification by the backend happens.
//   *
//   * @param input AST
//   * @return Modified AST
//   */
//  override def beforeVerify(input: Program) : Program = ???
//
//  /** Called after the verification of an entity, which is used to stream verification results to the IDE
//   * (which happens as soon as a member has been verified). Error transformation should happen here.
//   * This will only be called if verification of `entity` took place.
//   *
//   * @param entity Entity to which `input` belongs
//   * @param input Result of verification
//   * @return Modified result
//   */
//  override def mapEntityVerificationResult(entity: Entity, input: VerificationResult): VerificationResult = ???
//
//  /** Called after the verification. Error transformation should happen here.
//   * This will only be called if verification took place.
//   *
//   * @param program Viper AST
//   * @param input Result of verification
//   * @return Modified result
//   */
//  override def mapVerificationResult(program: Program, input: VerificationResult): VerificationResult = ???
//
//  /** Called after the verification just before the result is printed. Will not be called in tests.
//   * This will also be called even if verification did not take place (i.e. an error during parsing/translation occurred).
//   *
//   * @param input Result of verification
//   * @return Modified result
//   */
//  override def beforeFinish(input: VerificationResult) : VerificationResult = ???
//
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

}