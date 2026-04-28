package viper.silver.plugin.crimp

import fastparse.{NoCut, P}
import viper.silver.ast.pretty.FastPrettyPrinter.pretty
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.ast.{NoPosition, Position, Program}
import viper.silver.frontend.{DefaultStates, ViperPAstProvider}
import viper.silver.logger.SilentLogger
import viper.silver.parser.FastParserCompanion.{ExtendedParsing, LeadingWhitespace, PositionParsing, reservedKw, reservedSym}
import viper.silver.parser.PDelimited.Comma
import viper.silver.parser.{FastParser, FastParserCompanion, PAnnotationsPosition, PAssign, PCall, PCallable, PDelimited, PDomain, PDomainType, PDomainTypeKinds, PExp, PFieldAccess, PFormalArgDecl, PGrouped, PIdnDef, PIdnRef, PKw, PNode, PProgram, PReserved, PSetType, PSym, PType}
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
//    ParserExtension.addNewDeclAtStart(filterDef(_))
//    crimpDomainString() ++
//    crimpDomainStringNoId() ++
//    fuelDomainString() ++
//    receiverDomainString() ++
//    opDomainString() ++
//    mappingDomainString() ++
//    setEditDomainString() ++
    input
  }

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
   *
   * @param input Parse AST
   * @return Modified Parse AST
   */
  override def beforeResolve(input: PProgram) : PProgram = {
    if (input.filterMembers {
      case _: PCrimp | _: PReceiver | _: PMapping | _: POperator => true
      case _ => false
    }.members.isEmpty) {
      input
    } else {
      setOperators = input.deepCollect({
        case op: POperator =>
          op
      }).toSet

      val importCrimpM = if (input.filterMembers {
        case op: POperator => op.opUnit match {
          case None => false
          case Some(_) => true
        }
        case _ => false
      }.members.nonEmpty) {
        Set("import <crimp/crimpM.vpr>")
      } else { Set() }

      val importCrimpS = if (input.filterMembers {
        case op: POperator => op.opUnit match {
          case None => true
          case Some(_) => false
        }
        case _ => false
      }.members.nonEmpty) {
        Set("import <crimp/crimpS.vpr>")
      } else { Set() }

      val importStmts = Set("import <crimp/crimp.vpr>") ++ importCrimpM ++ importCrimpS

//      val opDomains = (input.filterMembers {
//        case _: POperator => true
//        case _ => false
//      }.members map {
//        case op@POperator(_, idndef, args, _, returnType, _) =>
//          val arglist = if (args.inner.isEmpty) {""} else
//          {args.inner.toSeq.map(a => s"""${a.idndef.name}: ${a.typ.toString()}""").mkString(", ")}
//          s"""
//             |domain ${op.genDomainName} {
//             |
//             |  function ${idndef.name}$arglist: $opDKey[${returnType.toString()}]
//             |
//             |}""".stripMargin
//      }).mkString("\n")
//
//      val mapDomains = (input.filterMembers {
//        case _: PMapping => true
//        case _ => false
//      }.members map {
//        case map@PMapping(_, idndef, args, _, returnType) =>
//          val arglist = if (args.inner.isEmpty) {""} else
//          {args.inner.toSeq.map(a => s"""${a.idndef.name}: ${a.typ.toString()}""").mkString(", ")}
//          s"""
//             |domain ${map.genDomainName} {
//             |
//             |  function ${idndef.name}$arglist: $mapDKey[${map.inputType.toString()},${returnType.toString()}]
//             |
//             |}""".stripMargin
//      }).mkString("\n")
//
//      val recvDomains = (input.filterMembers {
//        case _: PReceiver => true
//        case _ => false
//      }.members map {
//        case recv@PReceiver(_, idndef, args, _) =>
//          val arglist = if (args.inner.isEmpty) {""} else
//          {args.inner.toSeq.map(a => s"""${a.idndef.name}: ${a.typ.toString()}""").mkString(", ")}
//          s"""
//             |domain ${recv.genDomainName} {
//             |
//             |  function ${idndef.name}($arglist): $recDKey[${recv.indexType.toString()}]
//             |
//             |}""".stripMargin
//      }).mkString("\n")

      val importOnlyProgram = importStmts.mkString("\n")
      val importPProgram = PAstProvider.generateViperPAst(importOnlyProgram).get.filterMembers(_.isInstanceOf[PDomain])
      val mergedProgram = PProgram(input.imported :+ importPProgram, input.members)(input.pos, input.localErrors, input.offsets, input.rawProgram)
      val output = super.beforeTranslate(mergedProgram)
      output
//      def transformStrategy[T <: PNode](input: T): T = StrategyBuilder.Slim[PNode]({
//        case op@POperator(_, idndef, args, _, returnType, _) =>
//          genOpPDomain(op, idndef, args, returnType)
//      }).execute(input)
//
//      val newOutput = transformStrategy(output)
//      newOutput
    }
  }

//  private def genOpPDomain[T <: PNode](op: POperator, idndef: PIdnDef, args: Comma[PSym.Paren, PFormalArgDecl], returnType: PType) = {
//    val arglist = if (args.inner.isEmpty) {"()"} else {args.inner.toSeq.toString()}
//    val dom = PAstProvider.generateViperPAst(
//      s"""
//         |import <crimp/crimp.vpr>
//         |
//         |domain ${op.genDomainName} {
//         |
//         |  function ${idndef.name}$arglist: $opDKey[${returnType.toString()}]
//         |
//         |}""".stripMargin)
//    dom.get.filterMembers(_.isInstanceOf[PDomain])
//  }

  object PAstProvider extends ViperPAstProvider(NoopReporter, SilentLogger().get) {
    def generateViperPAst(code: String): Option[PProgram] = {
      val code_id = code.hashCode.asInstanceOf[Short].toString
      _input = Some(code)
      execute(Seq("--ignoreFile", code_id))

      if (errors.isEmpty) {
        Some(semanticAnalysisResult)
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

  def defaultMappingIden(tuple: (Position, Position)): PCall = {
    PCall(PIdnRef(mapIdenKey)(tuple), PDelimited.impliedParenComma(Seq()), None)(tuple)
  }

  def makeDomainType(name: String, typeArgs: Seq[PType]): PDomainType = {
    val noPosTuple = (NoPosition, NoPosition)
    val outType = PDomainType(PIdnRef(name)(noPosTuple), Some(PDelimited.impliedBracketComma(typeArgs)))(noPosTuple)
    outType.kind = PDomainTypeKinds.Domain
    outType
  }

  def makeSetType(typeArg: PType): PSetType = {
    val noPosTuple = (NoPosition, NoPosition)
    val outType = PSetType(PReserved.implied(PKw.Set), PGrouped.impliedBracket(typeArg))(noPosTuple)
    outType
  }

}