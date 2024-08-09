package viper.silver.plugin.toto

import fastparse.P
import viper.silver.FastMessaging
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast._
import viper.silver.parser.FastParserCompanion
import viper.silver.parser.FastParser
import viper.silver.parser._
import viper.silver.plugin.toto.ComprehensionPlugin.{addInlinedAxioms, defaultMappingIden, makeDomainType}
import viper.silver.plugin.toto.DomainsGenerator._
import viper.silver.plugin.toto.ast.{ACompApply, ASnapshotDecl}
import viper.silver.plugin.toto.parser.PComprehension.PComprehensionKeywordType
import viper.silver.plugin.toto.parser.{PComprehension, PComprehensionKeyword, PFilter, PFilterKeyword, PFunInline, PFunInlineKeyword, PMapping, PMappingFieldReceiver, PMappingKeyword, PCompOperator, PCompOperatorKeyword, PReceiver, PReceiverKeyword}
import viper.silver.plugin.toto.util.AxiomHelper
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractError, VerificationResult}

import scala.annotation.unused

class ComprehensionPlugin(@unused reporter: viper.silver.reporter.Reporter,
                          @unused logger: ch.qos.logback.classic.Logger,
                          @unused config: viper.silver.frontend.SilFrontendConfig,
                          fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{ParserExtension, funcApp, exp, argList, formalArg, idndef, idnuse, idnref, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, PositionParsing, reservedKw, whitespace}

  private var setOperators: Set[PCompOperator] = Set()

  /** Parser for comprehension statements. */
  def compOp[$: P]: P[(PComprehensionKeywordType, PCall)] =
    P(P(PComprehensionKeyword) ~/ "[" ~ funcApp ~ "]")

  def compDef[$: P]: P[(PMappingFieldReceiver, PExp)] =
    P("(") ~ mapRecBoth ~ "|" ~ exp ~ ")"

  def comp[$: P]: P[PComprehension] =
    P(
      (compOp ~/ compDef) map {
        case (kw, op, (mRf, f)) => (kw, op, mRf, f)
      } map (PComprehension.apply _).tupled
    ).pos

  def funDef[$:P]: P[PFunInline] =
    P(
      (P(PFunInlineKeyword) ~ argList(formalArg) ~ "::" ~ exp) map {
        case (kw, args, body) => (kw, args.inner.toSeq, body)
      } map (PFunInline.apply _).tupled
    ).pos

  def recDef[$:P]: P[PAnnotationsPosition => PReceiver] =
    P(
      (P(PReceiverKeyword) ~ idndef ~ argList(formalArg) ~ funDef.parens) map {
        case (kw, name, args, body) =>
          ap: PAnnotationsPosition => {
            PReceiver(kw, name, args.inner.toSeq, Some(body.inner))(ap.pos)
          }
      }
    )

  def opUnitDef[$:P]: P[PAnnotationsPosition => PCompOperator] =
    P(
      (P(PCompOperatorKeyword) ~ idndef ~ argList(formalArg) ~/ "(" ~ exp ~ "," ~ funDef ~ ")") map {
        case (kw, name, args, unitdef, fundef) =>
          ap: PAnnotationsPosition => {
            PCompOperator(
              kw, name, args.inner.toSeq, unitdef, Some(fundef)
            )(ap.pos)
          }
      }
    )

  def mappingDef[$:P]: P[PAnnotationsPosition => PMapping] =
    P(
      (P(PMappingKeyword) ~ idndef ~ argList(formalArg) ~ funDef.parens) map {
        case (kw, name, args, body) =>
          ap: PAnnotationsPosition => {
            PMapping(kw, name, args.inner.toSeq, Some(body.inner))(ap.pos)
          }
      }
    )

  def filterDef[$:P]: P[PAnnotationsPosition => PFilter] =
  P(
    (P(PFilterKeyword) ~ idndef ~ argList(formalArg) ~ funDef.parens) map {
      case (kw, name, args, body) =>
        ap: PAnnotationsPosition => {
          PFilter(
            kw,
            name,
            args.inner.toSeq,
            Some(body.inner)
          )(ap.pos)
        }
    }
  )

  // Parser without the mapping function
  def recVal[$: P]: P[PMappingFieldReceiver] =
    // Parse the mapping function with two possible syntaxes
    P(
      (funcApp ~ "." ~ idnuse) map {
        case (receiver, field) => (
          defaultMappingIden(receiver.pos),
          field,
          receiver
        )
      } map (PMappingFieldReceiver.apply _).tupled
    ).pos

  // Parser with mapping
  def mapRecVal[$: P]: P[PMappingFieldReceiver] =
    P(
      (idnref[$, PCallable] ~/ "(" ~ recVal ~ "," ~ exp.rep(sep = ",").? ~ ")") map {
        case (mappingFunc, pMappingFieldReceiver, mappingFuncArgs) =>
          pMappingFieldReceiver.copy(mapping =
            PCall(mappingFunc,
              PDelimited.impliedParenComma(mappingFuncArgs.getOrElse(Seq())),
              None
            )(pMappingFieldReceiver.pos)
          )(pMappingFieldReceiver.pos)

      }
    )

  // Allow both with and without Mapping function
  def mapRecBoth[$: P]: P[PMappingFieldReceiver] = {
    recVal | mapRecVal
  }

  /** Called before any processing happened.
    *
    * @param input Source code as read from file
    * @param isImported Whether the current input is an imported file or the main file
    * @return Modified source code
    */
  override def beforeParse(input: String, isImported: Boolean) : String = {
    ParserExtension.addNewExpAtStart(comp(_))
    ParserExtension.addNewDeclAtStart(recDef(_))
    ParserExtension.addNewDeclAtStart(mappingDef(_))
    ParserExtension.addNewDeclAtStart(filterDef(_))
    ParserExtension.addNewDeclAtStart(opUnitDef(_))

//    ParserExtension.addNewDeclAtStart(opUnitDef(_))
//    ParserExtension.addNewPreCondition(comp(_))
//    ParserExtension.addNewPostCondition(comp(_))
//    ParserExtension.addNewInvariantCondition(comp(_))
//    val newInput = input + "\n" + DomainsGenerator.compDomainString() + "\n" +
//      DomainsGenerator.receiverDomainString() + "\n" + DomainsGenerator.mappingDomainString() + "\n" +
//      DomainsGenerator.opDomainString()
//    print(newInput)
    input
  }

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram) : PProgram = {

    val domainsToAdd = Seq(
      compDomainString(),
      receiverDomainString(),
      opDomainString(),
      mappingDomainString(),
      mapCustomDomainString(),
      setFuncDomainString()
    ).map(parseDomainString)// :+ convertUserDefs(input.extensions)

    val newInput = input.copy(
      members = input.members ++ domainsToAdd
    )(input.pos, input.localErrors)
    newInput
  }

  /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeTranslate(input: PProgram): PProgram = {
//    val newInput = input.copy(extensions = input.extensions.filterNot(e => e match {
//        case _: PFilter => true
//        case _: PReceiver => true
//        case _: POperator => true
//        case _: PMapping => true
//        case _ => false
//      }))(input.pos)
    setOperators = input.deepCollect({
      case op: PCompOperator =>
        op
    }).toSet
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

  /** Called after methods are filtered but before the verification by the backend happens.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeVerify(input: Program) : Program = {
//    val dfevalComp = input.findDomainFunction("evalComp")
//    val dfcomp = input.findDomainFunction("comp")
    var newInput =
      input.copy(functions = input.functions.concat(ASnapshotDecl.getAllSnapDecls(input)))(
        input.pos, input.info, input.errT
      )

    // Change the thing to comp
//    newInput = newInput.transform({
//      case c@ASnapshotApp(comprehension4Tuple, filter, _) =>
//        c.toViper
//    })
//    newInput = newInput.transform({
//      case c@ AComprehension4Tuple(_, _, _, _) =>
//        c.toViper
//    })
//    newInput = newInput.transform( {
//      case c@ ACompApply(_, _) =>
//        c.toViper(newInput)
//    })
//    print(pretty(newInput))

//    val currbody = newInput.findMethod("test1").body.get

//    val gen = new InlineAxiomGenerator(newInput, "test1")
//    val newBody = currbody.copy(ss = currbody.ss.appended(gen.generateExhaleAxioms()))(
//      currbody.pos, currbody.info, currbody.errT
//    )

    newInput = addInlinedAxioms(newInput)
    newInput = newInput.transform( {
      case c@ ACompApply(_, _) =>
        c.toViper(newInput)
    })
    newInput = newInput.transform ( {
      case ori @ Assume(a) => Inhale(a)(ori.pos, ori.info, ori.errT)
          // Dont need to transform asserts
//      case ori @ Assert(a) => Exhale(a)(ori.pos, ori.info, ori.errT)
    })
//    print(pretty(newInput))

    newInput


    //    ViperStrategy.Slim({
//      case c@Comprehension(exp) => exp
//    }).execute(input)
  }

  /** Called after the verification. Error transformation should happen here.
    * This will only be called if verification took place.
    *
    * @param input Result of verification
    * @return Modified result
    */
  override def mapVerificationResult(program: Program, input: VerificationResult): VerificationResult = {
    input
  }

  /** Called after the verification just before the result is printed. Will not be called in tests.
    * This will also be called even if verification did not take place (i.e. an error during parsing/translation occurred).
    *
    * @param input Result of verification
    * @return Modified result
    */
  override def beforeFinish(input: VerificationResult) : VerificationResult = {
    input
  }

  /** Can be called by the plugin to report an error while transforming the input.
    *
    * The reported error should correspond to the stage in which it is generated (e.g. no ParseError in beforeVerify)
    *
    * @param error The error to report
    */
  override def reportError(error: AbstractError): Unit = {
    super.reportError(error)
  }

  def addOpWelldefinednessMethods(p: Program): Program = {
    val opMethods = setOperators.map(o => o.generatedOpWelldefinednessCheck(p)).toSeq
    p.copy(methods = opMethods ++ p.methods)(p.pos, p.info, p.errT)
  }
}

object ComprehensionPlugin {

  def defaultMappingIden(tuple: (Position, Position)): PCall = {
    PCall(PIdnRef(mapIdenKey)(tuple), PDelimited.impliedParenComma(Seq()), None)(tuple)
  }

  def makeDomainType(name: String, typeArgs: Seq[PType]): PDomainType = {
    val noPosTuple = (NoPosition,NoPosition)
    val outType = PDomainType(PIdnRef(name)(noPosTuple), Some(PDelimited.impliedBracketComma(typeArgs)))(noPosTuple)
    outType.kind = PDomainTypeKinds.Domain
    outType
  }

  def makeSetType(typeArg: PType): PSetType = {
    val noPosTuple = (NoPosition,NoPosition)
    val outType = PSetType(PReserved.implied(PKw.Set), PGrouped.impliedBracket(typeArg))(noPosTuple)
    outType
  }

  def typeCheckCustom(t: TypeChecker, exp: PExp, oexpected: Option[PType],
                       doCheckInternal : Boolean = true,
                       customMessage: Option[String]): Unit = {
    if (doCheckInternal) {
      t.checkInternal(exp)
    }
    if (exp.typ.isValidOrUndeclared && exp.typeSubstitutions.nonEmpty) {
      val etss = oexpected match {
        case Some(expected) if expected.isValidOrUndeclared => exp.typeSubstitutions.flatMap(_.add(exp.typ, expected).toOption)
        case _ => exp.typeSubstitutions
      }
      if (etss.nonEmpty) {
        val ts = t.selectAndGroundTypeSubstitution(exp, etss)
        exp.forceSubstitution(ts)
      } else {
        oexpected match {
          case Some(expected) =>
            val reportedActual = if (exp.typ.isGround) {
              exp.typ
            } else {
              exp.typ.substitute(t.selectAndGroundTypeSubstitution(exp, exp.typeSubstitutions))
            }
            if (customMessage.nonEmpty) {
              t.messages ++= FastMessaging.message(exp, customMessage.get +
                s"Expected ${expected.toString()}, but found $reportedActual")
            } else {
              t.messages ++= FastMessaging.message(exp,
                s"Expected type ${expected.toString()}, but found $reportedActual at the expression at ${exp.pos._1}")
            }
          case None =>
            t.typeError(exp)
        }
      }
    }
  }

  def addInlinedAxioms(p: Program) : Program = {
    def modifyMethod(m: Method) : Method = {
      val axiomGenerator = new InlineAxiomGenerator(p, m.name)
      // If no comprehension is used in a method, keep the method the same
      if (axiomGenerator.snapshotDeclsUsed.isEmpty) {
        return m
      }
      val helper = new AxiomHelper(p)

      // Convert all method calls to inhales and exhales
      var outM: Method = m.transform({
        case e@MethodCall(_,_,_) =>
          axiomGenerator.convertMethodToInhaleExhale(e)
      })

      // Add the start label to the body
      outM = outM.body match {
        case Some(bodyBody) =>
          outM.copy(body = Some(bodyBody.copy(ss =
            helper.getStartLabel() +:
              bodyBody.ss)(bodyBody.pos, bodyBody.info, bodyBody.errT)))(
            outM.pos, outM.info, outM.errT)
        case None => return m
      }
      // add axioms for exhales inhales and heap writes.
      outM = outM.transform({
        case e : Exhale if !helper.checkIfPure(e) =>
          val fields = helper.extractFieldAcc(e)
          axiomGenerator.generateExhaleAxioms(e, fields)
        case i@ Inhale(_) if !helper.checkIfPure(i) =>
          val fields = helper.extractFieldAcc(i)
          axiomGenerator.generateInhaleAxioms(i, fields)
        case fa: FieldAssign =>
          axiomGenerator.generateHeapWriteAxioms(fa)
      })
      // add axioms for heap reads, using bottom up traversal
      outM = outM.transform({
        case s: Stmt  =>
          axiomGenerator.generateHeapReadAxioms(s)
      }, recurse = Traverse.BottomUp)
      outM
    }

    // Modify all methods
    val outMethods = p.methods.map(m => modifyMethod(m))
    // Modify the program
    p.copy(methods = outMethods)(p.pos, p.info, p.errT)
  }
}
