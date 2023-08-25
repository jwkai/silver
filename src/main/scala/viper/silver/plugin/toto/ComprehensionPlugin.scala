package viper.silver.plugin.toto

import fastparse.P
import viper.silver.FastMessaging
import viper.silver.ast.pretty.FastPrettyPrinter.pretty
import viper.silver.ast.{FilePosition, NoPosition, Program}
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser._
import viper.silver.plugin.toto.DomainsGenerator._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractError, VerificationResult}

import scala.annotation.unused

class ComprehensionPlugin(@unused reporter: viper.silver.reporter.Reporter,
                          @unused logger: ch.qos.logback.classic.Logger,
                          @unused config: viper.silver.frontend.SilFrontendConfig,
                          fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{FP, ParserExtension, exp, keyword}

  private val comprehensionKeyword: String = "comp"

  private val recKeyword: String = "receiver"
  private val opUnitKeyword: String = "unitOp"
  private val mapKeyword: String = "mapping"
  private val filterKeyword: String = "filter"

  // Fix the FP somewhere else
  def compOp[$: P]: P[((FilePosition, FilePosition), PCall)] =
    FP(keyword(comprehensionKeyword) ~/ "[" ~/ fp.funcApp ~/ "]")
//    FP(keyword(comprehensionKeyword) ~/ "[" ~/ fp.funcApp ~ "," ~ exp ~/ "]")

  def compDef[$: P]: P[(PMappingFieldReceiver, PExp)] =
    P("{") ~ mapRecBoth ~ "|" ~ exp ~ "}"

  def comp[$: P]: P[PComprehension] =
    (compOp ~ compDef).map{
      case (pos, unitOp, (mRF, parsedFilter)) =>
        PComprehension(unitOp,mRF,parsedFilter)(pos)
    }


  def funDef[$:P]: P[PFunInline] =
    FP(keyword("fun") ~ fp.formalArgList ~ "::" ~ fp.exp).map{
      case (pos, (args, body)) => PFunInline(args, body)(pos)
    }

  def recDef[$:P]: P[PReceiver] =
    FP(keyword(recKeyword) ~ fp.idndef ~ fp.parens(fp.formalArgList) ~ fp.parens(funDef)).map {
      case (pos, (name, args, body)) => PReceiver(name, args, body)(pos)
    }

  def opUnitDef[$:P]: P[POperator] =
    FP(keyword(opUnitKeyword) ~ fp.idndef ~ fp.parens(fp.formalArgList) ~ fp.parens(
      exp ~ "," ~ funDef)).map {
      case (pos, (name, args, (unitdef, fundef))) => POperator(name, args, unitdef, fundef)(pos)
    }

  def mappingDef[$:P]: P[PMapping] =
    FP(keyword(mapKeyword) ~ fp.idndef ~ fp.parens(fp.formalArgList) ~ fp.parens(funDef)).map {
      case (pos, (name, args, body)) => PMapping(name, args, body)(pos)
    }

  def filterDef[$:P]: P[PFilter] =
    FP(keyword(filterKeyword) ~ fp.idndef ~ fp.parens(fp.formalArgList) ~ fp.parens(funDef)).map {
      case (pos, (name, args, body)) => PFilter(name, args, body)(pos)
    }






//  def mapRecVal[_:P]: P[PMappingFieldReceiver] =
//    FP(fp.idnuse ~  "(" ~ fp.funcApp ~ "." ~ fp.idnuse ~ (P(",") ~ fp.actualArgList).? ~ ")").map{
//      case (posTuple, (mappingFunc, receiverApp, field, mappingFuncArgs)) => PMappingFieldReceiver(
//        PCall(mappingFunc, mappingFuncArgs.getOrElse(Seq()))(posTuple),
//        field,
//        receiverApp
//      )(posTuple)
//    }

  def recVal[$: P]: P[PMappingFieldReceiver]   = {
    // Parse the mapping function with two possible syntaxes
    FP(fp.funcApp ~ "." ~ fp.idnuse).map{
      case (posTuple, (receiver, field)) => PMappingFieldReceiver(
        null,
        field,
        receiver
      )(posTuple)
    }
  }

  def mapRecVal[$: P]: P[PMappingFieldReceiver] = {
    FP(fp.idnuse ~ fp.parens(recVal ~ (P(",") ~ fp.actualArgList).?)).map{
      case (posTuple, (mappingFunc, (pMappingFieldReceiver, mappingFuncArgs))) =>
        pMappingFieldReceiver.copy(mapping =
          PCall(mappingFunc, mappingFuncArgs.getOrElse(Seq()))(posTuple))(posTuple)
    }
  }


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
//    errors
    val domainsToAdd = Seq(
      compDomainString(),
      receiverDomainString(),
      opDomainString(),
      mappingDomainString()).map(parseDomainString(_))// :+ convertUserDefs(input.extensions)

    val newInput = input.copy(
      domains = input.domains ++ domainsToAdd)(input.pos)
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
    input
  }

  /** Called after parse AST has been translated into the normal AST but before methods to verify are filtered.
    * In [[viper.silver.frontend.SilFrontend]] this step is confusingly called doTranslate.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeMethodFilter(input: Program) : Program = {
    input
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
    newInput = newInput.transform( {
      case c@ AEvalComp(_, _) =>
        c.toViper(newInput)
    })
    print(pretty(newInput))
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
}

object ComprehensionPlugin {

  def makeDomainType(name: String, typeArgs: Seq[PType]): PDomainType = {
    val noPosTuple = (NoPosition,NoPosition)
    val outType = PDomainType(PIdnUse(name)(noPosTuple), typeArgs)(noPosTuple)
    outType.kind = PDomainTypeKinds.Domain
    outType
  }

  def makeSetType(typeArg: PType): PSetType = {
    val noPosTuple = (NoPosition,NoPosition)
    val outType = PSetType(typeArg)(noPosTuple)
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
                s"Expected ${expected.toString}, but found ${reportedActual}")
            } else {
              t.messages ++= FastMessaging.message(exp,
                s"Expected type ${expected.toString}, but found ${reportedActual} at the expression at ${exp.pos._1}")
            }
          case None =>
            t.typeError(exp)
        }
      }
    }
  }



}
