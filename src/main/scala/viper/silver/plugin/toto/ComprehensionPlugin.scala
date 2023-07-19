package viper.silver.plugin.toto

import fastparse.P
import viper.silver.ast.{FilePosition, IntLit, NoPosition, Program}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, PCall, PDomainType, PDomainTypeKinds, PExp, PIdnUse, PProgram, PSetType, PType}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractError, VerificationResult}

import scala.annotation.unused

class ComprehensionPlugin(@unused reporter: viper.silver.reporter.Reporter,
                          @unused logger: ch.qos.logback.classic.Logger,
                          @unused config: viper.silver.frontend.SilFrontendConfig,
                          fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{FP, keyword, exp, ParserExtension}

  private val comprehensionKeyword: String = "comp"

  // Fix the FP somewhere else
  def compOp[_: P]: P[((FilePosition, FilePosition), (PCall, PExp))] =
    FP(keyword(comprehensionKeyword) ~/ "[" ~/ fp.funcApp ~ "," ~ exp ~/ "]")

  def compDef[_:P]: P[(PMappingFieldReceiver, PExp)] =
    P("{") ~ mapRecVal ~ "|" ~ exp ~ "}"

  def comp[_:P]: P[PComprehension] =
    (compOp ~ compDef).map{
      case (pos, (op, opUnit), (mRF, parsedFilter)) =>
        PComprehension(op,opUnit,mRF,parsedFilter)(pos)
    }

  def mapRecVal[_:P]: P[PMappingFieldReceiver] =
    FP(fp.idnuse ~  "(" ~ fp.funcApp ~ "." ~ fp.idnuse ~ (P(",") ~ fp.actualArgList).? ~ ")").map{
      case (posTuple, (mappingFunc, receiverApp, field, mappingFuncArgs)) => PMappingFieldReceiver(
        PCall(mappingFunc, mappingFuncArgs.getOrElse(Seq()))(posTuple),
        field,
        receiverApp
      )(posTuple)
    }


  /** Called before any processing happened.
    *
    * @param input Source code as read from file
    * @param isImported Whether the current input is an imported file or the main file
    * @return Modified source code
    */
  override def beforeParse(input: String, isImported: Boolean) : String = {
    ParserExtension.addNewExpAtStart(comp(_))
    ParserExtension.addNewPreCondition(comp(_))
    ParserExtension.addNewPostCondition(comp(_))
    ParserExtension.addNewInvariantCondition(comp(_))
    input
  }

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram) : PProgram = {

    print(input)
    input
  }

  /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeTranslate(input: PProgram): PProgram = {
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
    val out = input.transform({
      case c@Comprehension(op, unit, mapping, field, receiver, filter) => unit
    })
    out
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
}
