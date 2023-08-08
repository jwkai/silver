package viper.silver.plugin.toto

import fastparse.P
import viper.silver.FastMessaging
import viper.silver.ast.pretty.FastPrettyPrinter.pretty
import viper.silver.ast.{DomainFuncApp, FilePosition, FuncApp, IntLit, NoPosition, Program}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, PCall, PDomain, PDomainFunction, PDomainType, PDomainTypeKinds, PExp, PFormalArgDecl, PIdnDef, PIdnUse, PProgram, PSetType, PType, PTypeVar, PTypeVarDecl, TypeChecker}
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

//  def mapRecVal[_:P]: P[PMappingFieldReceiver] =
//    FP(fp.idnuse ~  "(" ~ fp.funcApp ~ "." ~ fp.idnuse ~ (P(",") ~ fp.actualArgList).? ~ ")").map{
//      case (posTuple, (mappingFunc, receiverApp, field, mappingFuncArgs)) => PMappingFieldReceiver(
//        PCall(mappingFunc, mappingFuncArgs.getOrElse(Seq()))(posTuple),
//        field,
//        receiverApp
//      )(posTuple)
//    }

  def recVal[_: P]: P[PMappingFieldReceiver]   = {
    // Parse the mapping function with two possible syntaxes
    FP(fp.funcApp ~ "." ~ fp.idnuse).map{
      case (posTuple, (receiver, field)) => PMappingFieldReceiver(
        null,
        field,
        receiver
      )(posTuple)
    }
  }

  def mapRecVal[_: P]: P[PMappingFieldReceiver] = {
    FP(fp.idnuse ~ fp.parens(recVal ~ (P(",") ~ fp.actualArgList).?)).map{
      case (posTuple, (mappingFunc, (pMappingFieldReceiver, mappingFuncArgs))) =>
        pMappingFieldReceiver.copy(mapping =
          PCall(mappingFunc, mappingFuncArgs.getOrElse(Seq()))(posTuple))(posTuple)
    }
  }


  def mapRecBoth[_:P]: P[PMappingFieldReceiver] = {
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
//    ParserExtension.addNewPreCondition(comp(_))
//    ParserExtension.addNewPostCondition(comp(_))
//    ParserExtension.addNewInvariantCondition(comp(_))
    input
  }

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram) : PProgram = {
//    errors
    val newInput = input //TODO
    newInput
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

  final val compDomainKeyword = "Comp"
  final val compFunctionKeyword = "comp"

  final val receiverDomainKeyword = "Receiver"
  final val mappingDomainKeyword = "Mapping"
  final val operatorDomainKeyword = "Operator"



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

  private def addCompDomain(input: PProgram): PProgram = {
    val compDomainTypeVar0 = "A"
    val compDomainTypeVar1 = "V"
    val compDomainTypeVar2 = "B"

    // checks and add an Comp domain if doesn't exist
    if (checkCompExists(input)) {
      throw new Exception("Comp domain already exists. Implementing edits")
    }
    val noPosTuple = (NoPosition,NoPosition)
    val typVar0 = PTypeVarDecl(PIdnDef(compDomainTypeVar0)(noPosTuple))(noPosTuple)
    val typVar1 = PTypeVarDecl(PIdnDef(compDomainTypeVar1)(noPosTuple))(noPosTuple)
    val typVar2 = PTypeVarDecl(PIdnDef(compDomainTypeVar2)(noPosTuple))(noPosTuple)
    val compDomain = PDomain(PIdnDef(compDomainKeyword)(noPosTuple),
      Seq(typVar0, typVar1, typVar2), Seq(), Seq(), None)(noPosTuple, Seq())
//    val compInputRec = PFormalArgDecl(PIdnDef("r")(noPosTuple),)


    val receiverType = PDomainType(PIdnUse(receiverDomainKeyword)(noPosTuple),
      Seq(PTypeVar(compDomainTypeVar0)))(noPosTuple)
    val mappingType = PDomainType(PIdnUse(mappingDomainKeyword)(noPosTuple),
      Seq(PTypeVar(compDomainTypeVar1), PTypeVar(compDomainTypeVar2)))(noPosTuple)
    val operatorType = PDomainType(PIdnUse(operatorDomainKeyword)(noPosTuple),
      Seq(PTypeVar(compDomainTypeVar2)))(noPosTuple)
    val unitType = PTypeVar(compDomainTypeVar2)

    val compFuncArg0 = PFormalArgDecl(PIdnDef("r")(noPosTuple), receiverType)(noPosTuple)
    val compFuncArg1 = PFormalArgDecl(PIdnDef("m")(noPosTuple), mappingType)(noPosTuple)
    val compFuncArg2 = PFormalArgDecl(PIdnDef("op")(noPosTuple), operatorType)(noPosTuple)
    val compFuncArg3 = PFormalArgDecl(PIdnDef("u")(noPosTuple), unitType)(noPosTuple)

    val compFuncOutType = PDomainType(PIdnUse(compDomainKeyword)(noPosTuple),
      Seq(PTypeVar(compDomainTypeVar0),
        PTypeVar(compDomainTypeVar1),
        PTypeVar(compDomainTypeVar2)))(noPosTuple)

    val compFunc = PDomainFunction(PIdnDef(compFunctionKeyword)(noPosTuple),
      Seq(compFuncArg0, compFuncArg1, compFuncArg2, compFuncArg3), compFuncOutType, unique = false, None)(
      PIdnUse(compDomainKeyword)(noPosTuple))(noPosTuple, Seq())



  }

  private def checkCompFuncExists(input: PProgram): Boolean = {
    input.domains.find(d => d.idndef.name == compDomainKeyword) match {
      case Some(domain) =>
        domain.funcs.find(f => f.idndef.name == compFunctionKeyword) match {
          case Some(_) =>
            true
          case None =>
            false
        }
      case None =>
        throw new Exception("Should not get here.")
    }

  }


  private def checkCompExists(input: PProgram): Boolean = {
    input.domains.find(d => d.idndef.name == compDomainKeyword) match {
      case Some(value) =>
        val dTypeVars = value.typVars
        if (dTypeVars.length >= 3) {
          throw new Exception("Comp domain should have at least 3 type variables")
        }
        true
      case None =>
        false
    }
  }



}
