package viper.silver.plugin.toto

import fastparse.{NoCut, P}
import viper.silver.FastMessaging
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.pretty
import viper.silver.parser.FastParserCompanion
import viper.silver.parser.FastParser
import viper.silver.parser._
import viper.silver.plugin.toto.ComprehensionPlugin.{addInlinedAxioms, defaultMappingIden}
import viper.silver.plugin.toto.DomainsGenerator._
import viper.silver.plugin.toto.ast.{ACompApply, AFHeap, fHeapInfo}
import viper.silver.plugin.toto.parser.PComprehension.PComprehensionKeywordType
import viper.silver.plugin.toto.parser._
import viper.silver.plugin.toto.util.AxiomHelper
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractError, VerificationResult}

import scala.annotation.unused

class ComprehensionPlugin(@unused reporter: viper.silver.reporter.Reporter,
                          @unused logger: ch.qos.logback.classic.Logger,
                          @unused config: viper.silver.frontend.SilFrontendConfig,
                          fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{ParserExtension, funcApp, exp, argList, commaSeparated, formalArg, fieldAccess, foldPExp, idndef, idnref, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, PositionParsing, reservedKw, whitespace}

  private var setOperators: Set[PCompOperator] = Set()

  /** Parser for comprehension statements. */
  def compOp[$: P]: P[(PComprehensionKeywordType, PCall)] =
    P(P(PComprehensionKeyword) ~/ "[" ~ funcApp ~ "]")

  def compDef[$: P]: P[(PMappingFieldReceiver, PExp)] =
    P(P("(") ~/ mapRecBoth ~ "|" ~ exp ~ ")")

  def comp[$: P]: P[PComprehension] =
    P(
      (compOp ~/ compDef) map {
        case (kw, op, (mRf, f)) => (kw, op, mRf, f)
      } map (PComprehension.apply _).tupled
    ).pos

  def funDef[$:P]: P[PFunInline] =
    P(
      (P(PFunInlineKeyword) ~ commaSeparated(formalArg) ~ "::" ~ exp) map {
        case (kw, args, body) => (kw, args.toSeq, body)
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
    P(
      (funcApp ~~ fieldAccess map { case (fa, ss) => foldPExp(fa, Seq(ss)) }) map {
        case p@PFieldAccess(rcv, _, idnref) => (
          defaultMappingIden(p.pos),
          idnref,
          rcv.asInstanceOf[PCall]
        )
      } map (PMappingFieldReceiver.apply _).tupled
    ).pos

  // Parser with mapping
  def mapRecVal[$: P]: P[PMappingFieldReceiver] =
    P(
      (idnref[$, PCallable] ~ (recVal ~ (P(",") ~ exp.rep(sep = ",")).?).parens) map {
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

  // Allow both with and without Mapping function
  def mapRecBoth[$: P]: P[PMappingFieldReceiver] =
    P(NoCut(recVal) | mapRecVal)

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
    input
  }

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram) : PProgram = {

    if (input.filterMembers {
      case _: PComprehension | _: PReceiver | _: PMapping | _: PFilter | _: PCompOperator => true
      case _ => false
    }.members.isEmpty) {
      input
    } else {
      val domainsToAdd = Seq(
        compDomainString(),
        receiverDomainString(),
        opDomainString(),
        mappingDomainString(),
        setEditDomainString()
      ).map(parseDomainString) // :+ convertUserDefs(input.extensions)

      val newInput = input.copy(
        members = input.members ++ domainsToAdd
      )(input.pos, input.localErrors)
      newInput
    }
  }

  /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeTranslate(input: PProgram): PProgram = {
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
    var newInput = addInlinedAxioms(input)
    newInput = newInput.transform({
      case e@Assume(a) => Inhale(a)(e.pos, e.info, e.errT)
    })
    print(pretty(newInput) + "\n\n")
    newInput
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

//  def typeCheckCustom(t: TypeChecker, exp: PExp, oexpected: Option[PType],
//                       doCheckInternal : Boolean = true,
//                       customMessage: Option[String]): Unit = {
//    if (doCheckInternal) {
//      t.checkInternal(exp)
//    }
//    if (exp.typ.isValidOrUndeclared && exp.typeSubstitutions.nonEmpty) {
//      val etss = oexpected match {
//        case Some(expected) if expected.isValidOrUndeclared => exp.typeSubstitutions.flatMap(_.add(exp.typ, expected).toOption)
//        case _ => exp.typeSubstitutions
//      }
//      if (etss.nonEmpty) {
//        val ts = t.selectAndGroundTypeSubstitution(exp, etss)
//        exp.forceSubstitution(ts)
//      } else {
//        oexpected match {
//          case Some(expected) =>
//            val reportedActual = if (exp.typ.isGround) {
//              exp.typ
//            } else {
//              exp.typ.substitute(t.selectAndGroundTypeSubstitution(exp, exp.typeSubstitutions))
//            }
//            if (customMessage.nonEmpty) {
//              t.messages ++= FastMessaging.message(exp, customMessage.get +
//                s"Expected ${expected.toString()}, but found $reportedActual")
//            } else {
//              t.messages ++= FastMessaging.message(exp,
//                s"Expected type ${expected.toString()}, but found $reportedActual at the expression at ${exp.pos._1}")
//            }
//          case None => t.typeError(exp)
//        }
//      }
//    }
//  }

  def addInlinedAxioms(p: Program) : Program = {
    def modifyMethod(m: Method) : Method = {
      val axiomGenerator = new InlineAxiomGenerator(p, m.name)

      // If no comprehension is used in a method, keep the method the same
      if (axiomGenerator.compDeclsUsed.isEmpty) { return m }

      val helper = new AxiomHelper(p)

      // Convert all method calls to inhales and exhales
      var outM: Method = m.transform({
        case e: MethodCall => axiomGenerator.convertMethodToInhaleExhale(e)
      })

      // Add the start label to the body
      outM = outM.body match {
        case Some(mBody) =>
          outM.copy(body =
            Some(mBody.copy(ss =
              axiomGenerator.getOldLabel +: mBody.ss
            )(mBody.pos, mBody.info, mBody.errT))
          )(outM.pos, outM.info, outM.errT)
        case None => return m
      }

      // Add axioms for exhales, inhales and heap writes, tracking fHeap insertions
      def addAxiomsToBody(): PartialFunction[Node, Node] = {
        case e: Exhale =>
          if (!helper.checkIfPure(e)) {
            val fields = helper.extractFieldAcc(e)
            axiomGenerator.generateExhaleAxioms(e, fields)
          } else {
            e.withMeta(e.pos, MakeInfoPair(e.info, fHeapInfo(axiomGenerator.getCurrentfHeap)), e.errT)
          }
        case i: Inhale =>
          if (!helper.checkIfPure(i)) {
            val fields = helper.extractFieldAcc(i)
            axiomGenerator.generateInhaleAxioms(i, fields)
          } else {
            i.withMeta(i.pos, MakeInfoPair(i.info, fHeapInfo(axiomGenerator.getCurrentfHeap)), i.errT)
          }
        case fa: FieldAssign =>
          axiomGenerator.generateHeapWriteAxioms(fa)
        case l@Label(name, _) =>
          axiomGenerator.mapUserLabelToCurrentAFHeap(name)
          l
        case a: Assert =>
          a.withMeta(a.pos, MakeInfoPair(a.info, fHeapInfo(axiomGenerator.getCurrentfHeap)), a.errT)
        case a: Assume =>
          a.withMeta(a.pos, MakeInfoPair(a.info, fHeapInfo(axiomGenerator.getCurrentfHeap)), a.errT)
        case i: If =>
          val fHeapOrig = axiomGenerator.getCurrentfHeap
          i.copy(
            thn = i.thn.transform(addAxiomsToBody()),
            els = i.els.transform(addAxiomsToBody())
          )(i.pos, MakeInfoPair(i.info, fHeapInfo(fHeapOrig)), i.errT)
        case w: While =>
          val fHeapOrig = axiomGenerator.getCurrentfHeap
          w.copy(
            body = w.body.transform(addAxiomsToBody())
          )(w.pos, MakeInfoPair(w.info, fHeapInfo(fHeapOrig)), w.errT)
      }
      outM = outM.body match {
        case Some(mBody) =>
          outM.copy(body =
            Some(mBody.transform(addAxiomsToBody()))
          )(outM.pos, outM.info, outM.errT)
        case None => return m
      }

      // Now, transform ACompApply nodes in context of fHeap annotations
      outM = outM.body match {
        case Some(mBody) =>
          outM.copy(body =
            Some(mBody.transformWithContext[AFHeap]({
              case (n@NodeWithFHeapInfo(fHeapInfo(fh)), _) =>
                (n, fh)
              case (lo@LabelledOld(exp, labelName), fh) =>
                exp match {
                  case ca: ACompApply =>
                    val cap = ca.copy()(lo.pos, lo.info, lo.errT)
                    cap.fHeap = Some(axiomGenerator.getAFHeapFromUserLabel(labelName))
                    (cap.toViper(p), fh)
                  case _ =>
                    val newLO = LabelledOld(
                      exp.transform({
                        case ca: ACompApply =>
                          ca.fHeap = Some(axiomGenerator.getAFHeapFromUserLabel(labelName))
                          ca.toViper(p)
                      }),
                      labelName
                    )(lo.pos, lo.info, lo.errT)
                    (newLO, fh)
                }
              case (o@Old(exp), fh) =>
                exp match {
                  case ca: ACompApply =>
                    val cap = ca.copy()(o.pos, o.info, o.errT)
                    cap.fHeap = Some(axiomGenerator.getOldfHeap)
                    (cap.toViper(p), fh)
                  case _ =>
                    val newO = Old(
                      exp.transform({
                        case ca: ACompApply =>
                          ca.fHeap = Some(axiomGenerator.getOldfHeap)
                          ca.toViper(p)
                      })
                    )(o.pos, o.info, o.errT)
                    (newO, fh)
                }
              case (ca: ACompApply, fh) =>
                ca.fHeap = Some(fh)
                (ca.toViper(p), fh)
            }, initialContext = axiomGenerator.getOldfHeap))
          )(outM.pos, outM.info, outM.errT)
        case None => return m
      }

      // TODO: figure out why this doesn't work...
//      def stripfHeapInfo(n: Node) = {
//        val nMeta = n.meta.copy(_2 = n.meta._2.removeUniqueInfo[fHeapInfo])
//        n.withMeta(nMeta)
//      }
//      outM = outM.body match {
//        case Some(mBody) =>
//          outM.copy(body =
//            Some(mBody.transform({
//              case n@NodeWithFHeapInfo(fHeapInfo(_)) =>
//                stripfHeapInfo(n)
//            }))
//          )(outM.pos, outM.info, outM.errT)
//        case None => return m
//      }

      val setFHeapApply: PartialFunction[Node, Node] = {
        case lo@Old(exp) =>
          exp match {
            case ca: ACompApply =>
              val c = ca.copy()(lo.pos, lo.info, lo.errT)
              c.fHeap = Some(axiomGenerator.getOldfHeap)
              c.toViper(p)
            case _ =>
              Old(
                exp.transform({
                  case ca: ACompApply =>
                    ca.fHeap = Some(axiomGenerator.getOldfHeap)
                    ca.toViper(p)
                })
              )(lo.pos, lo.info, lo.errT)
          }
        case ca: ACompApply =>
          ca.fHeap = Some(axiomGenerator.getCurrentfHeap)
          ca.toViper(p)
      }

      // Add heap-dependent function to pre-/post-conditions and loop invariants
      outM = outM.copy(
        pres =
          outM.pres.map(pre => pre.transform(setFHeapApply, recurse = Traverse.Innermost)),
        posts =
          outM.posts.map(post => post.transform(setFHeapApply, recurse = Traverse.Innermost)),
        body =
          outM.body match {
            case Some(bodyD) =>
              Some(bodyD.transform({
                // TODO: deal with tricky invariant situations -
                //  symbolic state (fHeap) is not well-defined at entry.
                //  It's possible to manually convert these invariants:
                //  - Add assert (in old fHeap) prior to the while statement,
                //    and (in current fHeap) the end of the while body.
                //  - Add assumes (in current fHeap) at start of while body
                //    and immediately after the while statement.
                case w@While(cond, invs, body) =>
                  While(cond,
                    invs.map(inv => inv.transform(setFHeapApply)),
                    body)(w.pos, w.info, w.errT)},
                recurse = Traverse.BottomUp))
            case None => None
          }
      )(outM.pos, outM.info, outM.errT)

      outM
    }

    // Modify all methods
    val outMethods = p.methods.map(m => modifyMethod(m))

    // Modify the program
    p.copy(methods = outMethods)(p.pos, p.info, p.errT)
  }
}

object NodeWithFHeapInfo {
  def unapply(node : Node) : Option[fHeapInfo] = node match {
    case i: Infoed => i.info.getUniqueInfo[fHeapInfo]
    case _ => None
  }
}