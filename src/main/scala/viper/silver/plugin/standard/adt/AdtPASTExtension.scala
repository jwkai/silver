// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.ast.utility.lsp._
import viper.silver.parser._
import viper.silver.plugin.standard.adt.PAdtConstructor.findAdtConstructor

import scala.annotation.unused
import scala.util.{Success, Try}
// import viper.silver.ast.utility.lsp.GotoDefinition
import viper.silver.ast.utility.lsp.SymbolKind

/**
  * Keywords used to define ADT's
  */
case object PAdtKeyword extends PKw("adt") with PKeywordLang
case object PDerivesKeyword extends PKw("derives") with PKeywordLang
case object PWithoutKeyword extends PKw("without") with PKeywordLang

case class PAdt(annotations: Seq[PAnnotation], adt: PReserved[PAdtKeyword.type], idndef: PIdnDef, typVars: Option[PDelimited.Comma[PSym.Bracket, PTypeVarDecl]], c: PAdtSeq[PAdtConstructor], derive: Option[PAdtDeriving])
               (val pos: (Position, Position)) extends PExtender with PSingleMember with PGlobalDeclaration with PPrettySubnodes with HasFoldingRanges { // with PSemanticDeclaration with PGlobalSymbol
  def typVarsSeq: Seq[PTypeVarDecl] = typVars.map(_.inner.toSeq).getOrElse(Nil)
  def constructors: Seq[PAdtConstructor] = c.inner

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      constructors foreach (_.typecheck(t, n))
    }
    // Check that formalArg identifiers among all constructors are unique
    val allFormalArgs = constructors flatMap (_.formalArgs collect { case fad: PFormalArgDecl => fad })
    val duplicateArgs = allFormalArgs.groupBy(_.idndef.name).collect { case (_, ys) if ys.size > 1 => ys.tail }.toSeq
    t.messages ++= duplicateArgs.flatMap { args => args.flatMap { arg =>
      FastMessaging.message(arg.idndef, "Duplicate argument identifier `" + arg.idndef.name + "' among adt constructors at " + arg.idndef.pos._1)
    }}

    // Check validity blocklisted identifiers
    derive.foreach(_.derivingInfos.inner.foreach { di =>
      val diff = di.without.map(without => {
        val possibleFields =  allFormalArgs.map(_.toIdnUse.name).toSet
        without.blockList.toSeq.filterNot(blockedField => possibleFields(blockedField.name))
      }).getOrElse(Nil)
      if (diff.nonEmpty) {
        t.messages ++= FastMessaging.message(diff.head, "Invalid identifier `" + diff.head.name + "' at " + diff.head.pos._1)
      }
    })
    // Check duplicate deriving infos
    val duplicateDerivingInfo = derive.toSeq.flatMap(_.derivingInfos.inner.groupBy(_.idnuse).collect { case (_, ys) if ys.size > 1 => ys.head })
    t.messages ++= duplicateDerivingInfo.flatMap { di =>
      FastMessaging.message(di.idnuse, "Duplicate derivation of function `" + di.idnuse.name + "' at " + di.idnuse.pos._1)
    }

    derive.foreach(_.typecheck(t, n))

    None
  }

  override def translateMemberSignature(t: Translator): Adt = {

    Adt(
      idndef.name,
      null,
      typVarsSeq map (t => TypeVar(t.idndef.name)),
      derive.toSeq.flatMap(_.derivingInfos.inner.map { a =>
        val without = a.without.toSet
        (a.idnuse.name, (if (a.param.nonEmpty) Some(t.ttyp(a.param.get.inner)) else None, without.flatMap(_.blockList.toSeq.map(_.name))))
      }).toMap
    )(t.liftPos(this), Translator.toInfo(this.annotations, this))
  }

  override def translateMember(t: Translator): Member = {

    // In a first step translate constructor signatures
    constructors map (c => {
      val cc = c.translateMemberSignature(t)
      t.getMembers().put(c.idndef.name, cc)
    })

    val a = PAdt.findAdt(idndef, t)
    val aa = a.copy(constructors = constructors map (_.translateMember(t)))(a.pos, a.info, a.errT)
    t.getMembers()(a.name) = aa
    aa
  }

  /**
    * This is a helper method that creates an AdtType from the ADT's signature.
    *
    * @return An AdtType that corresponds to the ADTs signature
    */
  def getAdtType: PAdtType = {
    val adtType = PAdtType(PIdnRef(idndef.name)(NoPosition, NoPosition), typVars map (tv => tv.update(tv.inner.toSeq map { t =>
      val typeVar = PDomainType(PIdnRef(t.idndef.name)(NoPosition, NoPosition), None)(NoPosition, NoPosition)
      typeVar.kind = PDomainTypeKinds.TypeVar
      typeVar
    })))(NoPosition, NoPosition)
    adtType.kind = PAdtTypeKinds.Adt
    adtType
  }

  override def tokenType = TokenType.Enum
  override def symbolKind = SymbolKind.Enum
  def tvsPretty: String = typVars.map(_.pretty).getOrElse("")
  override def hint = {
    s"${adt.pretty}${idndef.pretty}$tvsPretty"
  }
  override def getFoldingRanges: Seq[FoldingRange] = RangePosition(this).map(FoldingRange(_)).toSeq
  // override def withChildren(children: Seq[Any], pos: Option[(Position, Position)] = None, forceRewrite: Boolean = false): this.type = {
  //   if (!forceRewrite && this.children == children && pos.isEmpty)
  //     this
  //   else {
  //     assert(children.length == 6, s"PAdt : expected length 6 but got ${children.length}")
  //     val first = children(0).asInstanceOf[Seq[PAnnotation]]
  //     val second = children(1).asInstanceOf[PReserved[PAdtKeyword.type]]
  //     val third = children(2).asInstanceOf[PIdnDef]
  //     val fourth = children(3).asInstanceOf[Option[PDelimited.Comma[PSym.Bracket, PTypeVarDecl]]]
  //     val fifth = children(4).asInstanceOf[PAdtSeq[PAdtConstructor]]
  //     val sixth = children(5).asInstanceOf[Option[PAdtDeriving]]
  //     PAdt(first, second, third, fourth, fifth, sixth)(pos.getOrElse(this.pos)).asInstanceOf[this.type]
  //   }
  // }
  override def completionScope: Map[SuggestionScope,Byte] = Map(TypeScope -> 0)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Enum
  override def description: String = "Adt"
}

object PAdt {
  /**
    * This is a helper method helper that can be called if one knows which 'id' refers to an ADT
    *
    * @param id identifier of the ADT
    * @param t  translator unit
    * @return the corresponding ADT object
    */
  def findAdt(id: PIdentifier, t: Translator): Adt = t.getMembers()(id.name).asInstanceOf[Adt]

}

case class PAdtSeq[T <: PNode](seq: PGrouped[PSym.Brace, Seq[T]])(val pos: (Position, Position)) extends PExtender {
  def inner: Seq[T] = seq.inner
  override def pretty = s"${seq.l.pretty}\n  ${seq.inner.map(_.pretty).mkString("  \n")}\n${seq.r.pretty}"
}

case class PAdtConstructor(annotations: Seq[PAnnotation], idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl])
                          (var adt: PAdt)(val pos: (Position, Position)) extends PExtender with PSingleMember with PGlobalCallableNamedArgs with PPrettySubnodes with PLspAnyFunction {
  def adtName: PIdnRef = PIdnRef(adt.idndef.name)(adt.idndef.pos)
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this.formalArgs foreach (a => t.check(a.typ))

    // Check if there are name clashes for the corresponding discriminator, if so we raise a type-check error
    Try {
      n.definition(t.curMember)(PIdnRef("is" + idndef.name)(idndef.pos))
    } match {
      case Success(Some(decl)) =>
        t.messages ++= FastMessaging.message(idndef, "corresponding adt discriminator identifier `" + decl.idndef.name + "' at " + idndef.pos._1 + " is shadowed at " + decl.idndef.pos._1)
      case _ =>
    }
    None
  }

  override def translateMemberSignature(t: Translator): AdtConstructor = {
    val adt = PAdt.findAdt(adtName, t)
    AdtConstructor(
      adt,
      idndef.name,
      formalArgs map { arg => LocalVarDecl(arg.idndef.name, t.ttyp(arg.typ))(t.liftPos(arg.idndef)) }
    )(t.liftPos(this), Translator.toInfo(annotations, this))
  }

  override def translateMember(t: Translator): AdtConstructor = {
    findAdtConstructor(idndef, t)
  }

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)] = None, forceRewrite: Boolean = false): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 3, s"PAdtConstructor : expected length 3 but got ${children.length}")
      val first = children(0).asInstanceOf[Seq[PAnnotation]]
      val second = children(1).asInstanceOf[PIdnDef]
      val third = children(2).asInstanceOf[PDelimited.Comma[PSym.Paren, PFormalArgDecl]]
      PAdtConstructor(first, second, third)(this.adt)(pos.getOrElse(this.pos)).asInstanceOf[this.type]
    }
  }

  override def c: PSym.Colon = PReserved.implied(PSym.Colon)
  override def resultType: PType = adt.getAdtType

  override def tokenType = TokenType.EnumMember
  override def symbolKind = SymbolKind.EnumMember
  override def keyword = adt.adt
  override def bodyRange: Option[RangePosition] = None
  override def returnString: Option[String] = Some(s": ${adt.idndef.pretty}${adt.tvsPretty}")
  override def pres = PDelimited.empty
  override def posts = PDelimited.empty
  // TODO:
  // override def getHoverHints: Seq[HoverHint] = super.getHoverHints ++
  //   Seq(HoverHint(s"```\nadt ${adtName.pretty}.is${idndef.name}: Bool\n```", None, SelectionBoundKeyword("is" + idndef.name))) ++
  //   formalArgs.map(arg => HoverHint(s"\n```adt ${adtName.pretty}.${arg.idndef.pretty}: ${arg.typ.pretty}\n```", None, SelectionBoundKeyword(arg.idndef.name)))
  override def completionScope: Map[SuggestionScope,Byte] = Map(ExpressionScope -> 0, StatementScope -> -50)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.EnumMember
  override def description: String = "Adt Constructor"
}

object PAdtConstructor {
  /**
    * This is a helper method helper that can be called if one knows which 'id' refers to an ADTConstructor
    *
    * @param id identifier of the ADT constructor
    * @param t  translator unit
    * @return the corresponding ADTConstructor object
    */
  def findAdtConstructor(id: PIdentifier, t: Translator): AdtConstructor = t.getMembers()(id.name).asInstanceOf[AdtConstructor]
}

case class PAdtConstructors1(seq: PGrouped[PSym.Brace, Seq[PAdtConstructor1]])(val pos: (Position, Position))
case class PAdtConstructor1(annotations: Seq[PAnnotation], idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], s: Option[PSym.Semi])(val pos: (Position, Position))

case class PAdtDeriving(k: PReserved[PDerivesKeyword.type], derivingInfos: PAdtSeq[PAdtDerivingInfo])(val pos: (Position, Position)) extends PExtender with PPrettySubnodes {
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    derivingInfos.inner.foreach(_.typecheck(t, n))
    None
  }
}

case class PAdtWithout(k: PReserved[PWithoutKeyword.type], blockList: PDelimited[PAdtFieldRef, PSym.Comma])(val pos: (Position, Position)) extends PExtender with PPrettySubnodes

case class PAdtDerivingInfo(idnuse: PIdnRef, param: Option[PGrouped[PSym.Bracket, PType]], without: Option[PAdtWithout])(val pos: (Position, Position)) extends PExtender with PPrettySubnodes {

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    param.map(_.inner).foreach(t.check)
    None
  }
}

case class PAdtType(adt: PIdnRef, args: Option[PDelimited.Comma[PSym.Bracket, PType]])
                   (val pos: (Position, Position)) extends PExtender with PGenericType with HasSemanticHighlights {

  var kind: PAdtTypeKinds.Kind = PAdtTypeKinds.Unresolved

  def typeArgs = args.map(_.inner.toSeq).getOrElse(Nil)
  override def genericName: String = adt.name
  override def typeArguments: Seq[PType] = typeArgs
  override def isValidOrUndeclared: Boolean = (kind == PAdtTypeKinds.Adt || isUndeclared) && typeArgs.forall(_.isValidOrUndeclared)

  override def substitute(ts: PTypeSubstitution): PType = {
    require(kind == PAdtTypeKinds.Adt || isUndeclared)
    val oldArgs = typeArgs
    val newArgs = oldArgs map (a => a.substitute(ts))
    if (oldArgs == newArgs)
      return this

    val newAdtType = PAdtType(adt, args.map(a => a.update(newArgs)))((NoPosition, NoPosition))
    newAdtType.kind = PAdtTypeKinds.Adt
    newAdtType
  }

  def isUndeclared: Boolean = kind == PAdtTypeKinds.Undeclared

  override def subNodes: Seq[PType] = typeArgs

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this match {
      case at@PAdtType(_, _) if at.isResolved => None
      /* Already resolved, nothing left to do */
      case at@PAdtType(adt, args) =>
        assert(!at.isResolved, "Only yet-unresolved adt types should be type-checked and resolved")

        typeArgs foreach t.check

        var x: Any = null

        try {
          x = t.names.definition(t.curMember)(adt).get
        } catch {
          case _: Throwable =>
        }

        x match {
          case PAdt(_, _, _, typVars, _, _) =>
            t.ensure(args.map(_.inner.length) == typVars.map(_.inner.length), this, "wrong number of type arguments")
            at.kind = PAdtTypeKinds.Adt
            None
          case _ =>
            at.kind = PAdtTypeKinds.Undeclared
            Option(Seq(s"found undeclared type ${at.adt.name}"))
        }
    }
  }

  def isResolved: Boolean = kind != PAdtTypeKinds.Unresolved

  override def translateType(t: Translator): Type = {
    t.getMembers().get(adt.name) match {
      case Some(d) =>
        val adt = d.asInstanceOf[Adt]
        val typVarMapping = adt.typVars zip (typeArgs map t.ttyp)
        AdtType(adt, typVarMapping.toMap)
      case None => sys.error("undeclared adt type")
    }
  }

  override def withTypeArguments(s: Seq[PType]): PAdtType =
    if (s.length == 0 && args.isEmpty) this else copy(args = Some(args.get.update(s)))(pos)

  override def getSemanticHighlights: Seq[SemanticHighlight] =
    RangePosition(adt).map(sp => SemanticHighlight(sp, TokenType.Enum)).toSeq
}

object PAdtTypeKinds {
  trait Kind

  case object Unresolved extends Kind

  case object Adt extends Kind

  case object Undeclared extends Kind
}

/** Common trait for ADT operator applications * */
sealed trait PAdtOpApp extends PExtender with POpApp {
  // Following fields are set during resolving, respectively in the typecheck method below
  var adt: PAdt = null
  var adtTypeRenaming: Option[PTypeRenaming] = None
  var adtSubstitution: Option[PTypeSubstitution] = None
  var _extraLocalTypeVariables: Set[PDomainType] = Set()

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = PAdtOpApp.typecheck(this)(t, n)

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(this, Some(expected))
    None
  }

  override def forceSubstitution(ots: PTypeSubstitution): Unit = {

    val ts = adtTypeRenaming match {
      case Some(dtr) =>
        val s3 = PTypeSubstitution(dtr.mm.map(kv => kv._1 -> (ots.get(kv._2) match {
          case Some(pt) => pt
          case None => PTypeSubstitution.defaultType
        })))
        assert(s3.m.keySet == dtr.mm.keySet)
        assert(s3.m.forall(_._2.isGround))
        adtSubstitution = Some(s3)
        dtr.mm.values.foldLeft(ots)(
          (tss, s) => if (tss.contains(s)) tss else tss.add(s, PTypeSubstitution.defaultType).toOption.get)
      case _ => ots
    }
    super.forceSubstitution(ts)
  }

  override def extraLocalTypeVariables: Set[PDomainType] = _extraLocalTypeVariables

}

object PAdtOpApp {
  /**
    * This method mirrors the functionality in Resolver.scala that handles operation applications, except that it is
    * adapted to work for ADT operator applications.
    */
  def typecheck(poa: PAdtOpApp)(t: TypeChecker, @unused n: NameAnalyser): Option[Seq[String]] = {

    def getFreshTypeSubstitution(tvs: Seq[PDomainType]): PTypeRenaming =
      PTypeVar.freshTypeSubstitutionPTVs(tvs)

    // Checks that a substitution is fully reduced (idempotent)
    def refreshWith(ts: PTypeSubstitution, rts: PTypeRenaming): PTypeSubstitution = {
      require(ts.isFullyReduced)
      require(rts.isFullyReduced)
      new PTypeSubstitution(ts map (kv => rts.rename(kv._1) -> kv._2.substitute(rts)))
    }

    var extraReturnTypeConstraint: Option[PType] = None

    if (poa.typeSubstitutions.isEmpty) {
      poa.args.foreach(t.checkInternal)
      var nestedTypeError = !poa.args.forall(a => a.typ.isValidOrUndeclared)
      if (!nestedTypeError) {
        poa match {
          case pcc@PConstructorCall(constr, _, typeAnnotated) =>
            typeAnnotated match {
              case Some((_, ta)) =>
                t.check(ta)
                if (!ta.isValidOrUndeclared) nestedTypeError = true
              case None =>
            }

            if (!nestedTypeError) {
              val ac = t.names.definition(t.curMember)(constr).get.asInstanceOf[PAdtConstructor]
              pcc.constructor = ac
              t.ensure(ac.formalArgs.size == pcc.args.size, pcc, "wrong number of arguments")
              val adt = t.names.definition(t.curMember)(ac.adtName).get.asInstanceOf[PAdt]
              pcc.adt = adt
              val fdtv = PTypeVar.freshTypeSubstitution((adt.typVarsSeq map (tv => tv.idndef.name)).distinct) //fresh domain type variables
              pcc.adtTypeRenaming = Some(fdtv)
              pcc._extraLocalTypeVariables = (adt.typVarsSeq map (tv => PTypeVar(tv.idndef.name))).toSet
              extraReturnTypeConstraint = pcc.typeAnnotated.map(_._2)
            }

          case pdc@PDestructorCall(_, _, name) =>
            pdc.args.head.typ match {
              case at: PAdtType =>
                val adt = t.names.definition(t.curMember)(at.adt).get.asInstanceOf[PAdt]
                pdc.adt = adt
                val matchingConstructorArgs: Seq[PFormalArgDecl] = adt.constructors flatMap (c => c.formalArgs.collect { case fad@PFormalArgDecl(idndef, _, _) if idndef.name == name.name => fad })
                if (matchingConstructorArgs.nonEmpty) {
                  pdc.matchingConstructorArg = matchingConstructorArgs.head
                  name.decl = Some(matchingConstructorArgs.head)
                  val fdtv = PTypeVar.freshTypeSubstitution((adt.typVarsSeq map (tv => tv.idndef.name)).distinct) //fresh domain type variables
                  pdc.adtTypeRenaming = Some(fdtv)
                  pdc._extraLocalTypeVariables = (adt.typVarsSeq map (tv => PTypeVar(tv.idndef.name))).toSet
                } else {
                  nestedTypeError = true
                  t.messages ++= FastMessaging.message(pdc, "no matching destructor found")
                }
              case _ =>
                nestedTypeError = true
                t.messages ++= FastMessaging.message(pdc, "expected an adt as receiver")
            }

          case pdc@PDiscriminatorCall(_, _, _, name) =>
            t.names.definition(t.curMember)(name) match {
              case Some(ac: PAdtConstructor) =>
                val adt = t.names.definition(t.curMember)(ac.adtName).get.asInstanceOf[PAdt]
                pdc.adt = adt
                val fdtv = PTypeVar.freshTypeSubstitution((adt.typVarsSeq map (tv => tv.idndef.name)).distinct) //fresh domain type variables
                pdc.adtTypeRenaming = Some(fdtv)
                pdc._extraLocalTypeVariables = (adt.typVarsSeq map (tv => PTypeVar(tv.idndef.name))).toSet
              case _ =>
                nestedTypeError = true
                t.messages ++= FastMessaging.message(pdc, "invalid adt discriminator")
            }

          case _ => sys.error("PAdtOpApp#typecheck: unexpectable type")
        }

        if (poa.signatures.nonEmpty && poa.args.forall(_.typeSubstitutions.nonEmpty) && !nestedTypeError) {
          val ltr = getFreshTypeSubstitution(poa.localScope.toList) //local type renaming - fresh versions
          val rlts = poa.signatures map (ts => refreshWith(ts, ltr)) //local substitutions refreshed
          assert(rlts.nonEmpty)
          val rrt: PDomainType = POpApp.pRes.substitute(ltr).asInstanceOf[PDomainType] // return type (which is a dummy type variable) replaced with fresh type
          val flat = poa.args.indices map (i => POpApp.pArg(i).substitute(ltr)) //fresh local argument types
          // the tuples below are: (fresh argument type, argument type as used in domain of substitutions, substitutions, the argument itself)
          poa.typeSubstitutions ++= t.unifySequenceWithSubstitutions(rlts, flat.indices.map(i => (flat(i), poa.args(i).typ, poa.args(i).typeSubstitutions.distinct.toSeq, poa.args(i))) ++
            (
              extraReturnTypeConstraint match {
                case None => Nil
                case Some(t) => Seq((rrt, t, List(PTypeSubstitution.id), poa))
              }
              )
          ).getOrElse(Seq())
          val ts = poa.typeSubstitutions.distinct
          if (ts.isEmpty)
            t.typeError(poa)
          poa.typ = if (ts.size == 1) rrt.substitute(ts.head) else rrt
        } else {
          poa.typeSubstitutions.clear()
          poa.typ = PUnknown()()
        }
      }
    }
    None
  }
}

case class PConstructorCall(idnref: PIdnRef, callArgs: PDelimited.Comma[PSym.Paren, PExp], typeAnnotated: Option[(PSym.Colon, PType)])
                           (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp with PCallLike with PLocationAccess with HasSemanticHighlights with PLspCall {
  // Following field is set during resolving, respectively in the typecheck method inherited from PAdtOpApp
  var constructor: PAdtConstructor = null

  override def signatures: List[PTypeSubstitution] = {
    if (adt != null && constructor != null && constructor.formalArgs.size == args.size) {
      List(
        new PTypeSubstitution(
          args.indices.map(i => POpApp.pArg(i).domain.name -> constructor.formalArgs(i).typ.substitute(adtTypeRenaming.get)) :+
            (POpApp.pRes.domain.name -> adt.getAdtType.substitute(adtTypeRenaming.get)))
      )
    } else List()
  }

  override def translateExp(t: Translator): Exp = {
    val constructor = PAdtConstructor.findAdtConstructor(idnref, t)
    val actualArgs = args map t.exp
    val so: Option[Map[TypeVar, Type]] = adtSubstitution match {
      case Some(ps) => Some(ps.m.map(kv => TypeVar(kv._1) -> t.ttyp(kv._2)))
      case None => None
    }
    so match {
      case Some(s) =>
        val adt = t.getMembers()(constructor.adtName).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtConstructorApp(constructor, actualArgs, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }

  override def getSemanticHighlights: Seq[SemanticHighlight] =
    RangePosition(idnref).map(sp => SemanticHighlight(sp, TokenType.EnumMember)).toSeq
}

// Cannot reuse `PIdnRef` because it implements `PIdnUseName` but the name analyser doesn't work for field references.
case class PAdtFieldRef(name: String)(val pos: (Position, Position)) extends PIdnUse with PLspIdnUse {
  override def rename(newName: String) = PIdnRef(newName)(pos)
}

case class PDestructorCall(rcv: PExp, dot: PReserved[PDiscDot.type], idnref: PAdtFieldRef)
                          (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp with HasSemanticHighlights with PLspExpRef {
  // Following field is set during resolving, respectively in the typecheck method inherited from PAdtOpApp
  var matchingConstructorArg: PFormalArgDecl = null

  // override def opName: String = name.name

  override def signatures: List[PTypeSubstitution] = if (adt != null && matchingConstructorArg != null) {
    assert(args.length == 1, s"PDestructorCall: Expected args to be of length 1 but was of length ${args.length}")
    List(
      new PTypeSubstitution(
        args.indices.map(i => POpApp.pArg(i).domain.name -> adt.getAdtType.substitute(adtTypeRenaming.get)) :+
          (POpApp.pRes.domain.name -> matchingConstructorArg.typ.substitute(adtTypeRenaming.get)))
    )
  } else List()

  override def args: Seq[PExp] = Seq(rcv)

  override def translateExp(t: Translator): Exp = {
    val actualRcv = t.exp(rcv)
    val so: Option[Map[TypeVar, Type]] = adtSubstitution match {
      case Some(ps) => Some(ps.m.map(kv => TypeVar(kv._1) -> t.ttyp(kv._2)))
      case None => None
    }
    so match {
      case Some(s) =>
        val adt = t.getMembers()(this.adt.idndef.name).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtDestructorApp(adt, idnref.name, actualRcv, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }

  override def getSemanticHighlights: Seq[SemanticHighlight] =
    RangePosition(idnref).map(sp => SemanticHighlight(sp, TokenType.EnumMember)).toSeq
}

case object PIsKeyword extends PKwOp("is") {
  override def rightPad = ""
}
case object PDiscDot extends PSym(".") with PSymbolOp

case class PDiscriminatorCall(rcv: PExp, dot: PReserved[PDiscDot.type], is: PReserved[PIsKeyword.type], idnref: PIdnRef)
                             (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp with HasSemanticHighlights with PLspExpRef {
  // override def opName: String = "is" + name.name

  override def signatures: List[PTypeSubstitution] = if (adt != null) {
    assert(args.length == 1, s"PDiscriminatorCall: Expected args to be of length 1 but was of length ${args.length}")
    List(
      new PTypeSubstitution(
        args.indices.map(i => POpApp.pArg(i).domain.name -> adt.getAdtType.substitute(adtTypeRenaming.get)) :+
          (POpApp.pRes.domain.name -> TypeHelper.Bool))
    )
  } else List()

  override def args: Seq[PExp] = Seq(rcv)

  override def translateExp(t: Translator): Exp = {
    val actualRcv = t.exp(rcv)
    val so: Option[Map[TypeVar, Type]] = adtSubstitution match {
      case Some(ps) => Some(ps.m.map(kv => TypeVar(kv._1) -> t.ttyp(kv._2)))
      case None => None
    }
    so match {
      case Some(s) =>
        val adt = t.getMembers()(this.adt.idndef.name).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtDiscriminatorApp(adt, idnref.name, actualRcv, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }

  override def getSemanticHighlights: Seq[SemanticHighlight] =
    RangePosition(idnref).map(sp => SemanticHighlight(sp, TokenType.EnumMember)).toSeq

}