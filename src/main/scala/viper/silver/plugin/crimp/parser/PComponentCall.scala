package viper.silver.plugin.crimp.parser

import viper.silver.FastMessaging
import viper.silver.ast.{DomainFunc, DomainFuncApp, Exp, Position, SourcePNodeInfo}
import viper.silver.parser._

/** A call to a crimp component (receiver, filter, operator or mapping).
 * The parser reads it as a PCall, and transformComponentCalls in CrimpPlugin.beforeResolve replaces it by this node,
 * This node types and translates itself to an application of the component's DomainFunc. */
case class PComponentCall(idnref: PIdnRef[PCrimpComponent], callArgs: PDelimited.Comma[PSym.Paren, PExp], typeAnnotated: Option[(PSym.Colon, PType)])(val pos: (Position, Position))
  extends PExtender with PCallLike with PLocationAccess {
  
    def component: Option[PCrimpComponent] = idnref.decl

    private var checked = false

  // Only for a component with a type (its check succeeded), and with the right number of arguments. A component is
  // not generic: its argument and result types are ground.
    override def signatures: List[PTypeSubstitution] = component match {
      case Some(c) if c.checkState == ComponentCheckState.Ok && c.formalArgs.size == args.size => List(
            new PTypeSubstitution(args.indices.map(i => POpApp.pArg(i).domain.name -> c.formalArgs(i).typ) :+
                POpApp.pRes.domain.name -> c.resultType))
      case _ => Nil
    }

  /** Mirrors the type checker's handling of a call (TypeChecker.checkInternal), except that the crimp component is
   * first type checked if that has not happened yet, and a recursive call is an error.
   * The call gets no type (PUnknown) if the component failed its check. */
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    if (checked) return None
    checked = true
    typ = PUnknown()
    args.foreach(t.checkInternal)
    var nestedTypeError = !args.forall(_.typ.isValidOrUndeclared)
    typeAnnotated.foreach { case (_, ta) =>
      t.check(ta)
      if (!ta.isValidOrUndeclared) nestedTypeError = true
    }
    if (idnref.decls.isEmpty) return Some(Seq(s"undeclared call `${idnref.name}`, expected function or predicate"))
    if (component.isEmpty) return Some(Seq(s"ambiguous call `${idnref.name}`"))
    val c = component.get
    if (c.formalArgs.size != args.size) return Some(Seq("wrong number of arguments"))
    c.checkState match {
      case ComponentCheckState.InProgress =>
        return Some(Seq(s"Recursive use of crimp component `${idnref.name}`"))
      case ComponentCheckState.Unchecked => c.ensureChecked(t, n)
      case _ =>
    }
    if (nestedTypeError || signatures.isEmpty) return None
    val ltr = PTypeVar.freshTypeSubstitutionPTVs(localScope.toList)
    val rlts = signatures.map(ts => new PTypeSubstitution(ts.map(kv => ltr.rename(kv._1) -> kv._2.substitute(ltr))))
    val rrt = POpApp.pRes.substitute(ltr).asInstanceOf[PDomainType]
    val argData = args.indices.map(i => (args(i).typ, POpApp.pArg(i).substitute(ltr), args(i).typeSubsDistinct.toSeq,
      args(i))) ++ typeAnnotated.map { case (_, ta) => (ta, rrt, List(PTypeSubstitution.id), this) }
    t.unifySequenceWithSubstitutions(rlts, argData) match {
      // The same message at the same argument as the type checker's.
      case Left((a, b, at)) =>
        t.messages ++= FastMessaging.message(at, s"found incompatible type `${a.pretty}`, expected `${b.pretty}`")
      case Right(substitutions) =>
        typeSubstitutions ++= substitutions
        val ts = typeSubsDistinct
        typ = if (ts.size == 1) rrt.substitute(ts.head) else rrt
    }
    None
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(this, Some(expected))
    None
  }

  // The component's DomainFunc is registered with the member signatures (PCrimpComponent.translateMemberSignature)
  override def translateExp(t: Translator): Exp = t.getMembers()(idnref.name) match {
    case f: DomainFunc =>
      DomainFuncApp(f, args.map(t.exp), Map.empty)(t.liftPos(this), SourcePNodeInfo(this))
    case m =>
      sys.error(s"Component `${idnref.name}` is translated as ${m.getClass.getSimpleName}, not as a DomainFunc")
  }
}