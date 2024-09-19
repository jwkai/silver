package viper.silver.plugin.toto.ast

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.plugin.toto.DomainsGenerator
import viper.silver.plugin.toto.ast.ACompDecl.tupleFieldToString

// Constructor should not be called directly, use getOrMakeNewSnapDecl
case class ACompDecl private(compType: (Type, Type, Type), fieldName: String)(val pos : Position = NoPosition)
  extends ExtensionMember
{
  def key: String = tupleFieldToString(compType, fieldName)

  override def name: String = key
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = text(key)

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = Seq()

  val outType: Type = compType._3

  def compDType(input: Program): DomainType = {
    val compDomain = input.findDomain(DomainsGenerator.compDKey)
    val typeVars = compDomain.typVars
    if (typeVars.length != 3) {
      throw new Exception("Comp domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> compType._1,
      typeVars(1) -> compType._2,
      typeVars(2) -> compType._3
    )
    DomainType.apply(compDomain, typeVarMap)
  }

  def primeViperDecl(program: Program) : DomainFunc = {
    val originalDecl = viperFuncSignature(program)
//    val compArg = originalDecl.formalArgs(0)
//    val filterArg = originalDecl.formalArgs(1)
//    val (pre, post) = primePrePosts(program, compArg.localVar, filterArg.localVar)

    originalDecl.copy(name = originalDecl.name + "1")(
      originalDecl.pos, originalDecl.info, originalDecl.domainName, originalDecl.errT)
  }

//  def primePrePosts(program: Program, c: Exp, f: Exp): (Seq[Exp],Seq[Exp]) = {
//    val helper = new AxiomHelper(program)
//    val reqFRGood = helper.filterReceiverGood(f, c)
//    val accessCheck = helper.forallFilterHaveAccImpure(f, c, fieldName,
//      FractionalPerm(IntLit(1)(), IntLit(10)())())
//    (Seq(reqFRGood, accessCheck), Seq(reqFRGood))
//  }

  def viperFuncSignature(input: Program): DomainFunc = {
    val compDomain = input.findDomain(DomainsGenerator.compDKey)
    val typeVars = compDomain.typVars
    if (typeVars.length != 3) {
      throw new Exception("Comp domain must have 3 type variables")
    }
    val typeVarMap = Map(
      typeVars(0) -> compType._1,
      typeVars(1) -> compType._2,
      typeVars(2) -> compType._3
    )
    val args0 = LocalVarDecl("fh", AFHeap.getType)()
    val args1 = LocalVarDecl("c", DomainType.apply(compDomain, typeVarMap))()
    val args2 = LocalVarDecl("f", SetType(compType._1))()
    DomainFunc(name, Seq(args0, args1, args2), outType)(domainName = compDomain.name)
  }

  def viperDecl(input: Program): DomainFunc = {
    viperFuncSignature(input)
//    val decl = viperFuncSignature(input)
//    val (pre, post) = prePostConditions(input, decl.formalArgs(0).localVar,
//      decl.formalArgs(1).localVar)
//    decl.copy(pres = pre, posts = post)(decl.pos, decl.info, decl.errT)
  }

//  def prePostConditions(input: Program, c: Exp, f: Exp): (Seq[Exp],Seq[Exp]) = {
//    val compType = c.typ.asInstanceOf[DomainType]
//
//    val helper = new AxiomHelper(input)
//
//    val reqFRGood = helper.filterReceiverGood(f, c)
//    val fElemType = f.typ match {
//      case setType: SetType => setType.elementType
//      case _ => throw new Exception("Filter must be a set")
//    }
//    // Make the injectivity checks
//    val forallVarInd1 = LocalVarDecl("__ind1", fElemType)()
//    val forallVarInd2 = LocalVarDecl("__ind2", fElemType)()
//
//    val setContainsi1 = AnySetContains(forallVarInd1.localVar, f)()
//    val setContainsi2 = AnySetContains(forallVarInd2.localVar, f)()
//    val i1Neqi2 = NeCmp(forallVarInd1.localVar, forallVarInd2.localVar)()
//
//    val getreceiver = input.findDomainFunction(DomainsGenerator.compGetRecvKey)
//    // getreceiver($c)
//    val getreceiverApplied = DomainFuncApp(getreceiver, Seq(c),
//      compType.typVarsMap)()
//    val recApplyInd1 = helper.applyDomainFunc(DomainsGenerator.recApplyKey,
//      Seq(getreceiverApplied, forallVarInd1.localVar),
//      compType.typVarsMap)
//    val recApplyInd2 = helper.applyDomainFunc(DomainsGenerator.recApplyKey,
//      Seq(getreceiverApplied, forallVarInd2.localVar),
//      compType.typVarsMap)
//    val recApplyNeq = NeCmp(recApplyInd1, recApplyInd2)()
//    val injectiveFullCheck = Forall(Seq(forallVarInd1, forallVarInd2),
//      Seq(Trigger(Seq(setContainsi1, setContainsi2))()),
//      helper.foldedConjImplies(Seq(setContainsi1, setContainsi2, i1Neqi2),
//        Seq(recApplyNeq))
//    )()
//
//    // requires [filterReceiverGood(indices, getreceiver(c)),
//    // filterReceiverGood(indices, getreceiver(c)) || forall $i1: Int, $i2: Int ::
//    val inhaleExhaleExp = InhaleExhaleExp(reqFRGood,
//      Or(reqFRGood, injectiveFullCheck)())(
//      errT =
//        ReTrafo({
//          case reasons.AssertionFalse(a) => FoldReasons.InjectivityError(a)
//        })
//    )
//
//    // Access pres
//    val accessCheckWithoutErr = helper.forallFilterHaveAccImpure(f, c, fieldName,
//      FractionalPerm(IntLit(1)(), IntLit(10)())())
//
//    val accessCheck = accessCheckWithoutErr.copy()(
//      pos  = accessCheckWithoutErr.pos,
//      info = accessCheckWithoutErr.info,
//      errT =
//        ReTrafo({
//          case reasons.InsufficientPermission(a) => FoldReasons.PermissionsError(a, fieldName)
//        })
//    )
//
//    // ------ Now posts------
//    // ensures domain(result) == indices
//    val domainEqF = EqCmp(MapDomain(Result(outType)())(), f)()
//
//    // ensures getFieldID(result) == int
//    val fieldIDApplied = helper.applyDomainFunc(DomainsGenerator.getFieldIDKey,
//      Seq(Result(outType)()),
//      compType.typVarsMap)
//    val fieldIDEq = EqCmp(fieldIDApplied, IntLit(ASnapshotDecl.getFieldInt(fieldName))())()
//
//
//    // ensures forall i: Int :: {result[i]}
//    //        i in indices ==> result[i] ==
//    //        mapApply(getmapping(c),recApply(getreceiver(c), i).val)
//    val mapGetPost = helper.forallFilterResultMap(f, c, fieldName,
//      Result(outType)())
//
//    // mapDelete axiom
//    val mapDeletePost = helper.forallMapDelete(f,c, primeViperDecl(input),
//      Result(outType)())
//
//    // mapSubmap axiom
//    val mapSubmapPost = helper.forallMapSubmap(f,c, primeViperDecl(input),
//      Result(outType)())
//
//    val disjPost = helper.forallDisjUnion(f,c, primeViperDecl(input),
//      Result(outType)())
//
//    // extensional eq of set axiom
//    val extensionalEqPost = helper.forallDummyExtensionality(f,c, primeViperDecl(input))
//
//    // prime equals axiom
//    val eqPrime = EqCmp(Result(outType)(),
//      FuncApp(primeViperDecl(input), Seq(c, f))())()
//
//    (Seq(inhaleExhaleExp, accessCheck),
//      Seq(reqFRGood, domainEqF, mapGetPost, mapDeletePost, mapSubmapPost, disjPost,
//        extensionalEqPost, eqPrime,
//        fieldIDEq))
//
//  }

  def findFieldInProgram(p: Program): Field = {
    p.findField(fieldName)
  }
}


object ACompDecl {

  private val compDecls: scala.collection.mutable.Map[String, ACompDecl] = scala.collection.mutable.Map()

  private var uniqueFieldInt = 0

  private val fieldIDMap: scala.collection.mutable.Map[String, Int] = scala.collection.mutable.Map()

  private def getOrMakeNewCompDecl(compType: (Type, Type, Type), fieldID: String): ACompDecl = {
    val key = tupleFieldToString(compType, fieldID)
    addFieldtoMap(fieldID)
    compDecls.getOrElseUpdate(key, new ACompDecl(compType, fieldID)(NoPosition))
  }

  def apply(compType: (Type, Type, Type), fieldID: String): ACompDecl = {
    getOrMakeNewCompDecl(compType, fieldID)
  }

  def addFieldtoMap(fieldName: String): Unit = {
    if (!fieldIDMap.contains(fieldName)) {
      fieldIDMap(fieldName) = uniqueFieldInt
      uniqueFieldInt += 1
    }
  }

  def getFieldInt(field: String): Int = {
    fieldIDMap(field)
  }

  def tupleFieldToString(t: (Type, Type, Type), fieldID: String): String = {
    // replace letters [ and ] with _
    ("__hfold_" + t._1.toString() + "_" + t._2.toString() + "_" + t._3.toString() + "_" + fieldID
      ).replaceAll("[\\[\\]]", "_")
  }

  def getAllCompDecls(input: Program) : Seq[DomainFunc] = {
    compDecls.values.flatMap(d =>
      Seq(d.viperDecl(input), d.primeViperDecl(input))
    ).toSeq
  }

}