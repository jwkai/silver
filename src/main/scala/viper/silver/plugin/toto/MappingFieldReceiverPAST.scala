package viper.silver.plugin.toto

import viper.silver.FastMessaging
import viper.silver.ast.{Member, NoPosition, Position}
import viper.silver.parser.{NameAnalyser, PCall, PDomainFunction, PDomainType, PExp, PExtender, PField, PIdnUse, PNode, PType, PTypeSubstitution, Translator, TypeChecker}

case class PMappingFieldReceiver(mapping: PCall, fieldID: PIdnUse, receiver: PCall)(val pos: (Position, Position))
  extends PExtender {

  override val getSubnodes: Seq[PNode] = Seq(mapping, fieldID, receiver)

  def typecheckComp(t: TypeChecker, typeUnit: PType, typeFilter: PType): Unit = {
    val correctReceiverType = ComprehensionPlugin.makeDomainType("Receiver", Seq(typeFilter))
    t.checkTopTyped(receiver, Some(correctReceiverType))
    t.checkTopTyped(fieldID, None)
    val correctMappingType = ComprehensionPlugin.makeDomainType("Mapping",
      Seq(fieldID.typ,typeUnit))
    t.checkTopTyped(mapping, Some(correctMappingType))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    Some(Seq("Typecheck should only be called from PComprehension node."))
  }

  def translateTo(t: Translator): Unit = {
    t.exp(fieldID)
  }

  override def translateMember(t: Translator): Member = ???

}
