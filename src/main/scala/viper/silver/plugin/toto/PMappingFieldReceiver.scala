package viper.silver.plugin.toto

import viper.silver.ast.{Exp, Position}
import viper.silver.parser._

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
    Some(Seq("Internal erro: typecheck should only be called from PComprehension node."))
  }

  def translateTo(t: Translator): (Option[Exp], String, Exp) = {
    val mappingOut = t.exp(mapping)
    val fieldOut = fieldID.name
    val receiverOut = t.exp(receiver)
    (Some(mappingOut), fieldOut, receiverOut)
  }

//  override def translateMember(t: Translator): Member = ???

}
