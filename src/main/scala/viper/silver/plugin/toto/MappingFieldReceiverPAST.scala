package viper.silver.plugin.toto

import viper.silver.FastMessaging
import viper.silver.ast.Position
import viper.silver.parser.{NameAnalyser, PCall, PDomainType, PExp, PExtender, PField, PIdnUse, PNode, PType, TypeChecker}

case class PMappingFieldReceiver(mapping: PCall, fieldID: PIdnUse, receiver: PCall)(val pos: (Position, Position))
  extends PExtender {

  override val getSubnodes: Seq[PNode] = Seq(mapping, fieldID, receiver)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    var messagesOut = Seq()
    t.checkTopTyped(mapping, None)
    t.checkTopTyped(receiver, None)
    receiver.typ match {
      case PDomainType(domain, args) =>
        if (!(domain.name == "Receiver")) messagesOut ++= "Receiver expression not a receiver."
      case _ =>
        messagesOut ++= "Receiver expression not a receiver."
    }
    mapping.typ match {
      case PDomainType(domain, args) =>
        if (domain.name == "Mapping")
          t.checkTopTyped(fieldID, Some(args.head))
        else
          messagesOut ++= "Mapping expression not a mapping."
      case messagesOut ++= "Mapping expression not a Mapping."
    }
    //    t.checkInternal(fieldID)
//    n.definition(null)(fieldID) match {
//      case Some(value) => fieldID.decl = value
//      case None => messagesOut ++= "Field in comprehension not found."
//    }
    Some(messagesOut)
  }



}
