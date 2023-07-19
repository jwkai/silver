package viper.silver.plugin.toto

import viper.silver.FastMessaging
import viper.silver.ast.{NoPosition, Position}
import viper.silver.parser.{NameAnalyser, PCall, PDomainFunction, PDomainType, PExp, PExtender, PField, PIdnUse, PNode, PType, PTypeSubstitution, TypeChecker}

case class PMappingFieldReceiver(mapping: PCall, fieldID: PIdnUse, receiver: PCall)(val pos: (Position, Position))
  extends PExtender {

  override val getSubnodes: Seq[PNode] = Seq(mapping, fieldID, receiver)

  def typecheckComp(t: TypeChecker, n: NameAnalyser, typeUnit: PType, typeFilter: PType): Option[Seq[String]] = {
    var messagesOut : Seq[String] = Seq()

//    receiver.typeSubstitutions
//    n.definition(null)(receiver.idnuse) match {
//      case Some(PDomainFunction(idndef, formalArgs, typ, unique, interpretation)) => typ.substitute()
//      case None => ???
//    }

//    receiver.typeSubstitutions = receiver.typeSubstitutions.addOne(PTypeSubstitution())
//    PDomainType("Receiver",Seq())()
    val correctReceiverType = ComprehensionPlugin.makeDomainType("Receiver", Seq(typeFilter))
    t.checkTopTyped(receiver, Some(correctReceiverType))
    t.checkTopTyped(fieldID, None)
    val correctMappingType = ComprehensionPlugin.makeDomainType("Mapping",
      Seq(fieldID.typ,typeUnit))
    t.checkTopTyped(mapping, Some(correctMappingType))
//    receiver.typ match {
//      case PDomainType(domain, args) =>
//        if (!(domain.name == "Receiver"))
//          messagesOut = messagesOut :+ "Receiver expression not a receiver."
//      case _ =>
//        messagesOut = messagesOut :+ "Receiver expression not a receiver."
//    }
//    mapping.typ match {
//      case PDomainType(domain, args) =>
//        if (domain.name == "Mapping")
//          t.checkTopTyped(fieldID, Some(args.head))
//        else
//          messagesOut = messagesOut :+ "Mapping expression not a mapping."
//      case _ =>  messagesOut = messagesOut :+ "Mapping expression not a Mapping."
//    }
    //    t.checkInternal(fieldID)
    //    n.definition(null)(fieldID) match {
    //      case Some(value) => fieldID.decl = value
    //      case None => messagesOut ++= "Field in comprehension not found."
    //    }
    Some(messagesOut)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }




}
