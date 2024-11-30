package viper.silver.plugin.hreduce.parser

import viper.silver.ast.{Exp, Position}
import viper.silver.parser._
import viper.silver.plugin.hreduce.HReducePlugin

case class PMappingFieldReceiver(mapping: PCall, fieldID: PIdnUse, receiver: PCall)(val pos: (Position, Position))
  extends PExtender with PPrettySubnodes {

  override val subnodes: Seq[PNode] = Seq(mapping, fieldID, receiver)

  def typecheckComp(t: TypeChecker, n: NameAnalyser, typeUnit: PType, typeFilter: PType): Seq[String] = {
    val errorSeq: Seq[String] = Seq()

    val correctReceiverType = HReducePlugin.makeDomainType("Receiver", Seq(typeFilter))
    t.checkTopTyped(receiver, Some(correctReceiverType))

    // find the field in the program
    val fields = n.globalDefinitions(fieldID.name)
    fields match {
      case Seq(field) =>
        field match {
          case decl: PFieldDecl =>
            // Mapping must be from field's type to operator's type
            val correctMappingType = HReducePlugin.makeDomainType("Mapping", Seq(decl.typ, typeUnit))
            t.checkTopTyped(mapping, Some(correctMappingType))
          case _ => return errorSeq :+ "Reduce field not declared as a field."
        }
      case Seq() => return errorSeq :+ "Field not found."
      case _ => return errorSeq :+ "Field not resolvable (multiple definitions found)."
    }
    errorSeq
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    Some(Seq("Internal error: typecheck should only be called from PReduction node."))
  }

  def translateTo(t: Translator): (Exp, String, Exp) = {
    val mappingOut = t.exp(mapping)
    val fieldOut = fieldID.name
    val receiverOut = t.exp(receiver)
    (mappingOut, fieldOut, receiverOut)
  }
}
