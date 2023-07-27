package viper.silver.plugin.toto

import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.{Declaration, ErrorTrafo, ExtensionMember, Info, Node, Position, Type}

case class ASnapshotDecl(name: String, compType: Type, fieldID: String)(val pos : Position) extends ExtensionMember
{
  override def extensionSubnodes: Seq[Node] = ???
  override def prettyPrint: PrettyPrintPrimitives#Cont = ???

  override def info: Info = ???

  override def errT: ErrorTrafo = ???

  override val scopedDecls: Seq[Declaration] = ???

}
