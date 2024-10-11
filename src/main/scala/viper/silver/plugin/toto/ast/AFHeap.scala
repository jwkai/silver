package viper.silver.plugin.toto.ast

import viper.silver.ast._
import viper.silver.plugin.toto.DomainsGenerator
import viper.silver.plugin.toto.ast.AFHeap.getType

case class AFHeap(name: String, tag: Int) {

  def toLocalVar: Exp = {
    LocalVar(name, getType)()
  }

}

object AFHeap {
  def getType: Type = DomainType(DomainsGenerator.fHeapKey, Map[viper.silver.ast.TypeVar,viper.silver.ast.Type]())(Nil)
}