package viper.silver.plugin.crimp.ast

import viper.silver.ast._

/** An info that tells us that this (statement) node is tagged with a particular crHeap. */
case class crHeapInfo(crh: CrHeap) extends Info {
  override def comment: Seq[String] = Seq(crh.toString)
  override def isCached: Boolean = false
}

case class CrHeap(crh: Int) {
  override def toString: String = crh.toString

  def toExp: Exp = IntLit(crh)()
}
