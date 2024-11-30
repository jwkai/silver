package viper.silver.plugin.hreduce.ast

import viper.silver.ast._

/** An info that tells us that this (statement) node is tagged with a particular rHeap. */
case class rHeapInfo(rh: ARHeap) extends Info {
  override def comment: Seq[String] = Seq(rh.toString)
  override def isCached: Boolean = false
}

case class ARHeap(rh: Int) {
  override def toString: String = rh.toString

  def toExp: Exp = IntLit(rh)()
}
