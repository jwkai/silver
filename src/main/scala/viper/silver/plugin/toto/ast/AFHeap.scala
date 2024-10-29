package viper.silver.plugin.toto.ast

import viper.silver.ast._

/** An info that tells us that this (statement) node is tagged with a particular fHeap. */
case class fHeapInfo(fh: AFHeap) extends Info {
  override def comment: Seq[String] = Seq(fh.toString)
  override def isCached: Boolean = false
}

case class AFHeap(fh: Int) {
  override def toString: String = fh.toString

  def toExp: Exp = IntLit(fh)()
}
