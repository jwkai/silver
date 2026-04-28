package viper.silver.plugin.crimp.ast

import viper.silver.ast._

/** An info that tells us that this (statement) node is tagged with a particular cHeap. */
case class cHeapInfo(ch: CHeap) extends Info {
  override def comment: Seq[String] = Seq(ch.toString)
  override def isCached: Boolean = false
}

case class CHeap(ch: Int) {
  override def toString: String = ch.toString

  def toExp: Exp = IntLit(ch)()
}
