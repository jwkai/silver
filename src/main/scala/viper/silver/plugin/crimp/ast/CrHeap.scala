package viper.silver.plugin.crimp.ast

import viper.silver.ast._

/** An info that tells us that this (statement) node is tagged with crimp-heap indices */
case class crHeapInfo(crh: CrHeapMap) extends Info {
  override def comment: Seq[String] = Seq(crh.toString)
  override def isCached: Boolean = false
}

case class CrHeap(crh: Int) {
  override def toString: String = crh.toString

  def toExp: Exp = IntLit(crh)()
}

case class HeapKey(receiver: Exp, field: String)

/** The crimp-heap index of every receiver of a method at one program point.
 *
 * These indices are allocated per field: a command advances all receivers over a field in its footprint to the same
 * fresh number (receivers over one field carry the same index at every point). `ofField` checks the lockstep invariant.
 */
case class CrHeapMap(m: Map[HeapKey, CrHeap]) {
  def fields: Set[String] = m.keySet.map(_.field)

  /** The index of every receiver over `field`. */
  def ofField(field: String): CrHeap = {
    val indices = m.collect { case (k, ch) if k.field == field => ch }.toSet
    if (indices.size != 1)
      throw new IllegalStateException(
        s"crimp: the receivers over field $field have the indices {${indices.mkString(", ")}} (expected exactly one)")
    indices.head
  }

  /** The index of receiver `key`. A key that is not in the map has the index of its field (lockstep). */
  def apply(key: HeapKey): CrHeap = m.getOrElse(key, ofField(key.field))

  /** The map in which every receiver over `field` has index `ch`. */
  def withField(field: String, ch: CrHeap): CrHeapMap =
    CrHeapMap(m.map { case (k, v) => if (k.field == field) k -> ch else k -> v })

  override def toString: String = fields.toSeq.sorted.map(f => s"$f:${ofField(f)}").mkString(" ")
}

object CrHeapMap {
  /** Every key at index `ch`. */
  def of(keys: Set[HeapKey], ch: CrHeap): CrHeapMap = CrHeapMap(keys.map(k => k -> ch).toMap)
}
