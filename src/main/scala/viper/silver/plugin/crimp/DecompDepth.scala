package viper.silver.plugin.crimp

/** The decomposition depth of a crimp term: how many single-index decompositions (_dropOne1, _loseMany, ...) the fold
  * laws allow on it, encoded as its fuel argument succ^d(zero()) (hcrimpApply{M,S}(fuel, ..); applyCrimpFuelEq lets a
  * term at depth d stand for itself at every smaller depth, so terms of different depths agree).
  * Heuristic: depth 1 suffices for cancellative operators e.g. (Int, +) or multiset union; max-like operators need 2.
  * Set by the user:
  *   - `@decompDepth("N")` before an operator or a receiver declaration: for the crimps with that operator or over that
  *     receiver (if both are annotated, the larger depth);
  *   - `@decompDepth("N") (crimp[..][..](..))`: for this crimp expression (e.g. in a macro for one receiver/operator
  *     pair); overrides the declarations;
  *   - otherwise the program-wide default: the JVM property `-Dcrimp.decompDepth=N`, else 2. */
object DecompDepth {
  final val key = "decompDepth"
  final val property = "crimp.decompDepth"
  final val builtinDefault = 2

  /** One annotation's values: exactly one positive integer (at most 999). */
  def parseValues(values: Seq[String]): Either[String, Int] = values.map(_.trim) match {
    case Seq(v) if v.matches("[1-9][0-9]{0,2}") => Right(v.toInt)
    case _ => Left(s"""@$key expects one positive integer, e.g. @$key("1"); found ${values.map("\"" + _ + "\"").mkString("(", ", ", ")")}.""")
  }

  /** The `@decompDepth` among the given annotations (key, values), if any. */
  def of(annotations: Seq[(String, Seq[String])]): Option[Either[String, Int]] = annotations.filter(_._1 == key) match {
    case Seq() => None
    case Seq((_, values)) => Some(parseValues(values))
    case _ => Some(Left(s"@$key is given more than once."))
  }

  /** The program-wide default: the JVM property if set, else builtinDefault. */
  def default: Either[String, Int] = sys.props.get(property) match {
    case Some(v) => parseValues(Seq(v)).left.map(_ => s"-D$property=$v: expected a positive integer (at most 999).")
    case None => Right(builtinDefault)
  }

  /** The depths the lowering uses: the default and the declared depths of operators and receivers, by name. */
  case class Config(default: Int, byComponent: Map[String, Int]) {
    /** A crimp term's depth: its own annotation, else the larger of its operator's and its receiver's, else the
      * default. */
    def of(own: Option[Int], operator: Option[String], receiver: Option[String]): Int =
      own.getOrElse(Seq(operator, receiver).flatten.flatMap(byComponent.get).maxOption.getOrElse(default))
  }
}
