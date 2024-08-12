package viper.silver.plugin.toto

import fastparse.P
import viper.silver.ast.FilePosition
import viper.silver.parser.FastParser

class DummyParser extends FastParser {

  def FP[T](t: => P[T])(implicit ctx: P[_]): P[((FilePosition, FilePosition), T)] ={
    val res: P[T] = t
    res.map({ parsed => ((FilePosition(null, 0, 0), FilePosition(null, 0, 0)), parsed) })
  }

}

class DummyParser2 extends FastParser {

}