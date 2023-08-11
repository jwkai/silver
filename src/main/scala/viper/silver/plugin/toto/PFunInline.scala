package viper.silver.plugin.toto

import viper.silver.ast.Position
import viper.silver.parser.{PExp, PExtender, PFormalArgDecl}

case class PFunInline(args: Seq[PFormalArgDecl], body: PExp)
                     (val pos : (Position, Position)) extends PExtender {
}
