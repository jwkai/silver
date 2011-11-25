package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.DomainExpression

abstract class DomainAxiom extends ASTNode 
{
	val name : String
	val expression : DomainExpression
}