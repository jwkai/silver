package silAST.expressions.terms

import silAST.source.SourceLocation

import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.expressions.util.{PTermSequence, GTermSequence}
import silAST.programs.symbols._
import silAST.types.{booleanType, DataTypeFactory, DataType}
import collection.{immutable, Set}
import silAST.expressions.{PProgramVariableSubstitutionC, PProgramVariableSubstitution}

protected[silAST] trait PTermFactory extends NodeFactory with GTermFactory with DataTypeFactory {
  def makePProgramVariableSubstitution(subs:immutable.Set[(ProgramVariable,PTerm)]) : PProgramVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new PProgramVariableSubstitutionC(this,subs,immutable.Set())
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(t : PTerm)
  {
    if (terms contains t)
      return;
    t match
    {
      case gt : GTerm => super.migrate(gt)
      case pv : ProgramVariableTerm => {
        require (programVariables contains pv.variable)
        addTerm(pv)
      }
      case fa : PFunctionApplicationTerm => {
        require(functions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case dfa : PDomainFunctionApplicationTerm => {
        dfa.arguments.foreach(migrate(_))
        require(domainFunctions contains dfa.function)
        addTerm(dfa)
      }
      case ct : PCastTerm => {
        migrate(ct.operand1)
        migrate(ct.newType)
        addTerm(t)
      }
      case fr : PFieldReadTerm => {
        require (fields contains fr.field)
        migrate (fr.location)
        addTerm(fr)
      }
      case ut : PUnfoldingTerm => {
        require (predicates contains ut.predicate)
        migrate (ut.receiver)
        migrate(ut.term)
        addTerm(ut)
      }
      case itet : PIfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pTerm)
        migrate(itet.nTerm)
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableTerm(sourceLocation : SourceLocation, v: ProgramVariable): ProgramVariableTerm = {
    if (!(programVariables contains  v)){
      System.out.println("PTF : " + programVariables.mkString(","))
    }
    require(programVariables contains v)
    addTerm(new ProgramVariableTerm(v)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFunctionApplicationTerm(sourceLocation : SourceLocation, r: PTerm, ff: FunctionFactory, a: PTermSequence): PFunctionApplicationTerm = {
    migrate(r)
    require(functions contains ff.pFunction)
    a.foreach(migrate(_))

    addTerm(new PFunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePCastTerm(sourceLocation : SourceLocation, t: PTerm, dt: DataType): PCastTerm = {
    migrate(t)
    migrate(dt)

    addTerm(new PCastTerm(t, dt)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFieldReadTerm(sourceLocation : SourceLocation, t: PTerm, f: Field): PFieldReadTerm = {
    migrate(t)
    require(fields contains f)

    addTerm(new PFieldReadTerm(t, f)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: PTermSequence): PDomainFunctionApplicationTerm = {
    a.foreach(migrate (_))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sourceLocation, f, a)
      case _ => addTerm(new PDomainFunctionApplicationTermC(f, a)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingTerm(sourceLocation : SourceLocation, r: PTerm, p: PredicateFactory, t: PTerm): PUnfoldingTerm = {
    require(predicates contains p.pPredicate)
    migrate(r)
    migrate(t)

    addTerm(new PUnfoldingTerm(r, p.pPredicate, t)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePIfThenElseTerm(sourceLocation : SourceLocation, c : PTerm,  p:PTerm,  n : PTerm): PIfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc:GTerm, gp:GTerm,gn:GTerm) => makeGIfThenElseTerm(sourceLocation,gc,gp,gn)
      case _ => addTerm(new PIfThenElseTermC(c,p,n)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def functions: Set[Function]

  protected[silAST] def programVariables: Set[ProgramVariable]

  protected[silAST] def fields: Set[Field]

  protected[silAST] def predicates: Set[Predicate]
}