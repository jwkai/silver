package viper.silver.plugin.crimp

import viper.silver.ast.{Exp, Position}
import viper.silver.plugin.crimp.ast.CrimpApp
import viper.silver.plugin.crimp.parser.POperator
import viper.silver.verifier._
import viper.silver.verifier.errors.ErrorNode

object ReduceErrors {

  case class OpWellDefinednessError(offendingNode: ErrorNode, op: POperator, reason: ErrorReason, override val cached: Boolean = false) extends ExtensionAbstractVerificationError {

    val id = "op.welldefined"
    val text = s"Reduce operator might not be well-defined."
    override def pos: Position = op.sourcePos
    override def withReason(reason: ErrorReason): AbstractVerificationError =
      OpWellDefinednessError(offendingNode, op,  reason, cached)

    override def withNode(offendingNode: ErrorNode): ErrorMessage =
      OpWellDefinednessError(offendingNode, op, reason, cached)
  }

  case class ReduceApplyError(offendingNode: ErrorNode, reduceNode: CrimpApp, reason: ErrorReason, override val cached: Boolean = false) extends ExtensionAbstractVerificationError {

    val id = "reduce.apply"
    val text = s"Reduce evaluation might not be well-defined."
    override def pos: Position = reduceNode.pos
    override def withReason(reason: ErrorReason): AbstractVerificationError = {
      reason match {
        case ie @ ReduceReasons.InjectivityError(_) =>
          ie.filter = reduceNode.filter
          ie.rec = reduceNode.reduction.receiver
          ReduceApplyError(offendingNode, reduceNode, ie, cached)
        case pe @ ReduceReasons.PermissionsError(_, _) =>
          pe.filter = reduceNode.filter
          pe.rec = reduceNode.reduction.receiver
          ReduceApplyError(offendingNode, reduceNode, pe, cached)
        case _ =>
          ReduceApplyError(offendingNode, reduceNode, reason, cached)
      }
    }

    override def withNode(offendingNode: ErrorNode): ErrorMessage =
      ReduceApplyError(offendingNode, reduceNode, reason, cached)
  }


}



object ReduceReasons {

  case class NotCommutative(offendingNode: ErrorNode, op: POperator) extends ExtensionAbstractErrorReason {
    override def id: String = "op.commutative"
    override def readableMessage: String = s"Operator ${op.idndef.name} might not be commutative."
    override def pos: Position = op.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = NotCommutative(offendingNode, op)
  }

  case class NotAssociative(offendingNode: ErrorNode, op: POperator) extends ExtensionAbstractErrorReason {
    override def id: String = "op.associative"
    override def readableMessage: String = s"Operator ${op.idndef.name} might not be associative."
    override def pos: Position = op.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = NotAssociative(offendingNode, op)
  }

  case class IncorrectIdentity(offendingNode: ErrorNode, op: POperator) extends ExtensionAbstractErrorReason {
    override def id: String = "op.identity"
    override def readableMessage: String = s"Operator ${op.idndef.name} might not have the correct identity."
    override def pos: Position = op.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = IncorrectIdentity(offendingNode, op)
  }


  case class InjectivityError(offendingNode: ErrorNode) extends ExtensionAbstractErrorReason {

    // To be reassigned by the withReason of reduceErrors
    var filter : Exp = null
    var rec : Exp = null

    // Pos does not really matter for reason.
//    override def pos: Position = null;

    override def id: String = "reduce.injective"
    override def readableMessage: String = s"Receiver $rec might not be injective over filter $filter."
//    override def pos: Position = offendingNode.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = InjectivityError(offendingNode)
  }

  case class PermissionsError(offendingNode: ErrorNode, field: String) extends ExtensionAbstractErrorReason {

    var filter : Exp = null
    var rec : Exp = null

    // Pos does not really matter for reason.
    //    override def pos: Position = null;

    override def id: String = "reduce.perm"
    override def readableMessage: String = s"There might be insufficient permission to access " +
      s"elements retrieved from receiver $rec, filter $filter, and field $field."
    //    override def pos: Position = offendingNode.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = PermissionsError(offendingNode, field)
  }

}
