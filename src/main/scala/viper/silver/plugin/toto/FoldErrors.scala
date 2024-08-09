package viper.silver.plugin.toto

import viper.silver.ast.{Exp, Position}
import viper.silver.plugin.toto.ast.ACompApply
import viper.silver.plugin.toto.parser.PCompOperator
import viper.silver.verifier.errors.ErrorNode
import viper.silver.verifier._

object FoldErrors {

  case class OpWellDefinednessError(offendingNode: ErrorNode, op: PCompOperator, reason: ErrorReason, override val cached: Boolean = false) extends ExtensionAbstractVerificationError {

    val id = "op.welldefined"
    val text = s"Fold operator might not be well-defined."
    override def pos: Position = op.sourcePos
    override def withReason(reason: ErrorReason): AbstractVerificationError =
      OpWellDefinednessError(offendingNode, op,  reason, cached)

    override def withNode(offendingNode: ErrorNode): ErrorMessage =
      OpWellDefinednessError(offendingNode, op, reason, cached)
  }

  case class FoldApplyError(offendingNode: ErrorNode, foldNode: ACompApply, reason: ErrorReason, override val cached: Boolean = false) extends ExtensionAbstractVerificationError {

    val id = "fold.apply"
    val text = s"Fold evaluation might not be well-defined."
    override def pos: Position = foldNode.pos
    override def withReason(reason: ErrorReason): AbstractVerificationError = {
      reason match {
        case ie @ FoldReasons.InjectivityError(_) =>
          ie.filter = foldNode.snap.filter
          ie.rec = foldNode.comp.receiver
          FoldApplyError(offendingNode, foldNode, ie, cached)
        case pe @ FoldReasons.PermissionsError(_, _) =>
          pe.filter = foldNode.snap.filter
          pe.rec = foldNode.comp.receiver
          FoldApplyError(offendingNode, foldNode, pe, cached)
        case _ =>
          FoldApplyError(offendingNode, foldNode, reason, cached)
      }
    }

    override def withNode(offendingNode: ErrorNode): ErrorMessage =
      FoldApplyError(offendingNode, foldNode, reason, cached)
  }


}



object FoldReasons {

  case class NotCommutative(offendingNode: ErrorNode, op: PCompOperator) extends ExtensionAbstractErrorReason {
    override def id: String = "op.commutative"
    override def readableMessage: String = s"Operator ${op.idndef.name} might not be commutative."
    override def pos: Position = op.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = NotCommutative(offendingNode, op)
  }

  case class NotAssociative(offendingNode: ErrorNode, op: PCompOperator) extends ExtensionAbstractErrorReason {
    override def id: String = "op.associative"
    override def readableMessage: String = s"Operator ${op.idndef.name} might not be associative."
    override def pos: Position = op.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = NotAssociative(offendingNode, op)
  }

  case class IncorrectIdentity(offendingNode: ErrorNode, op: PCompOperator) extends ExtensionAbstractErrorReason {
    override def id: String = "op.identity"
    override def readableMessage: String = s"Operator ${op.idndef.name} might not have the correct identity."
    override def pos: Position = op.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = IncorrectIdentity(offendingNode, op)
  }


  case class InjectivityError(offendingNode: ErrorNode) extends ExtensionAbstractErrorReason {

    // To be reassigned by the withReason of foldErrors
    var filter : Exp = null
    var rec : Exp = null

    // Pos does not really matter for reason.
//    override def pos: Position = null;

    override def id: String = "fold.injective"
    override def readableMessage: String = s"Receiver ${rec} might not be injective over filter ${filter}."
//    override def pos: Position = offendingNode.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = InjectivityError(offendingNode)
  }

  case class PermissionsError(offendingNode: ErrorNode, field: String) extends ExtensionAbstractErrorReason {

    var filter : Exp = null
    var rec : Exp = null

    // Pos does not really matter for reason.
    //    override def pos: Position = null;

    override def id: String = "fold.perm"
    override def readableMessage: String = s"There might be insufficient permission to access " +
      s"elements retrieved from receiver ${rec}, filter ${filter}, and field ${field}."
    //    override def pos: Position = offendingNode.sourcePos
    override def withNode(offendingNode: ErrorNode): ErrorMessage = PermissionsError(offendingNode, field)
  }

}
