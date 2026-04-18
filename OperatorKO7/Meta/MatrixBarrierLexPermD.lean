import OperatorKO7.Meta.MatrixBarrierLexPermD_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixBarrierLexPermD

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 unconditional specialization for the strengthened permutation-priority subclass. -/
theorem no_global_step_orientation_matrixLexPermD_with_primary_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexPermMeasureDWithPrimaryPump ko7Schema d) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval
        (StepDuplicatingSchema.VecPermLexLt M.priority) := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixLexPermD_with_primary_pump
      (Sys := ko7System) M

end OperatorKO7.MatrixBarrierLexPermD
