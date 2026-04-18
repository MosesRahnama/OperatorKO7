import OperatorKO7.Meta.MatrixProjectionCoverage_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixProjectionCoverage

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7-facing fixed-row corollary: the dimension-parametric tracked-row barrier already
covers any componentwise matrix interpretation whose chosen row satisfies the affine pump
interface. -/
theorem no_global_step_orientation_matrix_fixed_row_of_componentwise_pump
    {d : Nat} (tracked : Fin d)
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeTracked M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixD_of_componentwise_pump
      (Sys := ko7System) M hunbounded

/-- KO7-facing row-sum corollary: the all-ones projection is a concrete instance of the
weighted functional barrier. -/
theorem no_global_step_orientation_matrix_row_sum_of_componentwise_pump
    {d : Nat}
    (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d)
    (hweight : M.weight = StepDuplicatingSchema.rowSumWeight)
    (hunbounded : StepDuplicatingSchema.HasUnboundedWeightedRange M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt := by
  have hM : M.weight = StepDuplicatingSchema.rowSumWeight := hweight
  simpa using
    StepDuplicatingSchema.no_global_orients_matrixFunctional_of_componentwise_pump
      (Sys := ko7System) M (by
      simpa [hM] using hunbounded)

end OperatorKO7.MatrixProjectionCoverage
