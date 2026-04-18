import OperatorKO7.Meta.MatrixBarrierMix2_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixBarrierMix2

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the balanced mixed-coordinate dimension-2 barrier. -/
theorem no_global_step_orientation_matrixMix2_of_sum_pump
    (M : StepDuplicatingSchema.MatrixMix2Measure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeSum M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixMix2_of_sum_pump
      (Sys := ko7System) M hunbounded

end OperatorKO7.MatrixBarrierMix2
