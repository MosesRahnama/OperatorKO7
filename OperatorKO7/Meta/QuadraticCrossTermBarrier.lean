import OperatorKO7.Meta.QuadraticCrossTermBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.QuadraticCrossTermBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 root-orientation also fails for the bounded cross-term quadratic family. -/
theorem no_global_step_orientation_cross_quadratic_of_unbounded
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeX M)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_cross_quadratic_of_unbounded
      (Sys := ko7System) M hunbounded hbounded

/-- KO7 successor-pump specialization of the bounded cross-term quadratic barrier. -/
theorem no_global_step_orientation_cross_quadratic_of_succ_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_cross_quadratic_of_succ_pump
      (Sys := ko7System) M h_succ_bias h_succ_scale hbounded

/-- KO7 wrap-pump specialization of the bounded cross-term quadratic barrier. -/
theorem no_global_step_orientation_cross_quadratic_of_wrap_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_cross_quadratic_of_wrap_pump
      (Sys := ko7System) M h_wrap_bias hbounded

end OperatorKO7.QuadraticCrossTermBarrier
