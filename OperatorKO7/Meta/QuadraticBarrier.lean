import OperatorKO7.Meta.QuadraticBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.QuadraticBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 root-orientation cannot be proved by a restricted quadratic counter measure
whenever the measure has an unbounded affine pump along the schema constructors. -/
theorem no_global_step_orientation_quadratic_of_unbounded
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeQ M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_quadratic_of_unbounded
      (Sys := ko7System) M hunbounded

/-- KO7 successor-pump specialization of the restricted quadratic barrier. -/
theorem no_global_step_orientation_quadratic_of_succ_pump
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_quadratic_of_succ_pump
      (Sys := ko7System) M h_succ_bias h_succ_scale

/-- KO7 wrap-pump specialization of the restricted quadratic barrier. -/
theorem no_global_step_orientation_quadratic_of_wrap_pump
    (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_quadratic_of_wrap_pump
      (Sys := ko7System) M h_wrap_bias

end OperatorKO7.QuadraticBarrier
