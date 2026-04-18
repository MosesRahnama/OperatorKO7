import OperatorKO7.Meta.MultilinearBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MultilinearBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 root orientation also fails for the bounded multilinear family. -/
theorem no_global_step_orientation_multilinear_of_unbounded
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeML M)
    (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_multilinear_of_unbounded
      (Sys := ko7System) M hunbounded hdom

/-- KO7 successor-pump specialization of the bounded multilinear barrier. -/
theorem no_global_step_orientation_multilinear_of_succ_pump
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_multilinear_of_succ_pump
      (Sys := ko7System) M h_succ_bias h_succ_scale hdom

/-- KO7 wrap-pump specialization of the bounded multilinear barrier. -/
theorem no_global_step_orientation_multilinear_of_wrap_pump
    (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_multilinear_of_wrap_pump
      (Sys := ko7System) M h_wrap_bias hdom

end OperatorKO7.MultilinearBarrier
