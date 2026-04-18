import OperatorKO7.Meta.MaxBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MaxBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the schema-level max barrier. -/
theorem no_global_step_orientation_max_of_unbounded
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_max_of_unbounded
      (Sys := ko7System) M hunbounded

/-- KO7 successor-pump specialization of the schema-level max barrier. -/
theorem no_global_step_orientation_max_of_succ_pump
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema)
    (h_succ_const : 1 ≤ M.succ_const) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  apply no_global_step_orientation_max_of_unbounded (M := M)
  intro k
  refine ⟨StepDuplicatingSchema.succIter ko7Schema k, ?_⟩
  simpa using StepDuplicatingSchema.eval_succIter_ge_max (M := M) h_succ_const k

/-- KO7 wrap-pump specialization of the schema-level max barrier. -/
theorem no_global_step_orientation_max_of_wrap_pump
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema)
    (h_wrap_drift : 1 ≤ M.wrap_const + M.wrap_left) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  apply no_global_step_orientation_max_of_unbounded (M := M)
  intro k
  refine ⟨StepDuplicatingSchema.wrapIter ko7Schema k, ?_⟩
  simpa using StepDuplicatingSchema.eval_wrapIter_ge_max (M := M) h_wrap_drift k

end OperatorKO7.MaxBarrier
