import OperatorKO7.Meta.ArcticBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.ArcticBarrier

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the arctic primary-projection barrier. -/
theorem no_global_step_orientation_arctic_primary_of_unbounded
    (M : StepDuplicatingSchema.ArcticPrimaryMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M.projectedMax) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.ArcticLt := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.ArcticLt
          (M.eval (ko7Schema.wrap s (ko7Schema.recur b s n)))
          (M.eval (ko7Schema.recur b s (ko7Schema.succ n))) := by
    intro b s n
    exact h (ko7System.dup_step b s n)
  exact
    StepDuplicatingSchema.no_arctic_primary_orients_dup_step_of_unbounded
      (S := ko7Schema) M hunbounded hdup

end OperatorKO7.ArcticBarrier
