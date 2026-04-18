import OperatorKO7.Meta.TropicalBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.TropicalBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the tropical primary-projection barrier. -/
theorem no_global_step_orientation_tropical_primary_of_unbounded
    {β : Type}
    (M : StepDuplicatingSchema.TropicalPrimaryMeasure ko7Schema β)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M.projectedMax) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval M.lt := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        M.lt
          (M.eval (ko7Schema.wrap s (ko7Schema.recur b s n)))
          (M.eval (ko7Schema.recur b s (ko7Schema.succ n))) := by
    intro b s n
    exact h (ko7System.dup_step b s n)
  exact
    StepDuplicatingSchema.no_tropical_primary_orients_dup_step_of_unbounded
      (S := ko7Schema) M hunbounded hdup

end OperatorKO7.TropicalBarrier
