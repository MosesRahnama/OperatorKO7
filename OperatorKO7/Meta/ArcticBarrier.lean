import OperatorKO7.Meta.MaxBarrier

/-!
# Arctic Projection Barrier

This file records a tool-facing arctic-style corollary of the max barrier. We do
not formalize generic arctic matrix algebra. Instead, we isolate the case that
matters for the current boundary story: an arctic-family interpretation with a
distinguished finite primary projection whose values obey the same max-plus laws
as the schema-level `MaxMeasure`.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Minimal finite/bottom carrier for arctic-style projections. -/
inductive ArcticNat where
  | bot
  | fin : Nat → ArcticNat
deriving DecidableEq, Repr

/-- Comparison on a distinguished finite arctic coordinate. -/
def ArcticLt : ArcticNat → ArcticNat → Prop
  | ArcticNat.fin x, ArcticNat.fin y => x < y
  | _, _ => False

/-- An arctic-style family with a distinguished finite primary projection governed
by the max barrier interface. -/
structure ArcticPrimaryMeasure (S : StepDuplicatingSchema) where
  eval : S.T → ArcticNat
  projectedMax : MaxMeasure S
  eval_eq_fin : ∀ t, eval t = ArcticNat.fin (projectedMax.eval t)

/-- Unbounded-pump arctic barrier via the tracked finite max projection. -/
theorem no_arctic_primary_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : ArcticPrimaryMeasure S)
    (hunbounded : HasUnboundedRangeMax M.projectedMax) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    simpa [ArcticLt, M.eval_eq_fin] using h b s n
  exact no_max_orients_dup_step_of_unbounded (S := S) M.projectedMax hunbounded hmax

/-- Successor-pump arctic barrier via the tracked finite max projection. -/
theorem no_arctic_primary_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : ArcticPrimaryMeasure S)
    (h_succ_const : 1 ≤ M.projectedMax.succ_const) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    simpa [ArcticLt, M.eval_eq_fin] using h b s n
  exact no_max_orients_dup_step_of_succ_pump (S := S) M.projectedMax h_succ_const hmax

/-- Wrap-pump arctic barrier via the tracked finite max projection. -/
theorem no_arctic_primary_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : ArcticPrimaryMeasure S)
    (h_wrap_drift : 1 ≤ M.projectedMax.wrap_const + M.projectedMax.wrap_left) :
    ¬ (∀ (b s n : S.T),
      ArcticLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    simpa [ArcticLt, M.eval_eq_fin] using h b s n
  exact no_max_orients_dup_step_of_wrap_pump (S := S) M.projectedMax h_wrap_drift hmax

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

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
