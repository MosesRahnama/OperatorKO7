import OperatorKO7.Meta.MaxBarrier

/-!
# Tropical primary-projection barrier

This file extends the max/arctic line one step further. We still do not formalize
generic tropical semiring algebra. Instead, we isolate the abstract ingredient
used by the existing proofs:

- a distinguished finite primary projection to `Nat`,
- strict decrease in the ambient carrier reflected by strict decrease of that
  projection,
- and a projected scalar interface already blocked by the max barrier.

This covers a broader tropical-family envelope than the arctic-specific file
without claiming full semiring metatheory.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- A broad tropical-family primary projection: the carrier is abstract, but every
strict comparison must force strict decrease of the tracked finite primary scalar. -/
structure TropicalPrimaryMeasure (S : StepDuplicatingSchema) (β : Type) where
  eval : S.T → β
  lt : β → β → Prop
  primary : β → Nat
  projectedMax : MaxMeasure S
  primary_eq : ∀ t, primary (eval t) = projectedMax.eval t
  lt_strict_primary : ∀ {x y : β}, lt x y → primary x < primary y

/-- Unbounded-pump tropical barrier via the finite primary projection. -/
theorem no_tropical_primary_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} {β : Type}
    (M : TropicalPrimaryMeasure S β)
    (hunbounded : HasUnboundedRangeMax M.projectedMax) :
    ¬ (∀ (b s n : S.T),
      M.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    have hlt := h b s n
    have hproj := M.lt_strict_primary hlt
    simpa [M.primary_eq] using hproj
  exact no_max_orients_dup_step_of_unbounded (S := S) M.projectedMax hunbounded hmax

/-- Successor-pump tropical barrier via the finite primary projection. -/
theorem no_tropical_primary_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} {β : Type}
    (M : TropicalPrimaryMeasure S β)
    (h_succ_const : 1 ≤ M.projectedMax.succ_const) :
    ¬ (∀ (b s n : S.T),
      M.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    have hlt := h b s n
    have hproj := M.lt_strict_primary hlt
    simpa [M.primary_eq] using hproj
  exact no_max_orients_dup_step_of_succ_pump (S := S) M.projectedMax h_succ_const hmax

/-- Wrap-pump tropical barrier via the finite primary projection. -/
theorem no_tropical_primary_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} {β : Type}
    (M : TropicalPrimaryMeasure S β)
    (h_wrap_drift : 1 ≤ M.projectedMax.wrap_const + M.projectedMax.wrap_left) :
    ¬ (∀ (b s n : S.T),
      M.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hmax :
      ∀ b s n : S.T,
        M.projectedMax.eval (S.wrap s (S.recur b s n)) <
          M.projectedMax.eval (S.recur b s (S.succ n)) := by
    intro b s n
    have hlt := h b s n
    have hproj := M.lt_strict_primary hlt
    simpa [M.primary_eq] using hproj
  exact no_max_orients_dup_step_of_wrap_pump (S := S) M.projectedMax h_wrap_drift hmax

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

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
