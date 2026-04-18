import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Max-Based Depth Barrier

This module provides the max-aggregative depth barrier at two layers:

- a generic **schema-level** family `MaxDepthMeasure S` over an arbitrary
  `StepDuplicatingSchema`, with the corresponding impossibility theorem
  `no_maxDepth_orients_dup_step` and its `GlobalOrients` corollary; and
- the original **KO7-specific** max-aggregative depth family, now re-derived
  as a thin corollary via a `toSchemaMeasure` projection that forgets the
  unused extra constructor weights (`c_integrate`, `c_merge`, `c_eq`).

The schema proof is discharged on the concrete duplicating-rule instance
with `b = base`, `s = succ base`, `n = base`.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- A schema-level max-aggregative depth family.

`succ` adds a unary bump and forwards its argument; `wrap` and `recur`
add an outer bump on top of the maximum depth of their visible branches.
The only load-bearing side condition is `h_wrap_pos : 1 ≤ c_wrap`: the
duplicating rule exposes the step argument under an extra wrapper, and a
positive wrapper offset forces that exposure to strictly increase depth. -/
structure MaxDepthMeasure (S : StepDuplicatingSchema) where
  eval       : S.T → Nat
  c_base     : Nat
  c_succ     : Nat
  c_wrap     : Nat
  c_recur    : Nat
  eval_base  : eval S.base = c_base
  eval_succ  : ∀ t, eval (S.succ t) = c_succ + eval t
  eval_wrap  : ∀ x y, eval (S.wrap x y) = c_wrap + max (eval x) (eval y)
  eval_recur : ∀ b s n,
    eval (S.recur b s n) = c_recur + max (max (eval b) (eval s)) (eval n)
  h_wrap_pos : 1 ≤ c_wrap

/-- **Schema-level max-aggregative depth barrier.**

No such measure can strictly orient the duplicating rule uniformly. The
contradiction falls out of the concrete instance `b = base`, `s = succ base`,
`n = base`, where both sides share the same frozen branches and the target
is exactly `c_wrap` larger than the source. -/
theorem no_maxDepth_orients_dup_step
    {S : StepDuplicatingSchema} (M : MaxDepthMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hspec := h S.base (S.succ S.base) S.base
  rw [M.eval_wrap, M.eval_recur, M.eval_recur, M.eval_succ, M.eval_base] at hspec
  have hwrap := M.h_wrap_pos
  omega

/-- Unbounded-range hypothesis is not needed; the barrier is unconditional. -/
theorem no_global_orients_maxDepth
    {Sys : StepDuplicatingSystem} (M : MaxDepthMeasure Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_maxDepth_orients_dup_step
      (S := Sys.toStepDuplicatingSchema) M
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
