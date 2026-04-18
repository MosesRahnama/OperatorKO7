import OperatorKO7.Meta.MatrixBarrierD_Schema
import OperatorKO7.Meta.MatrixBarrierLexD_Schema

/-!
# Projected-Primary Dominance Barrier

Many direct vector families in the orientation-boundary stack share the same proof pattern:

- the ambient order forces a designated primary scalar projection to be non-increasing;
- the designated primary scalar itself is an affine direct measure with the usual pump;
- the duplicating step forces that primary scalar to rise beyond any such non-increase.

This module packages that pattern once.

The abstraction is deliberately weak and therefore broad:
it does not ask the ambient order to strictly decrease the primary scalar, only to make it
non-increasing. This is enough to subsume both:

- strict componentwise vector orders, where every tracked coordinate decreases strictly;
- tracked-primary lexicographic vector orders, where the primary coordinate may stay equal
  but can never increase.

The theorem is schema-level and then specialized back to the existing fixed-dimension
componentwise and lexicographic families as compatibility corollaries.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- A stronger scalar barrier: no affine direct measure with an unbounded pump can make the
duplicating step merely non-increasing. The primary scalar must eventually rise. -/
theorem no_affine_primary_nonstrict_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : AffineMeasure S) (hunbounded : HasUnboundedRange M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) ≤ M.eval (S.recur b s (S.succ n))) := by
  intro h
  let threshold := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  rcases hunbounded (threshold + 1) with ⟨s, hs⟩
  let Sval := M.eval s
  let A := M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval
  let B := M.recur_counter * M.c_base
  let T := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  have hspec := h S.base s S.base
  have hle_spec' :
      M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) ≤ A + T := by
    simpa [Sval, A, B, T, M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add] using hspec
  have hsT1 : T + 1 ≤ Sval := by
    simpa [threshold, T, Sval] using hs
  have hS : Sval ≤ M.wrap_left * Sval := by
    calc
      Sval = 1 * Sval := by simp
      _ ≤ M.wrap_left * Sval := by
        exact Nat.mul_le_mul_right Sval M.h_wrap_left_pos
  have hAB : A + B ≤ M.wrap_right * (A + B) := by
    calc
      A + B = 1 * (A + B) := by simp
      _ ≤ M.wrap_right * (A + B) := by
        exact Nat.mul_le_mul_right (A + B) M.h_wrap_right_pos
  have h_rhs_to_aS1 : A + (T + 1) ≤ A + Sval := Nat.add_le_add_left hsT1 A
  have h_aS_to_aWS : A + Sval ≤ A + M.wrap_left * Sval := Nat.add_le_add_left hS A
  have h_aWS_to_sum : A + M.wrap_left * Sval ≤ A + M.wrap_left * Sval + B := by
    exact Nat.le_add_right _ _
  have h_sum_to_wsum :
      A + M.wrap_left * Sval + B ≤ M.wrap_left * Sval + M.wrap_right * (A + B) := by
    have hAB' :
        M.wrap_left * Sval + (A + B) ≤
          M.wrap_left * Sval + M.wrap_right * (A + B) :=
      Nat.add_le_add_left hAB (M.wrap_left * Sval)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAB'
  have h_with_const :
      M.wrap_left * Sval + M.wrap_right * (A + B) ≤
        M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
    calc
      M.wrap_left * Sval + M.wrap_right * (A + B)
          ≤ M.wrap_const + (M.wrap_left * Sval + M.wrap_right * (A + B)) := by
            exact Nat.le_add_left _ _
      _ = M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
        simp [Nat.add_assoc]
  have hgt :
      A + T + 1 ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
    have htmp :
        A + (T + 1) ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
      exact le_trans h_rhs_to_aS1 <|
        le_trans h_aS_to_aWS <|
        le_trans h_aWS_to_sum <|
        le_trans h_sum_to_wsum h_with_const
    simpa [Nat.add_assoc] using htmp
  omega

/-- Successor-pump corollary for the non-strict primary barrier. -/
theorem no_affine_primary_nonstrict_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) ≤ M.eval (S.recur b s (S.succ n))) := by
  apply no_affine_primary_nonstrict_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa using eval_succIter_ge M h_succ_bias h_succ_scale k

/-- Wrap-pump corollary for the non-strict primary barrier. -/
theorem no_affine_primary_nonstrict_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) ≤ M.eval (S.recur b s (S.succ n))) := by
  apply no_affine_primary_nonstrict_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa using eval_wrapIter_ge_affine M h_wrap_bias k

/-- Generic projected-primary barrier. If the ambient order forces a chosen scalar
projection to be non-increasing, and that projection is an affine direct measure with an
unbounded pump, then the ambient order cannot orient the duplicating step uniformly. -/
theorem no_orients_dup_step_of_projected_primary_dominance
    {S : StepDuplicatingSchema} {α : Type}
    (μ : S.T → α) (R : α → α → Prop) (π : α → Nat)
    (hdom : ∀ {u v : α}, R u v → π u ≤ π v)
    (M : AffineMeasure S)
    (heval : ∀ t : S.T, M.eval t = π (μ t))
    (hunbounded : HasUnboundedRange M) :
    ¬ (∀ (b s n : S.T), R (μ (S.wrap s (S.recur b s n))) (μ (S.recur b s (S.succ n)))) := by
  intro h
  have hprimary :
      ∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) ≤ M.eval (S.recur b s (S.succ n)) := by
    intro b s n
    have hproj : π (μ (S.wrap s (S.recur b s n))) ≤ π (μ (S.recur b s (S.succ n))) :=
      hdom (h b s n)
    simpa [heval (S.wrap s (S.recur b s n)), heval (S.recur b s (S.succ n))] using hproj
  exact no_affine_primary_nonstrict_orients_dup_step_of_unbounded M hunbounded hprimary

/-- Global version of the projected-primary dominance barrier. -/
theorem no_global_orients_of_projected_primary_dominance
    {Sys : StepDuplicatingSystem} {α : Type}
    (μ : Sys.toStepDuplicatingSchema.T → α) (R : α → α → Prop) (π : α → Nat)
    (hdom : ∀ {u v : α}, R u v → π u ≤ π v)
    (M : AffineMeasure Sys.toStepDuplicatingSchema)
    (heval : ∀ t : Sys.toStepDuplicatingSchema.T, M.eval t = π (μ t))
    (hunbounded : HasUnboundedRange M) :
    ¬ GlobalOrients Sys μ R := by
  intro h
  exact
    no_orients_dup_step_of_projected_primary_dominance
      (μ := μ) (R := R) (π := π) hdom M heval hunbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- The fixed-dimension tracked componentwise family is an instance of the generic
projected-primary dominance theorem. -/
theorem no_matrixD_orients_dup_step_of_componentwise_pump_via_primary_dominance
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (hunbounded : HasUnboundedRangeTracked M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_orients_dup_step_of_projected_primary_dominance
    (μ := M.eval) (R := VecLt) (π := fun v => v tracked) (M := M.trackedAffine)
  · intro u v h
    exact Nat.le_of_lt (h tracked)
  · intro t
    rfl
  · intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, ht⟩

/-- The finite tracked-primary lexicographic family is also an instance of the generic
projected-primary dominance theorem. -/
theorem no_matrixLexD_orients_dup_step_of_unbounded_primary_via_primary_dominance
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexMeasureD S d)
    (hunbounded : HasUnboundedPrimaryRange M) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_orients_dup_step_of_projected_primary_dominance
    (μ := M.eval) (R := VecLexLt) (π := fun v => v (primaryIdx d)) (M := M.primaryAffine)
  · intro u v h
    exact primary_le_of_vecLexLt h
  · intro t
    rfl
  · intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, ht⟩

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
