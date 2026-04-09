import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Restricted Quadratic Barrier

This module inserts one bounded nonlinear layer between the existing affine barrier and the
known successful nonlinear witnesses.

The class formalized here keeps `succ` and `wrap` affine and allows the recursor to use one
extra pure counter-square term:

`eval (recur b s n) = const + base*B + step*S + counter*N + quad*N^2`.

There is no step-counter cross term. This keeps the theorem outside the existing RecΔ-core
witness, whose escape mechanism depends on coupling the step payload to the counter growth.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Restricted quadratic constructor-local measures:
`succ` and `wrap` are affine, while the recursor adds one pure counter-square term. -/
structure QuadraticCounterMeasure (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  recur_quad : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap :
    ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        recur_const + recur_base * eval b + recur_step * eval s +
          recur_counter * eval n + recur_quad * eval n * eval n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Unbounded range hypothesis for restricted quadratic schema theorems. -/
def HasUnboundedRangeQ {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t

/-- Positive successor drift still pumps restricted quadratic measures because the
successor constructor itself remains affine. -/
lemma eval_succIter_ge_quadratic {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero =>
      rw [succIter, M.eval_base]
      omega
  | succ k ih =>
      simp [succIter, M.eval_succ]
      nlinarith

/-- Positive wrap/base drift still pumps restricted quadratic measures because the
wrapper constructor itself remains affine. -/
lemma eval_wrapIter_ge_quadratic {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (k : Nat) :
    k ≤ M.eval (wrapIter S k) := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      nlinarith [M.h_wrap_left_pos, h_wrap_bias, ih]

/-- Restricted quadratic barrier:
without step-counter coupling, a pure counter-square term still does not rescue direct
orientation of the duplicating step. Pump the step argument and fix the counter at `base`. -/
theorem no_quadratic_counter_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (hunbounded : HasUnboundedRangeQ M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let threshold := M.recur_counter * succBase + M.recur_quad * succBase * succBase
  rcases hunbounded threshold with ⟨s, hs⟩
  let Sval := M.eval s
  let A := M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval
  let B := M.recur_counter * M.c_base
  let Q := M.recur_quad * M.c_base * M.c_base
  let T := M.recur_counter * succBase + M.recur_quad * succBase * succBase
  have hspec := h S.base s S.base
  have hspec' :
      M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) < A + T := by
    simpa [Sval, A, B, Q, T, succBase, M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hspec
  have hsT : T ≤ Sval := by
    simpa [T, threshold, Sval, succBase] using hs
  have hS : Sval ≤ M.wrap_left * Sval := by
    calc
      Sval = 1 * Sval := by simp
      _ ≤ M.wrap_left * Sval := Nat.mul_le_mul_right Sval M.h_wrap_left_pos
  have hABQ : A + B + Q ≤ M.wrap_right * (A + B + Q) := by
    calc
      A + B + Q = 1 * (A + B + Q) := by simp
      _ ≤ M.wrap_right * (A + B + Q) := Nat.mul_le_mul_right (A + B + Q) M.h_wrap_right_pos
  have h_rhs_to_aS : A + T ≤ A + Sval := Nat.add_le_add_left hsT A
  have h_aS_to_aWS : A + Sval ≤ A + M.wrap_left * Sval := Nat.add_le_add_left hS A
  have h_aWS_to_sum : A + M.wrap_left * Sval ≤ A + M.wrap_left * Sval + (B + Q) := by
    exact Nat.le_add_right _ _
  have h_sum_to_wsum :
      A + M.wrap_left * Sval + (B + Q) ≤
        M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
    have hABQ' :
        M.wrap_left * Sval + (A + B + Q) ≤
          M.wrap_left * Sval + M.wrap_right * (A + B + Q) :=
      Nat.add_le_add_left hABQ (M.wrap_left * Sval)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hABQ'
  have h_with_const :
      M.wrap_left * Sval + M.wrap_right * (A + B + Q) ≤
        M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
    calc
      M.wrap_left * Sval + M.wrap_right * (A + B + Q)
          ≤ M.wrap_const + (M.wrap_left * Sval + M.wrap_right * (A + B + Q)) := by
            exact Nat.le_add_left _ _
      _ = M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
        simp [Nat.add_assoc]
  have hge :
      A + T ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
    exact le_trans h_rhs_to_aS <|
      le_trans h_aS_to_aWS <|
      le_trans h_aWS_to_sum <|
      le_trans h_sum_to_wsum h_with_const
  exact Nat.not_lt_of_ge hge hspec'

/-- Positive successor drift gives the restricted quadratic barrier via a `succ` pump. -/
theorem no_quadratic_counter_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_quadratic_counter_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa using eval_succIter_ge_quadratic (M := M) h_succ_bias h_succ_scale k

/-- Positive wrap/base drift gives the restricted quadratic barrier via a `wrap` pump. -/
theorem no_quadratic_counter_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_quadratic_counter_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa using eval_wrapIter_ge_quadratic (M := M) h_wrap_bias k

/-- Any globally oriented system containing the duplicating step would orient that step.
The restricted quadratic barrier therefore also lifts to global root orientation. -/
theorem no_global_orients_quadratic_of_unbounded
    {Sys : StepDuplicatingSystem} (M : QuadraticCounterMeasure Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRangeQ M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_quadratic_counter_orients_dup_step_of_unbounded
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Positive successor drift yields the restricted quadratic global barrier. -/
theorem no_global_orients_quadratic_of_succ_pump
    {Sys : StepDuplicatingSystem} (M : QuadraticCounterMeasure Sys.toStepDuplicatingSchema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_quadratic_of_unbounded (M := M)
  intro k
  refine ⟨succIter Sys.toStepDuplicatingSchema k, ?_⟩
  simpa using eval_succIter_ge_quadratic (M := M) h_succ_bias h_succ_scale k

/-- Positive wrap/base drift yields the restricted quadratic global barrier. -/
theorem no_global_orients_quadratic_of_wrap_pump
    {Sys : StepDuplicatingSystem} (M : QuadraticCounterMeasure Sys.toStepDuplicatingSchema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_quadratic_of_unbounded (M := M)
  intro k
  refine ⟨wrapIter Sys.toStepDuplicatingSchema k, ?_⟩
  simpa using eval_wrapIter_ge_quadratic (M := M) h_wrap_bias k

/-- Any Nat-valued global orienter is not representable by a restricted quadratic
measure from this barrier class when the measure satisfies the same unbounded pump
hypothesis used by the schema theorem. -/
theorem global_orienter_not_quadratic_unbounded_representable
    {Sys : StepDuplicatingSystem} (μ : Sys.T → Nat)
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ ∃ M : QuadraticCounterMeasure Sys.toStepDuplicatingSchema,
        HasUnboundedRangeQ M ∧ M.eval = μ := by
  intro hrep
  rcases hrep with ⟨M, hunbounded, hM⟩
  subst hM
  exact (no_global_orients_quadratic_of_unbounded (Sys := Sys) M hunbounded) horient

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

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
