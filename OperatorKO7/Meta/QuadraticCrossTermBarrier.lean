import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Bounded Cross-Term Quadratic Barrier

This module strengthens the restricted quadratic barrier by allowing one explicit step-counter
cross term in the recursor, but only inside a bounded coupling regime.

The recursor shape is:

`eval (recur b s n) = const + base*B + step*S + counter*N + quad*N^2 + cross*S*N`.

The theorem below does **not** cover arbitrary cross terms. It isolates a concrete regime in
which the wrapper gain still dominates the cross-term contribution after one successor step.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Constructor-local quadratic measures with one explicit step-counter cross term. -/
structure CrossTermQuadraticMeasure (S : StepDuplicatingSchema) where
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
  recur_cross : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap :
    ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        recur_const + recur_base * eval b + recur_step * eval s +
          recur_counter * eval n + recur_quad * eval n * eval n +
          recur_cross * eval s * eval n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Unbounded range hypothesis for the bounded cross-term barrier. -/
def HasUnboundedRangeX {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t

/-- A bounded-cross regime at the base point: the wrapper gain in the pumped step argument
still dominates one successor-step increase in the cross term. -/
def CrossTermBoundedAtBase {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) : Prop :=
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  M.recur_step + M.recur_cross * succBase + 1 ≤
    M.wrap_left + M.wrap_right * (M.recur_step + M.recur_cross * M.c_base)

/-- Positive successor drift still pumps the cross-term family because the successor constructor
itself remains affine. -/
lemma eval_succIter_ge_cross {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero =>
      rw [succIter, M.eval_base]
      omega
  | succ k ih =>
      simp [succIter, M.eval_succ]
      nlinarith

/-- Positive wrap/base drift still pumps the cross-term family because the wrapper itself
remains affine. -/
lemma eval_wrapIter_ge_cross {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (k : Nat) :
    k ≤ M.eval (wrapIter S k) := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      nlinarith [M.h_wrap_left_pos, h_wrap_bias, ih]

/-- Bounded cross-term quadratic barrier:
if the step-counter coupling stays below the explicit base-point wrapper-dominance bound,
the duplicating step still cannot be oriented uniformly. -/
theorem no_cross_quadratic_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (hunbounded : HasUnboundedRangeX M)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let sourceCoeff := M.recur_step + M.recur_cross * succBase
  let targetCoeff := M.wrap_left + M.wrap_right * (M.recur_step + M.recur_cross * M.c_base)
  let sourceConst :=
    M.recur_const + M.recur_base * M.c_base +
      M.recur_counter * succBase + M.recur_quad * succBase * succBase
  rcases hunbounded sourceConst with ⟨s, hs⟩
  let Sval := M.eval s
  let targetConst :=
    M.wrap_const +
      M.wrap_right *
        (M.recur_const + M.recur_base * M.c_base +
          M.recur_counter * M.c_base + M.recur_quad * M.c_base * M.c_base)
  have hspec := h S.base s S.base
  have hspec' :
      targetConst + targetCoeff * Sval < sourceConst + sourceCoeff * Sval := by
    simpa [Sval, succBase, sourceCoeff, targetCoeff, sourceConst, targetConst,
      M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hspec
  have hs0 : sourceConst ≤ Sval := by
    simpa [sourceConst, succBase, Sval] using hs
  have hcoeff : sourceCoeff + 1 ≤ targetCoeff := by
    simpa [CrossTermBoundedAtBase, succBase, sourceCoeff, targetCoeff] using hbounded
  have hmul :
      (sourceCoeff + 1) * Sval ≤ targetCoeff * Sval := by
    exact Nat.mul_le_mul_right Sval hcoeff
  have hsource_to_mul :
      sourceConst + sourceCoeff * Sval ≤ (sourceCoeff + 1) * Sval := by
    nlinarith
  have htarget_nonneg :
      targetCoeff * Sval ≤ targetConst + targetCoeff * Sval := by
    exact Nat.le_add_left _ _
  have hge :
      sourceConst + sourceCoeff * Sval ≤ targetConst + targetCoeff * Sval := by
    exact le_trans hsource_to_mul <| le_trans hmul htarget_nonneg
  exact Nat.not_lt_of_ge hge hspec'

/-- Positive successor drift specializes the bounded cross-term barrier via a successor pump. -/
theorem no_cross_quadratic_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_cross_quadratic_orients_dup_step_of_unbounded (M := M)
  · intro k
    refine ⟨succIter S k, ?_⟩
    simpa using eval_succIter_ge_cross (M := M) h_succ_bias h_succ_scale k
  · exact hbounded

/-- Positive wrap/base drift specializes the bounded cross-term barrier via a wrapper pump. -/
theorem no_cross_quadratic_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_cross_quadratic_orients_dup_step_of_unbounded (M := M)
  · intro k
    refine ⟨wrapIter S k, ?_⟩
    simpa using eval_wrapIter_ge_cross (M := M) h_wrap_bias k
  · exact hbounded

/-- The bounded cross-term barrier also lifts to global root orientation. -/
theorem no_global_orients_cross_quadratic_of_unbounded
    {Sys : StepDuplicatingSystem} (M : CrossTermQuadraticMeasure Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRangeX M)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_cross_quadratic_orients_dup_step_of_unbounded
      (S := Sys.toStepDuplicatingSchema) M hunbounded hbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Successor-pump global specialization for the bounded cross-term barrier. -/
theorem no_global_orients_cross_quadratic_of_succ_pump
    {Sys : StepDuplicatingSystem} (M : CrossTermQuadraticMeasure Sys.toStepDuplicatingSchema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_cross_quadratic_of_unbounded (M := M)
  · intro k
    refine ⟨succIter Sys.toStepDuplicatingSchema k, ?_⟩
    simpa using eval_succIter_ge_cross (M := M) h_succ_bias h_succ_scale k
  · exact hbounded

/-- Wrap-pump global specialization for the bounded cross-term barrier. -/
theorem no_global_orients_cross_quadratic_of_wrap_pump
    {Sys : StepDuplicatingSystem} (M : CrossTermQuadraticMeasure Sys.toStepDuplicatingSchema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_cross_quadratic_of_unbounded (M := M)
  · intro k
    refine ⟨wrapIter Sys.toStepDuplicatingSchema k, ?_⟩
    simpa using eval_wrapIter_ge_cross (M := M) h_wrap_bias k
  · exact hbounded

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.QuadraticCrossTermBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 root-orientation also fails for the bounded cross-term quadratic family. -/
theorem no_global_step_orientation_cross_quadratic_of_unbounded
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeX M)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_cross_quadratic_of_unbounded
      (Sys := ko7System) M hunbounded hbounded

/-- KO7 successor-pump specialization of the bounded cross-term quadratic barrier. -/
theorem no_global_step_orientation_cross_quadratic_of_succ_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_cross_quadratic_of_succ_pump
      (Sys := ko7System) M h_succ_bias h_succ_scale hbounded

/-- KO7 wrap-pump specialization of the bounded cross-term quadratic barrier. -/
theorem no_global_step_orientation_cross_quadratic_of_wrap_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hbounded : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_cross_quadratic_of_wrap_pump
      (Sys := ko7System) M h_wrap_bias hbounded

end OperatorKO7.QuadraticCrossTermBarrier
