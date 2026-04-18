import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Generalized Degree-Bounded Polynomial Barrier

This module extends the bounded multilinear story to finite polynomial tables
with arbitrary natural exponents in the three tracked scalar arguments
`M(b)`, `M(s)`, and `M(n)`.

The obstruction is expressed by an explicit frozen dominance condition at the
base point: after freezing `b = base` and comparing the source counter
`succ(base)` against the target counter `base`, the target-side polynomial must
eventually dominate the source-side polynomial as the pumped step value grows.

That condition is strong enough to force failure of strict orientation, and its
negation therefore becomes a necessary shape condition for any successful
polynomial escape within this direct family.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Finite polynomial monomials in the three tracked scalar arguments. -/
structure PolynomialMonomial where
  coeff : Nat
  basePow : Nat
  stepPow : Nat
  counterPow : Nat

namespace PolynomialMonomial

@[simp] def eval (m : PolynomialMonomial) (B S N : Nat) : Nat :=
  m.coeff * B ^ m.basePow * S ^ m.stepPow * N ^ m.counterPow

end PolynomialMonomial

/-- Finite polynomial-table constructor-local measures:
`succ` and `wrap` remain affine, while the recursor uses a finite polynomial
table in the three tracked scalar arguments. -/
structure BoundedPolynomialMeasure (S : StepDuplicatingSchema) where
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
  monomials : List PolynomialMonomial
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n +
          (monomials.map (fun m => m.eval (eval b) (eval s) (eval n))).sum
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

namespace BoundedPolynomialMeasure

@[simp] def sourceFrozenAtBase {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (Sval : Nat) : Nat :=
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval + M.recur_counter * succBase +
    (M.monomials.map (fun m => m.eval M.c_base Sval succBase)).sum

@[simp] def targetFrozenAtBase {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) (Sval : Nat) : Nat :=
  let inner :=
    M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval + M.recur_counter * M.c_base +
      (M.monomials.map (fun m => m.eval M.c_base Sval M.c_base)).sum
  M.wrap_const + M.wrap_left * Sval + M.wrap_right * inner

end BoundedPolynomialMeasure

/-- Unbounded range hypothesis for the generalized polynomial family. -/
def HasUnboundedRangePoly {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t

/-- Frozen dominance condition at the base point:
for sufficiently large pumped-step values, the target-side frozen polynomial
dominates the source-side frozen polynomial. -/
def EventuallyDominatedAtBase {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) : Prop :=
  ∃ K : Nat, ∀ Sval : Nat, K ≤ Sval →
    M.sourceFrozenAtBase Sval ≤ M.targetFrozenAtBase Sval

/-- Positive affine successor drift pumps the generalized polynomial family. -/
lemma eval_succIter_ge_poly {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero =>
      rw [succIter, M.eval_base]
      omega
  | succ k ih =>
      simp [succIter, M.eval_succ]
      nlinarith

/-- Positive affine wrap drift pumps the generalized polynomial family. -/
lemma eval_wrapIter_ge_poly {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (k : Nat) :
    k ≤ M.eval (wrapIter S k) := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      nlinarith [M.h_wrap_left_pos, h_wrap_bias, ih]

/-- Generalized polynomial barrier under frozen base-point dominance. -/
theorem no_polynomial_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (hunbounded : HasUnboundedRangePoly M)
    (hdom : EventuallyDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  rcases hdom with ⟨K, hK⟩
  rcases hunbounded K with ⟨s, hs⟩
  let Sval := M.eval s
  have hdomS : M.sourceFrozenAtBase Sval ≤ M.targetFrozenAtBase Sval := by
    exact hK Sval (by simpa [Sval] using hs)
  have hspec := h S.base s S.base
  have hsrc :
      M.eval (S.recur S.base s (S.succ S.base)) = M.sourceFrozenAtBase Sval := by
    rw [M.eval_recur, M.eval_succ, M.eval_base]
    simp [BoundedPolynomialMeasure.sourceFrozenAtBase, Sval, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, Nat.mul_add]
  have htgt :
      M.eval (S.wrap s (S.recur S.base s S.base)) = M.targetFrozenAtBase Sval := by
    rw [M.eval_wrap, M.eval_recur, M.eval_base]
    simp [BoundedPolynomialMeasure.targetFrozenAtBase, Sval, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, Nat.mul_add]
  rw [htgt, hsrc] at hspec
  exact Nat.not_lt_of_ge hdomS hspec

/-- Successor-pump specialization of the generalized polynomial barrier. -/
theorem no_polynomial_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hdom : EventuallyDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_polynomial_orients_dup_step_of_unbounded (M := M)
  · intro k
    refine ⟨succIter S k, ?_⟩
    simpa using eval_succIter_ge_poly (M := M) h_succ_bias h_succ_scale k
  · exact hdom

/-- Wrap-pump specialization of the generalized polynomial barrier. -/
theorem no_polynomial_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hdom : EventuallyDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_polynomial_orients_dup_step_of_unbounded (M := M)
  · intro k
    refine ⟨wrapIter S k, ?_⟩
    simpa using eval_wrapIter_ge_poly (M := M) h_wrap_bias k
  · exact hdom

/-- Any successful orienter in the generalized polynomial family must violate the
frozen dominance condition at the base point. -/
theorem polynomial_escape_requires_failure_of_base_dominance
    {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (hunbounded : HasUnboundedRangePoly M)
    (horient : ∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :
    ¬ EventuallyDominatedAtBase M := by
  intro hdom
  exact no_polynomial_orients_dup_step_of_unbounded M hunbounded hdom horient

/-- The generalized polynomial barrier lifts to global root orientation. -/
theorem no_global_orients_polynomial_of_unbounded
    {Sys : StepDuplicatingSystem}
    (M : BoundedPolynomialMeasure Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRangePoly M)
    (hdom : EventuallyDominatedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_polynomial_orients_dup_step_of_unbounded
      (S := Sys.toStepDuplicatingSchema) M hunbounded hdom
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
