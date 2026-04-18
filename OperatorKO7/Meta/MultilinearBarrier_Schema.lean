import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Bounded Multilinear Barrier

This module extends the scalar barrier stack beyond the single bounded cross-term
quadratic regime. The recursor may contain a finite table of multilinear monomials
in the three tracked scalar arguments `M(b)`, `M(s)`, and `M(n)`, with each variable
appearing at most once per monomial.

The theorem remains explicitly bounded. After freezing `b = base`, the only live
difference between source and target lies in:
- the counter value changing from `succ(base)` to `base`
- the total coefficient of the pumped step payload `M(s)`

If the wrapper gain still dominates that frozen source coefficient at the base point,
strict orientation remains impossible.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- A multilinear monomial in the scalar arguments `B = M(b)`, `S = M(s)`, `N = M(n)`. -/
structure MultilinearMonomial where
  coeff : Nat
  useBase : Bool
  useStep : Bool
  useCounter : Bool

namespace MultilinearMonomial

@[simp] def factor (flag : Bool) (x : Nat) : Nat :=
  if flag then x else 1

/-- Full monomial evaluation on the three scalar arguments. -/
@[simp] def eval (m : MultilinearMonomial) (B S N : Nat) : Nat :=
  m.coeff * factor m.useBase B * factor m.useStep S * factor m.useCounter N

/-- Frozen constant contribution when the pumped step variable is separated out. -/
@[simp] def constPart (m : MultilinearMonomial) (B N : Nat) : Nat :=
  if m.useStep then 0 else m.coeff * factor m.useBase B * factor m.useCounter N

/-- Coefficient of the pumped step variable after freezing the other arguments. -/
@[simp] def stepCoeff (m : MultilinearMonomial) (B N : Nat) : Nat :=
  if m.useStep then m.coeff * factor m.useBase B * factor m.useCounter N else 0

lemma eval_eq_constPart_add_stepCoeff (m : MultilinearMonomial) (B S N : Nat) :
    m.eval B S N = m.constPart B N + m.stepCoeff B N * S := by
  cases h : m.useStep <;>
    simp [eval, constPart, stepCoeff, factor, h, Nat.mul_left_comm, Nat.mul_comm]

end MultilinearMonomial

/-- Full multilinear-table evaluation. -/
@[simp] def monomialEvalSum : List MultilinearMonomial → Nat → Nat → Nat → Nat
  | [], _, _, _ => 0
  | m :: ms, B, S, N => m.eval B S N + monomialEvalSum ms B S N

/-- Sum of frozen constant parts over a multilinear table. -/
@[simp] def monomialConstSum : List MultilinearMonomial → Nat → Nat → Nat
  | [], _, _ => 0
  | m :: ms, B, N => m.constPart B N + monomialConstSum ms B N

/-- Sum of frozen step coefficients over a multilinear table. -/
@[simp] def monomialStepCoeffSum : List MultilinearMonomial → Nat → Nat → Nat
  | [], _, _ => 0
  | m :: ms, B, N => m.stepCoeff B N + monomialStepCoeffSum ms B N

/-- After freezing `B` and `N`, a multilinear table becomes an affine function of `S`. -/
lemma monomialSum_eq_constPart_add_stepCoeff
    (ms : List MultilinearMonomial) (B S N : Nat) :
    monomialEvalSum ms B S N =
      monomialConstSum ms B N + monomialStepCoeffSum ms B N * S := by
  induction ms with
  | nil =>
      simp
  | cons m ms ih =>
      cases hb : m.useBase <;> cases hs : m.useStep <;> cases hn : m.useCounter <;>
        (simp [hb, hs, hn, ih, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc]
         <;> try ring_nf)

/-- Finite multilinear constructor-local measures:
`succ` and `wrap` are affine, while the recursor adds a finite multilinear monomial table. -/
structure BoundedMultilinearMeasure (S : StepDuplicatingSchema) where
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
  monomials : List MultilinearMonomial
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap :
    ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        recur_const + recur_base * eval b + recur_step * eval s +
          recur_counter * eval n +
          monomialEvalSum monomials (eval b) (eval s) (eval n)
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

namespace BoundedMultilinearMeasure

@[simp] def constPartSum {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (B N : Nat) : Nat :=
  monomialConstSum M.monomials B N

@[simp] def stepCoeffSum {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (B N : Nat) : Nat :=
  monomialStepCoeffSum M.monomials B N

lemma monomialSum_eq_constPart_add_stepCoeff
    {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S) (B Sval N : Nat) :
    monomialEvalSum M.monomials B Sval N =
      M.constPartSum B N + M.stepCoeffSum B N * Sval := by
  simpa [constPartSum, stepCoeffSum] using
    (StepDuplicatingSchema.monomialSum_eq_constPart_add_stepCoeff M.monomials B Sval N)

end BoundedMultilinearMeasure

/-- Unbounded range hypothesis for the bounded multilinear barrier. -/
def HasUnboundedRangeML {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t

/-- Base-point dominance condition:
after freezing `b = base`, the wrapper gain still dominates the total pumped-step coefficient
when the source uses `succ(base)` and the target uses `base`. -/
def MultilinearDominatedAtBase {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) : Prop :=
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let sourceCoeff := M.recur_step + M.stepCoeffSum M.c_base succBase
  let targetCoeff := M.wrap_left + M.wrap_right * (M.recur_step + M.stepCoeffSum M.c_base M.c_base)
  sourceCoeff + 1 ≤ targetCoeff

/-- Positive successor drift still pumps the multilinear family because the successor
constructor itself remains affine. -/
lemma eval_succIter_ge_multilinear {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero =>
      rw [succIter, M.eval_base]
      omega
  | succ k ih =>
      simp [succIter, M.eval_succ]
      nlinarith

/-- Positive wrap/base drift still pumps the multilinear family because the wrapper
itself remains affine. -/
lemma eval_wrapIter_ge_multilinear {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (k : Nat) :
    k ≤ M.eval (wrapIter S k) := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      nlinarith [M.h_wrap_left_pos, h_wrap_bias, ih]

/-- Finite multilinear barrier:
if the total frozen pumped-step coefficient remains dominated by the wrapper gain at the
base point, the duplicating step still cannot be oriented uniformly. -/
theorem no_multilinear_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (hunbounded : HasUnboundedRangeML M)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  let succBase := M.succ_bias + M.succ_scale * M.c_base
  let sourceCoeff := M.recur_step + M.stepCoeffSum M.c_base succBase
  let targetCoeff := M.wrap_left + M.wrap_right * (M.recur_step + M.stepCoeffSum M.c_base M.c_base)
  let sourceConst :=
    M.recur_const + M.recur_base * M.c_base + M.recur_counter * succBase +
      M.constPartSum M.c_base succBase
  rcases hunbounded sourceConst with ⟨s, hs⟩
  let Sval := M.eval s
  let targetInnerConst :=
    M.recur_const + M.recur_base * M.c_base + M.recur_counter * M.c_base +
      M.constPartSum M.c_base M.c_base
  let targetConst := M.wrap_const + M.wrap_right * targetInnerConst
  have hspec := h S.base s S.base
  have hsourceMono :
      monomialEvalSum M.monomials M.c_base Sval succBase =
        M.constPartSum M.c_base succBase + M.stepCoeffSum M.c_base succBase * Sval := by
    simpa [Sval] using M.monomialSum_eq_constPart_add_stepCoeff M.c_base Sval succBase
  have htargetMono :
      monomialEvalSum M.monomials M.c_base Sval M.c_base =
        M.constPartSum M.c_base M.c_base + M.stepCoeffSum M.c_base M.c_base * Sval := by
    simpa [Sval] using M.monomialSum_eq_constPart_add_stepCoeff M.c_base Sval M.c_base
  have hspec' :
      targetConst + targetCoeff * Sval < sourceConst + sourceCoeff * Sval := by
    rw [M.eval_wrap, M.eval_recur, M.eval_recur, M.eval_succ] at hspec
    simp only [M.eval_base] at hspec
    rw [hsourceMono, htargetMono] at hspec
    simpa [Sval, succBase, sourceCoeff, targetCoeff, sourceConst, targetInnerConst, targetConst, M.eval_base,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hspec
  have hs0 : sourceConst ≤ Sval := by
    simpa [sourceConst, succBase, Sval] using hs
  have hcoeff : sourceCoeff + 1 ≤ targetCoeff := by
    simpa [MultilinearDominatedAtBase, succBase, sourceCoeff, targetCoeff] using hdom
  have hmul : (sourceCoeff + 1) * Sval ≤ targetCoeff * Sval := by
    exact Nat.mul_le_mul_right Sval hcoeff
  have hsource_to_mul :
      sourceConst + sourceCoeff * Sval ≤ (sourceCoeff + 1) * Sval := by
    nlinarith
  have htarget_nonneg : targetCoeff * Sval ≤ targetConst + targetCoeff * Sval := by
    exact Nat.le_add_left _ _
  have hge :
      sourceConst + sourceCoeff * Sval ≤ targetConst + targetCoeff * Sval := by
    exact le_trans hsource_to_mul <| le_trans hmul htarget_nonneg
  exact Nat.not_lt_of_ge hge hspec'

/-- Successor-pump specialization of the finite multilinear barrier. -/
theorem no_multilinear_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_multilinear_orients_dup_step_of_unbounded (M := M)
  · intro k
    refine ⟨succIter S k, ?_⟩
    simpa using eval_succIter_ge_multilinear (M := M) h_succ_bias h_succ_scale k
  · exact hdom

/-- Wrap-pump specialization of the finite multilinear barrier. -/
theorem no_multilinear_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_multilinear_orients_dup_step_of_unbounded (M := M)
  · intro k
    refine ⟨wrapIter S k, ?_⟩
    simpa using eval_wrapIter_ge_multilinear (M := M) h_wrap_bias k
  · exact hdom

/-- The multilinear barrier lifts to global root orientation. -/
theorem no_global_orients_multilinear_of_unbounded
    {Sys : StepDuplicatingSystem} (M : BoundedMultilinearMeasure Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRangeML M)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_multilinear_orients_dup_step_of_unbounded
      (S := Sys.toStepDuplicatingSchema) M hunbounded hdom
      (fun b s n => h (Sys.dup_step b s n))

/-- Successor-pump global specialization of the multilinear barrier. -/
theorem no_global_orients_multilinear_of_succ_pump
    {Sys : StepDuplicatingSystem} (M : BoundedMultilinearMeasure Sys.toStepDuplicatingSchema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_multilinear_of_unbounded (M := M)
  · intro k
    refine ⟨succIter Sys.toStepDuplicatingSchema k, ?_⟩
    simpa using eval_succIter_ge_multilinear (M := M) h_succ_bias h_succ_scale k
  · exact hdom

/-- Wrap-pump global specialization of the multilinear barrier. -/
theorem no_global_orients_multilinear_of_wrap_pump
    {Sys : StepDuplicatingSystem} (M : BoundedMultilinearMeasure Sys.toStepDuplicatingSchema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_multilinear_of_unbounded (M := M)
  · intro k
    refine ⟨wrapIter Sys.toStepDuplicatingSchema k, ?_⟩
    simpa using eval_wrapIter_ge_multilinear (M := M) h_wrap_bias k
  · exact hdom

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
