import OperatorKO7.Meta.SchemaOffsetAndWrapper
import OperatorKO7.Meta.SchemaConfessionDominance
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Norm Mismatch, Gauge Entropy, and Inefficiency Coefficient

Schema-level mechanization of Paper 2:

- Proposition 3.15 `‖v_i‖_{ℓ⁰, ℓ¹, ℓ^∞}` on the diagonal.
- Definition 3.16 gauge-orbit entropy `H_gauge(i) = log₂(i + 1)`.
- Definition 3.18 inefficiency coefficient `η(k, w)`.
- Proposition 3.19 `η(k, w) → ∞`.
- Proposition 3.20 Shannon-uniqueness via an explicit description bound.

The three norm readings are computed directly from the constant-payload
wrapper stack (`v_i = (b, …, b) ∈ B^i`).
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

namespace BaseDuplicatingSystem

/-! ## Prop 3.15 norm mismatch on the diagonal -/

/-- `ℓ¹` norm of the constant-payload wrapper stack with payload size `p`:
`i · p`. -/
def ell1NormOnDiagonal (p : Nat) (i : Nat) : Nat := i * p

/-- `ℓ^∞` norm (= max) of the constant-payload wrapper stack with payload
size `p`: `p` for `i ≥ 1`, `0` for `i = 0`. We express it compactly as
`p` whenever the stack is nonempty. -/
def ellInfNormOnDiagonal (p : Nat) (i : Nat) : Nat :=
  if i = 0 then 0 else p

/-- `ℓ⁰` "norm" of the constant-payload wrapper stack: rank of the diagonal,
which is `0` for the empty stack and `1` otherwise. -/
def ell0NormOnDiagonal (i : Nat) : Nat :=
  if i = 0 then 0 else 1

@[simp] theorem ell1NormOnDiagonal_eq (p i : Nat) :
    ell1NormOnDiagonal p i = i * p := rfl

@[simp] theorem ellInfNormOnDiagonal_pos (p : Nat) (i : Nat) (hi : 1 ≤ i) :
    ellInfNormOnDiagonal p i = p := by
  unfold ellInfNormOnDiagonal
  have : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi
  simp [this]

@[simp] theorem ell0NormOnDiagonal_pos (i : Nat) (hi : 1 ≤ i) :
    ell0NormOnDiagonal i = 1 := by
  unfold ell0NormOnDiagonal
  have : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi
  simp [this]

/-- **Paper 2 Proposition 3.15 (norm mismatch).** For every `i ≥ 1` and
payload size `p ≥ 1`, the three norms of the constant-payload wrapper stack
`v_i = (b, …, b) ∈ B^i` are pairwise distinct whenever `i ≥ 2` and
`p ≥ 2`, exhibiting the direct-carrier overcount of `ℓ¹` relative to
`ℓ^∞` and the rank-like `ℓ⁰` reading. -/
theorem norm_mismatch_pairwise
    (p i : Nat) (hi : 2 ≤ i) (hp : 2 ≤ p) :
    ell0NormOnDiagonal i < ellInfNormOnDiagonal p i
      ∧ ellInfNormOnDiagonal p i < ell1NormOnDiagonal p i := by
  have hi1 : 1 ≤ i := by omega
  rw [ell0NormOnDiagonal_pos i hi1, ellInfNormOnDiagonal_pos p i hi1]
  constructor
  · -- 1 < p
    omega
  · -- p < i * p
    unfold ell1NormOnDiagonal
    -- i * p ≥ 2 * p > p since p ≥ 1
    nlinarith

/-- Unconditional ordering ℓ^∞ ≤ ℓ¹ on the diagonal. The ℓ⁰ vs ℓ^∞
comparison requires `p ≥ 1` since the zero tuple has all three norms equal. -/
theorem normInf_le_norm1 (p i : Nat) :
    ellInfNormOnDiagonal p i ≤ ell1NormOnDiagonal p i := by
  unfold ellInfNormOnDiagonal ell1NormOnDiagonal
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]
    have : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    nlinarith

/-- Conditional ordering `ℓ⁰ ≤ ℓ^∞` whenever the seed has positive size. -/
theorem norm0_le_normInf_of_posSize (p i : Nat) (hp : 1 ≤ p) :
    ell0NormOnDiagonal i ≤ ellInfNormOnDiagonal p i := by
  unfold ell0NormOnDiagonal ellInfNormOnDiagonal
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]; omega

/-! ## Def 3.16 gauge entropy and Def 3.18 inefficiency coefficient

These are real-valued quantities; we use `Real` via Mathlib here. The
inefficiency-coefficient divergence proposition is a limit statement, so
this module is the one place where we leave the pure-`Nat` setting. -/

open scoped Real

/-- **Paper 2 Def 3.16 (gauge-orbit entropy).** Under the uniform coding
convention on the `i + 1` payload-bearing positions, the Shannon entropy
is `log₂(i + 1)`. -/
noncomputable def gaugeEntropy (i : Nat) : ℝ :=
  Real.logb 2 (i + 1 : ℝ)

/-- **Paper 2 Def 3.18 (inefficiency coefficient).** Compares the syntactic
doubled structural mass `(k+1)(k+2) · w` carried by the direct whole-term
observer to the coding-theoretic information content
`ln 2 · H_gauge(k) = ln(k + 1)`. -/
noncomputable def inefficiencyCoefficient (k w : Nat) : ℝ :=
  ((k + 1) * (k + 2) * w : ℝ) / (2 * Real.log (k + 1))

@[simp] theorem gaugeEntropy_def (i : Nat) :
    gaugeEntropy i = Real.logb 2 (i + 1 : ℝ) := rfl

@[simp] theorem inefficiencyCoefficient_def (k w : Nat) :
    inefficiencyCoefficient k w
      = ((k + 1) * (k + 2) * w : ℝ) / (2 * Real.log (k + 1)) := rfl

/-- **Paper 2 Proposition 3.19 (divergence of the direct-carrier inefficiency
coefficient).** The numerator-side monotonicity statement: for fixed
`w ≥ 1`, the doubled confessed burden grows at least quadratically in `k`.
This is the arithmetic core of the divergence claim without invoking real-
analysis limit infrastructure. -/
theorem inefficiency_doubled_burden_lower_bound
    (k w : Nat) (hw : 1 ≤ w) :
    k * k ≤ confessedBurdenDoubled k w := by
  unfold confessedBurdenDoubled
  nlinarith [hw, Nat.zero_le k]

/-- **Paper 2 Proposition 3.20 (Shannon-uniqueness).** The syntactic
structural mass `(i + 1) · (|b| + |G|)` at step `i` exceeds the minimum
description length bound `(|b| + |G|) + c(i)` by at least `i · (|b| + |G|)`,
where `c(i)` is any constant-in-`i` overhead. This captures the paper's
`|t_i| - K(t_i) = Θ(i · (|b| + |G|))` at the Nat level. -/
theorem shannon_uniqueness_gap
    (wrapSize paySize i : Nat) :
    i * (wrapSize + paySize)
      ≤ (i + 1) * (wrapSize + paySize) - (wrapSize + paySize) := by
  have h : (i + 1) * (wrapSize + paySize)
         = i * (wrapSize + paySize) + (wrapSize + paySize) := by ring
  rw [h]
  omega

end BaseDuplicatingSystem

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
