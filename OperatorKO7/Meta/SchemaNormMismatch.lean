import OperatorKO7.Meta.SchemaOffsetAndWrapper
import OperatorKO7.Meta.SchemaConfessionDominance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

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

/-- Exact values of the three canonical norm readings on a nonempty diagonal
wrapper stack. -/
theorem diagonal_norm_values (p i : Nat) (hi : 1 ≤ i) :
    ell0NormOnDiagonal i = 1
      ∧ ellInfNormOnDiagonal p i = p
      ∧ ell1NormOnDiagonal p i = i * p := by
  exact ⟨ell0NormOnDiagonal_pos i hi, ellInfNormOnDiagonal_pos p i hi, rfl⟩

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

/-- A linear lower bound on the inefficiency coefficient once the trace length
is nontrivial. This is the key estimate behind the unboundedness theorem. -/
theorem inefficiencyCoefficient_lower_linear
    (k w : Nat) (hk : 1 ≤ k) (hw : 1 ≤ w) :
    ((k + 1 : ℝ) * w / 2) ≤ inefficiencyCoefficient k w := by
  have hlog_pos : 0 < Real.log (k + 1) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < k + 1 by omega)
  have hlog_le : Real.log (k + 1) ≤ k := by
    have hkpos : 0 < (k + 1 : ℝ) := by positivity
    simpa using Real.log_le_sub_one_of_pos hkpos
  unfold inefficiencyCoefficient
  have hden_pos : 0 < 2 * Real.log (k + 1) := by nlinarith
  apply (le_div_iff₀ hden_pos).2
  calc
    ((k + 1 : ℝ) * w / 2) * (2 * Real.log (k + 1))
        = ((k + 1 : ℝ) * w) * Real.log (k + 1) := by ring
    _ ≤ ((k + 1 : ℝ) * w) * k := by
      have hmul_nonneg : 0 ≤ ((k + 1 : ℝ) * w) := by positivity
      exact mul_le_mul_of_nonneg_left hlog_le hmul_nonneg
    _ ≤ ((k + 1 : ℝ) * (k + 2) * w) := by
      nlinarith

/-- **Paper 2 Proposition 3.19 (schema-mechanized form).** For every target
bound `N`, the direct-carrier inefficiency coefficient eventually exceeds `N`
along the odd subsequence `k = 2N + 1`. This is a concrete unboundedness
theorem for `η(k,w)`. -/
theorem inefficiencyCoefficient_unbounded
    (w : Nat) (hw : 1 ≤ w) (N : Nat) :
    (N : ℝ) ≤ inefficiencyCoefficient (2 * N + 1) w := by
  have hk : 1 ≤ 2 * N + 1 := by omega
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hhalf :
      (N : ℝ) ≤ (((((2 * N + 1) + 1 : Nat) : ℝ)) / 2) := by
    have hrewrite : (((((2 * N + 1) + 1 : Nat) : ℝ)) / 2) = (N : ℝ) + 1 := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [hrewrite]
    nlinarith
  have hscale :
      (((((2 * N + 1) + 1 : Nat) : ℝ)) / 2)
        ≤ ((((2 * N + 1) + 1 : Nat) : ℝ) * w / 2) := by
    nlinarith
  calc
    (N : ℝ) ≤ (((((2 * N + 1) + 1 : Nat) : ℝ)) / 2) := hhalf
    _ ≤ ((((2 * N + 1) + 1 : Nat) : ℝ) * w / 2) := hscale
    _ ≤ inefficiencyCoefficient (2 * N + 1) w := by
      simpa using inefficiencyCoefficient_lower_linear (2 * N + 1) w hk hw

/-- Unboundedness packaged in existential form. -/
theorem inefficiencyCoefficient_unbounded_atTop
    (w : Nat) (hw : 1 ≤ w) :
    ∀ N : Nat, ∃ k : Nat, (N : ℝ) ≤ inefficiencyCoefficient k w := by
  intro N
  exact ⟨2 * N + 1, inefficiencyCoefficient_unbounded w hw N⟩

/-- A coarse repeated-carrier envelope for the duplicated payload component of
the canonical trace: one wrapper-cell budget per payload-bearing position. -/
def repeatedCarrierMass (wrapSize paySize i : Nat) : Nat :=
  (i + 1) * (wrapSize + paySize)

/-- An explicit description-length model for the canonical trace stage:
one seed description, one wrapper-symbol description, a binary-size code for
the step index, and constant glue overhead. -/
def explicitDescriptionLength
    (wrapSize paySize glue i : Nat) : Nat :=
  wrapSize + paySize + Nat.size (i + 1) + glue

@[simp] theorem repeatedCarrierMass_def (wrapSize paySize i : Nat) :
    repeatedCarrierMass wrapSize paySize i = (i + 1) * (wrapSize + paySize) := rfl

@[simp] theorem explicitDescriptionLength_def
    (wrapSize paySize glue i : Nat) :
    explicitDescriptionLength wrapSize paySize glue i
      = wrapSize + paySize + Nat.size (i + 1) + glue := rfl

/-- The explicit description length grows by only logarithmic index overhead
on top of one seed description and one wrapper-symbol description. -/
theorem explicitDescriptionLength_upper_bound
    (wrapSize paySize glue i : Nat) :
    explicitDescriptionLength wrapSize paySize glue i
      ≤ wrapSize + paySize + (i + 1) + glue := by
  unfold explicitDescriptionLength
  have hsize : Nat.size (i + 1) ≤ i + 1 := by
    apply Nat.not_lt.mp
    intro hlt
    have hpow : 2 ^ (i + 1) ≤ i + 1 := (Nat.lt_size).1 hlt
    exact ((i + 1).lt_two_pow_self).not_ge hpow
  omega

/-- The repeated carrier mass and explicit description length differ by an
exact linear term plus the logarithmic index code. -/
theorem repeatedCarrierMass_description_balance
    (wrapSize paySize glue i : Nat) :
    i * (wrapSize + paySize) + explicitDescriptionLength wrapSize paySize glue i
      = repeatedCarrierMass wrapSize paySize i + Nat.size (i + 1) + glue := by
  unfold repeatedCarrierMass explicitDescriptionLength
  ring

/-- **Paper 2 Proposition 3.20 (schema-mechanized form).** After subtracting
the explicit description length, the repeated-carrier envelope retains an
exact linear gap `i · (|b| + |G|)` up to the logarithmic index code
`Nat.size (i + 1)` and fixed glue overhead. -/
theorem explicitDescription_linear_gap
    (wrapSize paySize glue i : Nat) :
    i * (wrapSize + paySize)
      = repeatedCarrierMass wrapSize paySize i + Nat.size (i + 1) + glue
          - explicitDescriptionLength wrapSize paySize glue i := by
  have h :=
    repeatedCarrierMass_description_balance wrapSize paySize glue i
  omega

end BaseDuplicatingSystem

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
