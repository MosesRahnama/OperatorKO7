import OperatorKO7.Meta.SchemaOffsetAndWrapper
import OperatorKO7.Meta.SchemaConfessionDominance
import Mathlib.Analysis.Asymptotics.Theta
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

open Asymptotics Filter
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

/-! ## Exact asymptotic rate of inefficiency divergence -/

/-- Quadratic comparison model for the direct-carrier inefficiency coefficient. -/
noncomputable def inefficiencyQuadraticComparison (k w : Nat) : ℝ :=
  ((k : ℝ) ^ 2 * w) / (2 * Real.log (k + 1))

/-- Linear comparison model for the per-residual inefficiency rate. -/
noncomputable def inefficiencyLinearComparison (k w : Nat) : ℝ :=
  ((k : ℝ) * w) / (2 * Real.log (k + 1))

/-- One-step increment of the inefficiency coefficient along the canonical trace. -/
noncomputable def inefficiencyStepIncrement (k w : Nat) : ℝ :=
  inefficiencyCoefficient (k + 1) w - inefficiencyCoefficient k w

/-- Linear comparison model for the per-step increment of the inefficiency coefficient. -/
noncomputable def inefficiencyStepComparison (k w : Nat) : ℝ :=
  ((k : ℝ) * w) / (2 * Real.log (k + 2))

theorem log_succ_pos (k : Nat) (hk : 1 ≤ k) : 0 < Real.log (k + 1) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < k + 1 by omega)

theorem log_two_succ_pos (k : Nat) : 0 < Real.log (k + 2) := by
  apply Real.log_pos
  norm_num

theorem log_succ_ge_one_of_two_le (k : Nat) (hk : 2 ≤ k) : 1 ≤ Real.log (k + 1) := by
  have hkpos : 0 < (k + 1 : ℝ) := by positivity
  have hexp_lt : Real.exp 1 < (k + 1 : ℝ) := by
    refine lt_trans Real.exp_one_lt_d9 ?_
    have hthree : (3 : ℝ) ≤ (k + 1 : ℝ) := by
      exact_mod_cast (show 3 ≤ k + 1 by omega)
    nlinarith
  exact le_of_lt ((Real.lt_log_iff_exp_lt hkpos).2 hexp_lt)

theorem log_two_succ_le_two_mul_log_succ (k : Nat) (hk : 1 ≤ k) :
    Real.log (k + 2) ≤ 2 * Real.log (k + 1) := by
  have hlog_pos : 0 < Real.log (k + 1) := log_succ_pos k hk
  have hcomp : (k + 2 : ℝ) ≤ 2 * (k + 1 : ℝ) := by nlinarith
  have hlog_le : Real.log (k + 2 : ℝ) ≤ Real.log (2 * (k + 1 : ℝ)) := by
    by_cases hEq : (k + 2 : ℝ) = 2 * (k + 1 : ℝ)
    · simpa [hEq]
    · exact le_of_lt
        (Real.strictMonoOn_log (by positivity) (by positivity) (lt_of_le_of_ne hcomp hEq))
  have hlog_mul :
      Real.log (2 * (k + 1 : ℝ)) = Real.log 2 + Real.log (k + 1) := by
    rw [Real.log_mul] <;> positivity
  calc
    Real.log (k + 2 : ℝ) ≤ Real.log (2 * (k + 1 : ℝ)) := hlog_le
    _ = Real.log 2 + Real.log (k + 1) := hlog_mul
    _ ≤ 2 * Real.log (k + 1) := by
      have hlog2_le : Real.log 2 ≤ Real.log (k + 1) := by
        have htwo_le : (2 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast hk
        by_cases hEq : (2 : ℝ) = (k + 1 : ℝ)
        · simpa [hEq]
        · exact le_of_lt
            (Real.strictMonoOn_log (by positivity) (by positivity) (lt_of_le_of_ne htwo_le hEq))
      linarith

theorem inefficiencyQuadraticComparison_nonneg (k w : Nat) :
    0 ≤ inefficiencyQuadraticComparison k w := by
  by_cases hk : k = 0
  · simp [inefficiencyQuadraticComparison, hk]
  · have hk1 : 1 ≤ k := by omega
    unfold inefficiencyQuadraticComparison
    positivity [log_succ_pos k hk1]

theorem inefficiencyLinearComparison_nonneg (k w : Nat) :
    0 ≤ inefficiencyLinearComparison k w := by
  by_cases hk : k = 0
  · simp [inefficiencyLinearComparison, hk]
  · have hk1 : 1 ≤ k := by omega
    unfold inefficiencyLinearComparison
    positivity [log_succ_pos k hk1]

theorem inefficiencyStepComparison_nonneg (k w : Nat) :
    0 ≤ inefficiencyStepComparison k w := by
  unfold inefficiencyStepComparison
  positivity [log_two_succ_pos k]

theorem inefficiencyCoefficient_nonneg (k w : Nat) :
    0 ≤ inefficiencyCoefficient k w := by
  by_cases hk : k = 0
  · simp [inefficiencyCoefficient, hk]
  · have hk1 : 1 ≤ k := by omega
    unfold inefficiencyCoefficient
    positivity [log_succ_pos k hk1]

theorem inefficiencyQuadraticComparison_le_inefficiencyCoefficient
    (k w : Nat) (hk : 1 ≤ k) :
    inefficiencyQuadraticComparison k w ≤ inefficiencyCoefficient k w := by
  have hlog_pos : 0 < Real.log (k + 1) := log_succ_pos k hk
  have hden_pos : 0 < 2 * Real.log (k + 1) := by positivity
  unfold inefficiencyQuadraticComparison inefficiencyCoefficient
  refine (div_le_div_iff₀ hden_pos).2 ?_
  have hw_nonneg : 0 ≤ (w : ℝ) := by positivity
  nlinarith

theorem inefficiencyCoefficient_le_six_mul_quadraticComparison
    (k w : Nat) (hk : 1 ≤ k) :
    inefficiencyCoefficient k w ≤ 6 * inefficiencyQuadraticComparison k w := by
  have hlog_pos : 0 < Real.log (k + 1) := log_succ_pos k hk
  have hden_pos : 0 < 2 * Real.log (k + 1) := by positivity
  unfold inefficiencyQuadraticComparison inefficiencyCoefficient
  refine (div_le_div_iff₀ hden_pos).2 ?_
  have hw_nonneg : 0 ≤ (w : ℝ) := by positivity
  nlinarith

/-- The inefficiency coefficient has exact `Θ(k^2 w / log(k+1))` growth. -/
theorem inefficiencyCoefficient_isTheta_quadraticLog
    (w : Nat) (hw : 1 ≤ w) :
    (fun k : Nat => inefficiencyCoefficient k w)
      =Θ[atTop] (fun k : Nat => ((k : ℝ) ^ 2 * w) / Real.log (k + 1)) := by
  let cmp : Nat → ℝ := fun k => inefficiencyQuadraticComparison k w
  have hcmp :
      (fun k : Nat => inefficiencyCoefficient k w) =Θ[atTop] cmp := by
    refine ⟨Asymptotics.IsBigO.of_bound 6 ?_, Asymptotics.IsBigO.of_bound 1 ?_⟩
    · filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
      have h := inefficiencyCoefficient_le_six_mul_quadraticComparison k w hk
      rw [Real.norm_of_nonneg (inefficiencyCoefficient_nonneg k w),
        Real.norm_of_nonneg (inefficiencyQuadraticComparison_nonneg k w)]
      simpa [cmp] using h
    · filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
      have h := inefficiencyQuadraticComparison_le_inefficiencyCoefficient k w hk
      rw [Real.norm_of_nonneg (inefficiencyQuadraticComparison_nonneg k w),
        Real.norm_of_nonneg (inefficiencyCoefficient_nonneg k w)]
      simpa [cmp] using h
  have hconst :
      cmp =Θ[atTop] (fun k : Nat => ((k : ℝ) ^ 2 * w) / Real.log (k + 1)) := by
    simpa [cmp, inefficiencyQuadraticComparison, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using
      (Asymptotics.isTheta_rfl (f := fun k : Nat => ((k : ℝ) ^ 2 * w) / Real.log (k + 1))
        (l := atTop)).const_mul_left (show (2 : ℝ) ≠ 0 by norm_num)
  exact hcmp.trans hconst

theorem inefficiencyQuadraticComparison_div_eq_linearComparison
    (k w : Nat) :
    inefficiencyQuadraticComparison k w / k = inefficiencyLinearComparison k w := by
  by_cases hk : k = 0
  · simp [inefficiencyQuadraticComparison, inefficiencyLinearComparison, hk]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    unfold inefficiencyQuadraticComparison inefficiencyLinearComparison
    field_simp [hkR]
    ring

/-- The per-residual inefficiency rate has exact `Θ(k w / log(k+1))` growth. -/
theorem inefficiencyCoefficient_perResidual_isTheta_linearLog
    (w : Nat) (hw : 1 ≤ w) :
    (fun k : Nat => inefficiencyCoefficient k w / k)
      =Θ[atTop] (fun k : Nat => ((k : ℝ) * w) / Real.log (k + 1)) := by
  have hdiv :
      (fun k : Nat => inefficiencyCoefficient k w / k)
        =Θ[atTop] (fun k : Nat => inefficiencyQuadraticComparison k w / k) :=
    (inefficiencyCoefficient_isTheta_quadraticLog w hw).div Asymptotics.isTheta_rfl
  have hEq :
      (fun k : Nat => inefficiencyQuadraticComparison k w / k)
        =ᶠ[atTop] (fun k : Nat => inefficiencyLinearComparison k w) :=
    Filter.Eventually.of_forall (fun k =>
      inefficiencyQuadraticComparison_div_eq_linearComparison k w)
  have hcmp :
      (fun k : Nat => inefficiencyLinearComparison k w)
        =Θ[atTop] (fun k : Nat => ((k : ℝ) * w) / Real.log (k + 1)) := by
    simpa [inefficiencyLinearComparison, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Asymptotics.isTheta_rfl (f := fun k : Nat => ((k : ℝ) * w) / Real.log (k + 1))
        (l := atTop)).const_mul_left (show (2 : ℝ) ≠ 0 by norm_num)
  exact (hdiv.trans_eventuallyEq hEq).trans hcmp

theorem log_gap_le_inv_succ (k : Nat) :
    Real.log (k + 2) - Real.log (k + 1) ≤ 1 / (k + 1 : ℝ) := by
  have hxpos : 0 < ((k + 2 : ℝ) / (k + 1 : ℝ)) := by positivity
  have h := Real.log_le_sub_one_of_pos hxpos
  rw [Real.log_div (by positivity : (k + 2 : ℝ) ≠ 0) (by positivity : (k + 1 : ℝ) ≠ 0)] at h
  have hrewrite : ((k + 2 : ℝ) / (k + 1 : ℝ)) - 1 = 1 / (k + 1 : ℝ) := by
    field_simp
    ring
  simpa [hrewrite] using h

theorem inefficiencyStepComparison_le_stepIncrement
    (k w : Nat) (hk : 2 ≤ k) :
    inefficiencyStepComparison k w ≤ inefficiencyStepIncrement k w := by
  let L1 : ℝ := Real.log (k + 1)
  let L2 : ℝ := Real.log (k + 2)
  have hL1_pos : 0 < L1 := by
    have : 1 ≤ k := by omega
    simpa [L1] using log_succ_pos k this
  have hL2_pos : 0 < L2 := by simpa [L2] using log_two_succ_pos k
  have hL1_ge_one : 1 ≤ L1 := by simpa [L1] using log_succ_ge_one_of_two_le k hk
  have hgap : L2 - L1 ≤ 1 / (k + 1 : ℝ) := by simpa [L1, L2] using log_gap_le_inv_succ k
  let B : ℝ := (((k + 1) * (k + 2) : Nat) : ℝ)
  have hscaled : B * (L2 - L1) ≤ (k + 2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ B)
    have hrewrite : B * (1 / (k + 1 : ℝ)) = (k + 2 : ℝ) := by
      field_simp [B]
      ring
    exact hmul.trans_eq hrewrite
  have hterm :
      B * (L2 - L1) / (L1 * L2) ≤ (k + 2 : ℝ) / L2 := by
    have hfirst : B * (L2 - L1) / (L1 * L2) ≤ (k + 2 : ℝ) / (L1 * L2) := by
      refine (div_le_div_of_nonneg_right ?_).2 hscaled
      positivity
    have hsecond : (k + 2 : ℝ) / (L1 * L2) ≤ (k + 2 : ℝ) / L2 := by
      have hden_nonzero : L1 * L2 ≠ 0 := by positivity
      have hL2_nonzero : L2 ≠ 0 := by positivity
      field_simp [hden_nonzero, hL2_nonzero]
      nlinarith [hL1_ge_one, le_of_lt hL2_pos]
    exact hfirst.trans hsecond
  have hmain :
      ((2 * k + 4 : Nat) : ℝ) / L2 - B * (L2 - L1) / (L1 * L2) ≥ (k + 2 : ℝ) / L2 := by
    linarith
  have hdecomp :
      inefficiencyStepIncrement k w
        = ((w : ℝ) / 2)
            * ((((2 * k + 4 : Nat) : ℝ) / L2)
                - B * (L2 - L1) / (L1 * L2)) := by
    unfold inefficiencyStepIncrement inefficiencyCoefficient
    have hL1_ne : L1 ≠ 0 := by positivity
    have hL2_ne : L2 ≠ 0 := by positivity
    field_simp [L1, L2, hL1_ne, hL2_ne]
    ring
  rw [hdecomp]
  calc
    ((w : ℝ) / 2)
        * ((((2 * k + 4 : Nat) : ℝ) / L2)
            - B * (L2 - L1) / (L1 * L2))
      ≥ ((w : ℝ) / 2) * ((k + 2 : ℝ) / L2) := by
        gcongr
    _ = ((k + 2 : ℝ) * w) / (2 * L2) := by
        field_simp [L2]
        ring
    _ ≥ ((k : ℝ) * w) / (2 * L2) := by
        nlinarith
    _ = inefficiencyStepComparison k w := by simp [inefficiencyStepComparison, L2]

theorem stepIncrement_le_six_mul_stepComparison
    (k w : Nat) (hk : 1 ≤ k) :
    inefficiencyStepIncrement k w ≤ 6 * inefficiencyStepComparison k w := by
  let L2 : ℝ := Real.log (k + 2)
  have hraw :
      (((k + 2) * (k + 3) * w : Nat) : ℝ) / (2 * L2)
        - (((k + 1) * (k + 2) * w : Nat) : ℝ) / (2 * Real.log (k + 1))
      ≤ ((k + 2 : ℝ) * w) / L2 := by
    have hsub :
        (((k + 1) * (k + 2) * w : Nat) : ℝ) / (2 * Real.log (k + 1))
          ≥ (((k + 1) * (k + 2) * w : Nat) : ℝ) / (2 * L2) := by
      have hlog_le : Real.log (k + 1) ≤ L2 := by
        have hcomp : (k + 1 : ℝ) ≤ (k + 2 : ℝ) := by positivity
        by_cases hEq : (k + 1 : ℝ) = (k + 2 : ℝ)
        · simpa [L2, hEq]
        · exact le_of_lt
            (Real.strictMonoOn_log (by positivity) (by positivity) (lt_of_le_of_ne hcomp hEq))
      have hnum_nonneg :
          0 ≤ (((k + 1) * (k + 2) * w : Nat) : ℝ) := by positivity
      exact (div_le_div_of_nonneg_left hnum_nonneg (by positivity) (by nlinarith [hlog_le]))
    linarith
  unfold inefficiencyStepIncrement inefficiencyStepComparison
  calc
    inefficiencyCoefficient (k + 1) w - inefficiencyCoefficient k w
      ≤ ((k + 2 : ℝ) * w) / L2 := by
        simpa [inefficiencyCoefficient, L2] using hraw
    _ ≤ 6 * (((k : ℝ) * w) / (2 * L2)) := by
        nlinarith

/-- The one-step inefficiency increment has exact `Θ(k w / log(k+2))` growth. -/
theorem inefficiencyStepIncrement_isTheta_linearLogShift
    (w : Nat) (hw : 1 ≤ w) :
    (fun k : Nat => inefficiencyStepIncrement k w)
      =Θ[atTop] (fun k : Nat => ((k : ℝ) * w) / Real.log (k + 2)) := by
  let cmp : Nat → ℝ := fun k => inefficiencyStepComparison k w
  refine ⟨Asymptotics.IsBigO.of_bound 6 ?_, Asymptotics.IsBigO.of_bound 1 ?_⟩
  · filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
    have h := stepIncrement_le_six_mul_stepComparison k w hk
    have hnonneg : 0 ≤ inefficiencyStepIncrement k w := by
      exact (inefficiencyStepComparison_le_stepIncrement k w (by omega)).trans
        (le_of_eq rfl)
    rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (inefficiencyStepComparison_nonneg k w)]
    simpa [cmp] using h
  · filter_upwards [eventually_atTop.2 ⟨2, fun k hk => hk⟩] with k hk
    have h := inefficiencyStepComparison_le_stepIncrement k w hk
    rw [Real.norm_of_nonneg (inefficiencyStepComparison_nonneg k w)]
    have hstep_nonneg : 0 ≤ inefficiencyStepIncrement k w := h.trans (le_of_eq rfl)
    rw [Real.norm_of_nonneg hstep_nonneg]
    simpa [cmp] using h

/-- The shift from `log(k+2)` to `log(k+1)` does not change the linear `Θ` class. -/
theorem linearLogShift_isTheta_linearLog (w : Nat) :
    (fun k : Nat => ((k : ℝ) * w) / Real.log (k + 2))
      =Θ[atTop] (fun k : Nat => ((k : ℝ) * w) / Real.log (k + 1)) := by
  refine ⟨Asymptotics.IsBigO.of_bound 2 ?_, Asymptotics.IsBigO.of_bound 1 ?_⟩
  · filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hshift : Real.log (k + 2) ≤ 2 * Real.log (k + 1) :=
      log_two_succ_le_two_mul_log_succ k hk
    exact (div_le_div_of_nonneg_left (by positivity) (log_two_succ_pos k) hshift)
  · filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hlog_le : Real.log (k + 1) ≤ Real.log (k + 2) := by
      have hcomp : (k + 1 : ℝ) ≤ (k + 2 : ℝ) := by positivity
      by_cases hEq : (k + 1 : ℝ) = (k + 2 : ℝ)
      · simpa [hEq]
      · exact le_of_lt
          (Real.strictMonoOn_log (by positivity) (by positivity) (lt_of_le_of_ne hcomp hEq))
    exact (div_le_div_of_nonneg_left (by positivity) (log_succ_pos k hk) hlog_le)

/-- **Paper 2 Proposition 3.19 (exact asymptotic rate).** The direct-carrier
inefficiency coefficient grows as `Θ(k^2 w / log(k+1))`, the per-residual
rate as `Θ(k w / log(k+1))`, and the one-step increment as `Θ(k w / log(k+1))`.
-/
theorem inefficiencyCoefficient_exact_rate
    (w : Nat) (hw : 1 ≤ w) :
    (fun k : Nat => inefficiencyCoefficient k w)
        =Θ[atTop] (fun k : Nat => ((k : ℝ) ^ 2 * w) / Real.log (k + 1))
      ∧ (fun k : Nat => inefficiencyCoefficient k w / k)
        =Θ[atTop] (fun k : Nat => ((k : ℝ) * w) / Real.log (k + 1))
      ∧ (fun k : Nat => inefficiencyStepIncrement k w)
        =Θ[atTop] (fun k : Nat => ((k : ℝ) * w) / Real.log (k + 1)) := by
  refine ⟨inefficiencyCoefficient_isTheta_quadraticLog w hw,
    inefficiencyCoefficient_perResidual_isTheta_linearLog w hw, ?_⟩
  exact (inefficiencyStepIncrement_isTheta_linearLogShift w hw).trans
    (linearLogShift_isTheta_linearLog w)

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
