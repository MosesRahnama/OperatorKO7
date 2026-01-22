import OperatorKO7.Kernel
import Init.WF
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic

/-!
Termination infrastructure (ordinal measures and supporting lemmas).

Purpose:
- Defines an ordinal-valued measure `MetaSN.mu` on KO7 traces.
- Defines auxiliary counters/ranks (e.g. `MetaSN.kappa`) used in combined lex measures.
- Proves a library of ordinal arithmetic lemmas used by the KO7 termination developments.

Scope:
- This file is *measure infrastructure*. It does not define `SafeStep`, and it does not claim
  termination of the full kernel `Step` relation. The certified termination proofs for the safe
  fragment live in `OperatorKO7/Meta/Termination_KO7.lean`.

Key exports (used downstream):
- `MetaSN.mu` (ordinal payload)
- `MetaSN.kappa` and `MetaSN.μκ` (combined measures)
- lemma families `mu_lt_*` that provide strict decreases needed by per-rule drop proofs

Paper map:
- Supports the paper's SN section and the appendix discussion of ordinal hazards (right-addition is
  not strictly monotone; absorption requires an explicit `omega0 ≤ _` hypothesis).
-/
set_option linter.unnecessarySimpa false

/- Local compatibility shims (to avoid depending on Legacy Patch2025_08_10). -/
namespace OperatorKO7.Patch2025_08_10
open Ordinal

/-- strict monotonicity of `ω ^ _` (compat wrapper). -/
@[simp] theorem opow_lt_opow_right {a b : Ordinal} (h : a < b) :
  omega0 ^ a < omega0 ^ b :=
  ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)

/-- `0 < 1` for ordinals (compat helper). -/
@[simp] lemma zero_lt_one_ordinal : (0 : Ordinal) < 1 := by
  simpa using (nat_lt_omega0 1)

end OperatorKO7.Patch2025_08_10

/-
Ordinal hazards policy (explicit hypotheses):
- Use `Ordinal.opow_le_opow_right` for ≤-monotonicity in the exponent.
- For strict < at base ω, use the local strict-mono bridge (normality of opow at ω).
- Avoid transporting strictness via right-add unless justified; ordinal addition is not strictly right-mono.
- Only absorb `(n : Ordinal) + p = p` after showing `omega0 ≤ p`.
These constraints are enforced in new lemmas; legacy statements remain unchanged.
-/

universe u

open Ordinal
open OperatorKO7
open Trace
namespace MetaSN


/-- Ordinal-valued termination payload used in the KO7 developments. -/
noncomputable def mu : Trace → Ordinal.{0}
| .void        => 0
| .delta t     => (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1
| .integrate t => (omega0 ^ (4 : Ordinal)) * (mu t + 1) + 1
| .merge a b   =>
    (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) +
    (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1
| .recΔ b s n  =>
    omega0 ^ (MetaSN.mu n + MetaSN.mu s + (6 : Ordinal))
  + omega0 * (MetaSN.mu b + 1) + 1
| .eqW a b     =>
    omega0 ^ (MetaSN.mu a + MetaSN.mu b + (9 : Ordinal)) + 1
| .app a b     =>
    (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) +
    (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1

/-- Secondary counter: 0 everywhere except it counts nesting depth of `recΔ` (used for lex drops). -/
def kappa : Trace → ℕ
| Trace.recΔ _ _ n => (kappa n).succ
| Trace.void => 0
| Trace.delta _ => 0
| Trace.integrate _ => 0
| Trace.merge _ _ => 0
| Trace.app _ _ => 0
| Trace.eqW _ _ => 0

/-- Combined measure pair (kappa primary, mu secondary). -/
noncomputable def μκ (t : Trace) : ℕ × Ordinal := (kappa t, mu t)

/-- Lexicographic order on `(ℕ × Ordinal)` used for combined (kappa, mu) measures. -/
def LexNatOrd : (ℕ × Ordinal) → (ℕ × Ordinal) → Prop :=
  Prod.Lex (· < ·) (· < ·)


/-- `kappa` is zero on any trace that is not a `recΔ _ _ _`. -/
@[simp] lemma kappa_non_rec (t : Trace)
  : (¬ ∃ b s n, t = Trace.recΔ b s n) → kappa t = 0 := by
  cases t with
  | recΔ b s n =>
      intro h; exact (False.elim (h ⟨b, s, n, rfl⟩))
  | void => intro _; simp [kappa]
  | delta _ => intro _; simp [kappa]
  | integrate _ => intro _; simp [kappa]
  | merge _ _ => intro _; simp [kappa]
  | eqW _ _ => intro _; simp [kappa]
  | app _ _ => intro _; simp [kappa]

/-- Basic strictness: `mu t` is strictly less than the merge payload `mu (merge t void)`. -/
theorem mu_lt_merge_void_right (t : Trace) :
  -- Hypotheses used: opow_pos, opow_le_opow_right for ≤-mono, add-one bridges; no right-add strictness.
  mu t < MetaSN.mu (.merge t .void) := by
  -- μ(merge t void) = ω³*(μ t +1) + ω² + 1 dominates μ t
  have h1 : mu t < mu t + 1 :=
    (Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl
  have pos3 : 0 < omega0 ^ (3 : Ordinal) :=
    by simpa using (Ordinal.opow_pos (a := omega0) (b := (3 : Ordinal)) omega0_pos)
  have hmono : mu t + 1 ≤ omega0 ^ (3 : Ordinal) * (mu t + 1) := by
    simpa using (Ordinal.le_mul_right (a := mu t + 1) (b := omega0 ^ (3 : Ordinal)) pos3)
  have h2 : mu t < omega0 ^ (3 : Ordinal) * (mu t + 1) := lt_of_lt_of_le h1 hmono
  have tail : (0 : Ordinal) ≤ omega0 ^ (2 : Ordinal) * (0 + 1) + 1 := zero_le _
  have h3 : omega0 ^ (3 : Ordinal) * (mu t + 1) ≤
      omega0 ^ (3 : Ordinal) * (mu t + 1) + (omega0 ^ (2 : Ordinal) * (0 + 1) + 1) :=
    le_add_of_nonneg_right tail
  have h4 : mu t < omega0 ^ (3 : Ordinal) * (mu t + 1) + (omega0 ^ (2 : Ordinal) * (0 + 1) + 1) :=
    lt_of_lt_of_le h2 h3
  simpa [mu, add_assoc, add_comm, add_left_comm]
    using h4

/-- Convenience lemma: `0 < y + 1` for ordinals. -/
theorem zero_lt_add_one (y : Ordinal) : (0 : Ordinal) < y + 1 :=
  (Order.lt_add_one_iff (x := (0 : Ordinal)) (y := y)).2 bot_le

/-- Basic strictness: `mu void` is strictly less than `mu (integrate (delta t))`. -/
theorem mu_void_lt_integrate_delta (t : Trace) :
  -- Hypotheses used: principal_add_omega0_opow (strict-mono at ω), opow_pos, add-one bridge.
  MetaSN.mu .void < MetaSN.mu (.integrate (.delta t)) := by
  simp [MetaSN.mu]

/-- Basic strictness: `mu void` is strictly less than `mu (eqW a a)` for any `a`. -/
theorem mu_void_lt_eq_refl (a : Trace) :
  -- Hypotheses used: opow_le_opow_right and strict-mono bridge for the big exponent, final add-one bridge.
  MetaSN.mu .void < MetaSN.mu (.eqW a a) := by
  simp [MetaSN.mu]

section Debug


/-- Cancellation rule: `merge t t → t` strictly drops `μ`. -/
theorem mu_lt_merge_cancel (t : Trace) :
  -- Hypotheses used: opow_pos, le_mul_right, le_add_right, add-one bridge; avoids unjustified right-add strictness.
  MetaSN.mu t < MetaSN.mu (.merge t t) := by
  -- Legacy-proof (compiles in Termination_C):
  have h0 : MetaSN.mu t < MetaSN.mu t + 1 :=
    (Order.lt_add_one_iff (x := MetaSN.mu t) (y := MetaSN.mu t)).2 le_rfl
  have pos3 : 0 < omega0 ^ (3 : Ordinal) :=
    by simpa using (Ordinal.opow_pos (a := omega0) (b := (3 : Ordinal)) omega0_pos)
  have hmono : MetaSN.mu t + 1 ≤ omega0 ^ (3 : Ordinal) * (MetaSN.mu t + 1) := by
    simpa using (Ordinal.le_mul_right (a := MetaSN.mu t + 1)
      (b := omega0 ^ (3 : Ordinal)) pos3)
  have h1 : MetaSN.mu t < omega0 ^ (3 : Ordinal) * (MetaSN.mu t + 1) := lt_of_lt_of_le h0 hmono
  -- add the second ω²-term (same `t`) and tail +1
  have pad :
      omega0 ^ (3 : Ordinal) * (MetaSN.mu t + 1) ≤
      (omega0 ^ (3 : Ordinal)) * (MetaSN.mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1) :=
    Ordinal.le_add_right _ _
  have pad1 :
      omega0 ^ (3 : Ordinal) * (MetaSN.mu t + 1) + 1 ≤
      ((omega0 ^ (3 : Ordinal)) * (MetaSN.mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1)) + 1 :=
    add_le_add_right pad 1
  have h2 :
      MetaSN.mu t <
      ((omega0 ^ (3 : Ordinal)) * (MetaSN.mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1)) + 1 :=
    lt_of_lt_of_le
      (lt_of_lt_of_le h1 (le_add_of_nonneg_right (zero_le _))) pad1
  simpa [MetaSN.mu, add_assoc] using h2

/-! Hypothesis-explicit wrappers (to make ordinal hypotheses explicit in signatures).
    These consume the hypotheses and delegate to the established lemmas above. -/

theorem mu_lt_merge_void_right_with (t : Trace)
  (_hpos3 : (0 : Ordinal.{0}) < (omega0 : Ordinal.{0}) ^ (3 : Ordinal)) :
  mu t < MetaSN.mu (.merge t .void) := by
  simpa [mu_lt_merge_void_right] using mu_lt_merge_void_right t

theorem mu_void_lt_integrate_delta_with (t : Trace)
  (_hpos4 : (0 : Ordinal.{0}) < (omega0 : Ordinal.{0}) ^ (4 : Ordinal)) :
  MetaSN.mu .void < MetaSN.mu (.integrate (.delta t)) := by
  simpa [mu_void_lt_integrate_delta] using mu_void_lt_integrate_delta t

theorem mu_void_lt_eq_refl_with (a : Trace)
  (_hpos : (0 : Ordinal.{0}) < (omega0 : Ordinal.{0}) ^ (MetaSN.mu a + MetaSN.mu a + (9 : Ordinal))) :
  MetaSN.mu .void < MetaSN.mu (.eqW a a) := by
  simpa [mu_void_lt_eq_refl] using mu_void_lt_eq_refl a

theorem mu_lt_merge_cancel_with (t : Trace)
  (_hpos3 : (0 : Ordinal.{0}) < (omega0 : Ordinal.{0}) ^ (3 : Ordinal)) :
  MetaSN.mu t < MetaSN.mu (.merge t t) := by
  simpa using mu_lt_merge_cancel t


end Debug


-- (Removed earlier succ_succ_eq_add_two lemma to avoid recursive simp loops.)
lemma succ_succ_eq_add_two (x : Ordinal) :
  Order.succ (Order.succ x) = x + 2 := by
  have hx : Order.succ x = x + 1 := by
    simpa using (Ordinal.add_one_eq_succ (a := x)).symm
  have hx2 : Order.succ (Order.succ x) = (x + 1) + 1 := by
    -- rewrite outer succ
    rw [hx]
    simpa using (Ordinal.add_one_eq_succ (a := x + 1)).symm
  -- assemble via calc to avoid deep simp recursion
  calc
    Order.succ (Order.succ x) = (x + 1) + 1 := hx2
    _ = x + (1 + 1) := by rw [add_assoc]
    _ = x + 2 := by simp

@[simp] lemma succ_succ_pow2 :
  Order.succ (Order.succ (omega0 ^ (2 : Ordinal))) = omega0 ^ (2 : Ordinal) + 2 := by
  simpa using succ_succ_eq_add_two (omega0 ^ (2 : Ordinal))



-- alias le_of_not_gt := le_of_not_lt
-- what is this exactly?
attribute [simp] Ordinal.IsNormal.strictMono


/-- Special case: both args void. Clean proof staying in +2 form. -/
theorem mu_lt_eq_diff_both_void :
  MetaSN.mu (integrate (merge .void .void)) < MetaSN.mu (eqW .void .void) := by
  -- μ(merge void void)
  have hμm : MetaSN.mu (merge .void .void) =
      omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 1 := by
    simp [MetaSN.mu, add_assoc]
  -- rewrite μ(integrate ...)
  have hL : MetaSN.mu (integrate (merge .void .void)) =
      omega0 ^ (4 : Ordinal) * (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) + 1 := by
    simpa [MetaSN.mu, hμm, add_assoc]
  -- payload pieces < ω^5 via additive principal
  have hα : omega0 ^ (3 : Ordinal) < omega0 ^ (5 : Ordinal) := by
    have : (3 : Ordinal) < 5 := by norm_num
    simpa using OperatorKO7.Patch2025_08_10.opow_lt_opow_right this
  have hβ : omega0 ^ (2 : Ordinal) < omega0 ^ (5 : Ordinal) := by
    have : (2 : Ordinal) < 5 := by norm_num
    simpa using OperatorKO7.Patch2025_08_10.opow_lt_opow_right this
  have hγ : (2 : Ordinal) < omega0 ^ (5 : Ordinal) := by
    have h2ω : (2 : Ordinal) < omega0 := nat_lt_omega0 2
    have ω_le : omega0 ≤ omega0 ^ (5 : Ordinal) := by
      have : (1 : Ordinal) ≤ (5 : Ordinal) := by norm_num
      have hpow := Ordinal.opow_le_opow_right omega0_pos this
      simpa using (le_trans (by simpa using (Ordinal.opow_one omega0).symm.le) hpow)
    exact lt_of_lt_of_le h2ω ω_le
  have hprin := Ordinal.principal_add_omega0_opow (5 : Ordinal)
  have hsum12 : omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) < omega0 ^ (5 : Ordinal) :=
    hprin hα hβ
  have h_payload : omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2 < omega0 ^ (5 : Ordinal) :=
    hprin hsum12 hγ
  -- multiply by ω^4 and collapse exponent
  have pos4 : (0 : Ordinal) < omega0 ^ (4 : Ordinal) :=
    Ordinal.opow_pos (a := omega0) (b := (4 : Ordinal)) omega0_pos
  have hstep : omega0 ^ (4 : Ordinal) *
      (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) <
      omega0 ^ (4 : Ordinal) * omega0 ^ (5 : Ordinal) :=
    Ordinal.mul_lt_mul_of_pos_left h_payload pos4
  have hcollapse : omega0 ^ (4 : Ordinal) * omega0 ^ (5 : Ordinal) =
      omega0 ^ (4 + 5 : Ordinal) := by
    simpa using (Ordinal.opow_add omega0 (4:Ordinal) (5:Ordinal)).symm
  have h45 : (4 : Ordinal) + (5 : Ordinal) = (9 : Ordinal) := by norm_num
  have h_prod :
      omega0 ^ (4 : Ordinal) *
        (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) <
      omega0 ^ (9 : Ordinal) := by
    have htmp2 : omega0 ^ (4 : Ordinal) *
        (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) < omega0 ^ (4 + 5 : Ordinal) :=
      lt_of_lt_of_eq hstep hcollapse
    have hrewrite : omega0 ^ (4 + 5 : Ordinal) = omega0 ^ (9 : Ordinal) := by
      simpa using congrArg (fun e => omega0 ^ e) h45
    exact lt_of_lt_of_eq htmp2 hrewrite
  -- add-one bridge
  have hR : MetaSN.mu (eqW .void .void) = omega0 ^ (9 : Ordinal) + 1 := by
    simp [MetaSN.mu]
  have hA1 : omega0 ^ (4 : Ordinal) *
      (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) + 1 ≤
      omega0 ^ (9 : Ordinal) := Order.add_one_le_of_lt h_prod
  have hfin : omega0 ^ (4 : Ordinal) *
      (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) + 1 <
      omega0 ^ (9 : Ordinal) + 1 :=
    (Order.lt_add_one_iff (x := _ + 1) (y := omega0 ^ (9 : Ordinal))).2 hA1
  simpa [hL, hR] using hfin

@[simp] lemma succ_succ_mul_pow2_succ (x : Ordinal) :
  Order.succ (Order.succ (omega0 ^ (2 : Ordinal) * Order.succ x)) =
    omega0 ^ (2 : Ordinal) * Order.succ x + 2 := by
  simpa using succ_succ_eq_add_two (omega0 ^ (2 : Ordinal) * Order.succ x)

-- (section continues with μ auxiliary lemmas)
lemma mu_recDelta_plus_3_lt (b s n : Trace)
  (h_bound : omega0 ^ (MetaSN.mu n + MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 + 3 <
             (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) + 1 + MetaSN.mu s + 6) :
  MetaSN.mu (recΔ b s n) + 3 < MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
  -- Expand mu definitions on both sides; structure then matches h_bound directly
  simp only [mu]
  exact h_bound


private lemma le_omega_pow (x : Ordinal) : x ≤ omega0 ^ x :=
  Ordinal.right_le_opow (a := omega0) (b := x) one_lt_omega0

theorem add_one_le_of_lt {x y : Ordinal} (h : x < y) : x + 1 ≤ y := by
  simpa [Ordinal.add_one_eq_succ] using (Order.add_one_le_of_lt h)

private lemma nat_coeff_le_omega_pow (n : ℕ) :
  (n : Ordinal) + 1 ≤ (omega0 ^ (n : Ordinal)) := by
  classical
  cases' n with n
  · -- `n = 0`: `1 ≤ ω^0 = 1`
    simp
  · -- `n = n.succ`

    have hfin : (n.succ : Ordinal) < omega0 := by

      simpa using (Ordinal.nat_lt_omega0 (n.succ))
    have hleft : (n.succ : Ordinal) + 1 ≤ omega0 :=
      Order.add_one_le_of_lt hfin

    have hpos : (0 : Ordinal) < (n.succ : Ordinal) := by
      simpa using (Nat.cast_pos.mpr (Nat.succ_pos n))
    have hmono : (omega0 : Ordinal) ≤ (omega0 ^ (n.succ : Ordinal)) := by
      -- `left_le_opow` has type: `0 < b → a ≤ a ^ b`
      simpa using (Ordinal.left_le_opow (a := omega0) (b := (n.succ : Ordinal)) hpos)

    exact hleft.trans hmono

private lemma coeff_fin_le_omega_pow (n : ℕ) :
  (n : Ordinal) + 1 ≤ omega0 ^ (n : Ordinal) := nat_coeff_le_omega_pow n

@[simp] theorem natCast_le {m n : ℕ} :
  ((m : Ordinal) ≤ (n : Ordinal)) ↔ m ≤ n := Nat.cast_le

@[simp] theorem natCast_lt {m n : ℕ} :
  ((m : Ordinal) < (n : Ordinal)) ↔ m < n := Nat.cast_lt

theorem eq_nat_or_omega0_le (p : Ordinal) :
  (∃ n : ℕ, p = n) ∨ omega0 ≤ p := by
  classical
  cases lt_or_ge p omega0 with
  | inl h  =>
      rcases (lt_omega0).1 h with ⟨n, rfl⟩
      exact Or.inl ⟨n, rfl⟩
  | inr h  => exact Or.inr h

theorem one_left_add_absorb {p : Ordinal} (h : omega0 ≤ p) :
  (1 : Ordinal) + p = p := by
  simpa using (one_add_of_omega0_le h)

theorem nat_left_add_absorb {n : ℕ} {p : Ordinal} (h : omega0 ≤ p) :
  (n : Ordinal) + p = p := by
  simpa using (natCast_add_of_omega0_le h n)

@[simp] theorem add_natCast_left (m n : ℕ) :
  (m : Ordinal) + (n : Ordinal) = ((m + n : ℕ) : Ordinal) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Nat.cast_succ]

theorem mul_le_mul {a b c d : Ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) :
    a * b ≤ c * d := by
  have h₁' : a * b ≤ c * b := by
    simpa using (mul_le_mul_right' h₁ b)        -- mono in left factor
  have h₂' : c * b ≤ c * d := by
    simpa using (mul_le_mul_left' h₂ c)         -- mono in right factor
  exact le_trans h₁' h₂'

theorem add4_plus5_le_plus9 (p : Ordinal) :
  (4 : Ordinal) + (p + 5) ≤ p + 9 := by
  classical
  rcases lt_or_ge p omega0 with hfin | hinf
  · -- finite case: `p = n : ℕ`
    rcases (lt_omega0).1 hfin with ⟨n, rfl⟩
    -- compute on ℕ first
    have hEqNat : (4 + (n + 5) : ℕ) = (n + 9 : ℕ) := by
      -- both sides reduce to `n + 9`
      simp [Nat.add_left_comm]
    have hEq :
        (4 : Ordinal) + ((n : Ordinal) + 5) = (n : Ordinal) + 9 := by
      calc
        (4 : Ordinal) + ((n : Ordinal) + 5)
            = (4 : Ordinal) + (((n + 5 : ℕ) : Ordinal)) := by
                simp
        _   = ((4 + (n + 5) : ℕ) : Ordinal) := by
                simp
        _   = ((n + 9 : ℕ) : Ordinal) := by
                simpa using (congrArg (fun k : ℕ => (k : Ordinal)) hEqNat)
        _   = (n : Ordinal) + 9 := by
                simp
    exact le_of_eq hEq
  · -- infinite-or-larger case: the finite prefix on the left collapses
    -- `5 ≤ 9` as ordinals
    have h59 : (5 : Ordinal) ≤ (9 : Ordinal) := by
      simpa using (natCast_le.mpr (by decide : (5 : ℕ) ≤ 9))
    -- monotonicity in the right argument
    have hR : p + 5 ≤ p + 9 := by
      simpa using add_le_add_left h59 p
    -- collapse `4 + p` since `ω ≤ p`
    have hcollapse : (4 : Ordinal) + (p + 5) = p + 5 := by
      calc
        (4 : Ordinal) + (p + 5)
            = ((4 : Ordinal) + p) + 5 := by
                simp [add_assoc]
        _   = p + 5 := by
                have h4 : (4 : Ordinal) + p = p := nat_left_add_absorb (n := 4) (p := p) hinf
                rw [h4]
    simpa [hcollapse] using hR

theorem add_nat_succ_le_plus_succ (k : ℕ) (p : Ordinal) :
  (k : Ordinal) + Order.succ p ≤ p + (k + 1) := by
  rcases lt_or_ge p omega0 with hfin | hinf
  · rcases (lt_omega0).1 hfin with ⟨n, rfl⟩
    have hN : (k + (n + 1) : ℕ) = n + (k + 1) := by
      simp [Nat.add_left_comm]
    have h :
        (k : Ordinal) + ((n : Ordinal) + 1) = (n : Ordinal) + (k + 1) := by
      calc
        (k : Ordinal) + ((n : Ordinal) + 1)
            = ((k + (n + 1) : ℕ) : Ordinal) := by simp
        _   = ((n + (k + 1) : ℕ) : Ordinal) := by
              simpa using (congrArg (fun t : ℕ => (t : Ordinal)) hN)
        _   = (n : Ordinal) + (k + 1) := by simp
    have : (k : Ordinal) + Order.succ (n : Ordinal) = (n : Ordinal) + (k + 1) := by
      simpa [Ordinal.add_one_eq_succ] using h
    exact le_of_eq this
  ·
    have hk : (k : Ordinal) + p = p := nat_left_add_absorb (n := k) hinf
    have hcollapse :
        (k : Ordinal) + Order.succ p = Order.succ p := by
      simpa [Ordinal.add_succ] using congrArg Order.succ hk
    have hkNat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have h1k : (1 : Ordinal) ≤ (k + 1 : Ordinal) := by
      simpa using (natCast_le.mpr hkNat)
    have hstep0 : p + 1 ≤ p + (k + 1) := add_le_add_left h1k p
    have hstep : Order.succ p ≤ p + (k + 1) := by
      simpa [Ordinal.add_one_eq_succ] using hstep0
    exact (le_of_eq hcollapse).trans hstep

theorem add_nat_plus1_le_plus_succ (k : ℕ) (p : Ordinal) :
  (k : Ordinal) + (p + 1) ≤ p + (k + 1) := by
  simpa [Ordinal.add_one_eq_succ] using add_nat_succ_le_plus_succ k p

theorem add3_succ_le_plus4 (p : Ordinal) :
  (3 : Ordinal) + Order.succ p ≤ p + 4 := by
  simpa using add_nat_succ_le_plus_succ 3 p

theorem add2_succ_le_plus3 (p : Ordinal) :
  (2 : Ordinal) + Order.succ p ≤ p + 3 := by
  simpa using add_nat_succ_le_plus_succ 2 p

theorem add3_plus1_le_plus4 (p : Ordinal) :
  (3 : Ordinal) + (p + 1) ≤ p + 4 := by
  simpa [Ordinal.add_one_eq_succ] using add3_succ_le_plus4 p

theorem add2_plus1_le_plus3 (p : Ordinal) :
  (2 : Ordinal) + (p + 1) ≤ p + 3 := by
  simpa [Ordinal.add_one_eq_succ] using add2_succ_le_plus3 p

theorem termA_le (x : Ordinal) :
  (omega0 ^ (3 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 4) := by
  have hx : x + 1 ≤ omega0 ^ (x + 1) := le_omega_pow (x := x + 1)
  have hmul :
      (omega0 ^ (3 : Ordinal)) * (x + 1)
        ≤ (omega0 ^ (3 : Ordinal)) * (omega0 ^ (x + 1)) := by
    simpa using (mul_le_mul_left' hx (omega0 ^ (3 : Ordinal)))
  have hpow' :
      (omega0 ^ (3 : Ordinal)) * (omega0 ^ x * omega0)
        = omega0 ^ (3 + (x + 1)) := by
    simpa [Ordinal.opow_succ, add_comm, add_left_comm, add_assoc] using
      (Ordinal.opow_add omega0 (3 : Ordinal) (x + 1)).symm
  have hmul' :
      (omega0 ^ (3 : Ordinal)) * Order.succ x
        ≤ omega0 ^ (3 + (x + 1)) := by
    simpa [hpow', Ordinal.add_one_eq_succ] using hmul
  have hexp : 3 + (x + 1) ≤ x + 4 := by
    simpa [add_assoc, add_comm, add_left_comm] using add3_plus1_le_plus4 x
  have hmono :
      omega0 ^ (3 + (x + 1)) ≤ omega0 ^ (x + 4) := Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos hexp
  exact hmul'.trans hmono

theorem termB_le (x : Ordinal) :
  (omega0 ^ (2 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 3) := by
  have hx : x + 1 ≤ omega0 ^ (x + 1) := le_omega_pow (x := x + 1)
  have hmul :
      (omega0 ^ (2 : Ordinal)) * (x + 1)
        ≤ (omega0 ^ (2 : Ordinal)) * (omega0 ^ (x + 1)) := by
    simpa using (mul_le_mul_left' hx (omega0 ^ (2 : Ordinal)))
  have hpow' :
      (omega0 ^ (2 : Ordinal)) * (omega0 ^ x * omega0)
        = omega0 ^ (2 + (x + 1)) := by
    simpa [Ordinal.opow_succ, add_comm, add_left_comm, add_assoc] using
      (Ordinal.opow_add omega0 (2 : Ordinal) (x + 1)).symm
  have hmul' :
      (omega0 ^ (2 : Ordinal)) * Order.succ x
        ≤ omega0 ^ (2 + (x + 1)) := by
    simpa [hpow', Ordinal.add_one_eq_succ] using hmul
  have hexp : 2 + (x + 1) ≤ x + 3 := by
    simpa [add_assoc, add_comm, add_left_comm] using add2_plus1_le_plus3 x
  have hmono :
      omega0 ^ (2 + (x + 1)) ≤ omega0 ^ (x + 3) := Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos hexp
  exact hmul'.trans hmono


theorem payload_bound_merge (x : Ordinal) :
  (omega0 ^ (3 : Ordinal)) * (x + 1) + ((omega0 ^ (2 : Ordinal)) * (x + 1) + 1)
    ≤ omega0 ^ (x + 5) := by
  have hA : (omega0 ^ (3 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 4) := termA_le x
  have hB0 : (omega0 ^ (2 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 3) := termB_le x
  have h34 : (x + 3 : Ordinal) ≤ x + 4 := by
    have : ((3 : ℕ) : Ordinal) ≤ (4 : ℕ) := by
      simpa using (natCast_le.mpr (by decide : (3 : ℕ) ≤ 4))
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left this x
  have hB : (omega0 ^ (2 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 4) :=
    le_trans hB0 (Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos h34)
  have h1 : (1 : Ordinal) ≤ omega0 ^ (x + 4) := by
    have h0 : (0 : Ordinal) ≤ x + 4 := zero_le _
    have := Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos h0
    simpa [Ordinal.opow_zero] using this
  have t1 : (omega0 ^ (2 : Ordinal)) * (x + 1) + 1 ≤ omega0 ^ (x + 4) + 1 := add_le_add_right hB 1
  have t2 : omega0 ^ (x + 4) + 1 ≤ omega0 ^ (x + 4) + omega0 ^ (x + 4) := add_le_add_left h1 _

  have hsum1 :
      (omega0 ^ (2 : Ordinal)) * (x + 1) + 1 ≤ omega0 ^ (x + 4) + omega0 ^ (x + 4) :=
    t1.trans t2
  have hsum2 :
      (omega0 ^ (3 : Ordinal)) * (x + 1) + ((omega0 ^ (2 : Ordinal)) * (x + 1) + 1)
        ≤ omega0 ^ (x + 4) + (omega0 ^ (x + 4) + omega0 ^ (x + 4)) :=
    add_le_add hA hsum1

  set a : Ordinal := omega0 ^ (x + 4) with ha
  have h2 : a * (2 : Ordinal) = a * (1 : Ordinal) + a := by
    simpa using (Ordinal.mul_succ a (1 : Ordinal))
  have h3step : a * (3 : Ordinal) = a * (2 : Ordinal) + a := by
    simpa using (Ordinal.mul_succ a (2 : Ordinal))
  have hthree' : a * (3 : Ordinal) = a + (a + a) := by
    calc
      a * (3 : Ordinal)
          = a * (2 : Ordinal) + a := by simpa using h3step
      _   = (a * (1 : Ordinal) + a) + a := by simpa [h2]
      _   = (a + a) + a := by simp [mul_one]
      _   = a + (a + a) := by simp [add_assoc]
  have hsum3 :
      omega0 ^ (x + 4) + (omega0 ^ (x + 4) + omega0 ^ (x + 4))
        ≤ (omega0 ^ (x + 4)) * (3 : Ordinal) := by
    have h := hthree'.symm
    simpa [ha] using (le_of_eq h)

  have h3ω : (3 : Ordinal) ≤ omega0 := by
    exact le_of_lt (by simpa using (lt_omega0.2 ⟨3, rfl⟩))
  have hlift :
      (omega0 ^ (x + 4)) * (3 : Ordinal) ≤ (omega0 ^ (x + 4)) * omega0 := by
    simpa using mul_le_mul_left' h3ω (omega0 ^ (x + 4))
  have htow : (omega0 ^ (x + 4)) * omega0 = omega0 ^ (x + 5) := by
    simpa [add_comm, add_left_comm, add_assoc]
      using (Ordinal.opow_add omega0 (x + 4) (1 : Ordinal)).symm

  exact hsum2.trans (hsum3.trans (by simpa [htow] using hlift))

theorem payload_bound_merge_mu (a : Trace) :
  (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) + ((omega0 ^ (2 : Ordinal)) * (MetaSN.mu a + 1) + 1)
    ≤ omega0 ^ (MetaSN.mu a + 5) := by
  simpa using payload_bound_merge (MetaSN.mu a)

-- (legacy name replaced) ensure single definition only
-- theorem lt_add_one (x : Ordinal) : x < x + 1 := lt_add_one_of_le (le_rfl)
theorem lt_add_one (x : Ordinal) : x < x + 1 :=
  (Order.lt_add_one_iff (x := x) (y := x)).2 le_rfl

theorem lt_add_one_of_le {x y : Ordinal} (h : x ≤ y) : x < y + 1 :=
  (Order.lt_add_one_iff (x := x) (y := y)).2 h

theorem le_of_lt_add_one {x y : Ordinal} (h : x < y + 1) : x ≤ y :=
  (Order.lt_add_one_iff (x := x) (y := y)).1 h

-- mul_succ is provided by the patch compat layer
-- mul_succ is provided by the patch compat layer
-- Additional local copy from Termination_C (safe and self-contained)
theorem mul_succ (a b : Ordinal) : a * (b + 1) = a * b + a := by
  simpa [mul_one, add_comm, add_left_comm, add_assoc] using
    (mul_add a b (1 : Ordinal))
-- (mu_lt_delta is defined later near the μ-δ section.)

theorem two_lt_mu_delta_add_six (n : Trace) :
  (2 : Ordinal) < MetaSN.mu (.delta n) + 6 := by
  have h2lt6 : (2 : Ordinal) < 6 := by
    have : (2 : ℕ) < 6 := by decide
    simpa using (natCast_lt).2 this
  have h6le : (6 : Ordinal) ≤ MetaSN.mu (.delta n) + 6 := by
    have hμ : (0 : Ordinal) ≤ MetaSN.mu (.delta n) := zero_le _
    simpa [zero_add] using add_le_add_right hμ (6 : Ordinal)
  exact lt_of_lt_of_le h2lt6 h6le

private theorem pow2_le_A {n : Trace} {A : Ordinal}
    (hA : A = omega0 ^ (MetaSN.mu (Trace.delta n) + 6)) :
    (omega0 ^ (2 : Ordinal)) ≤ A := by
  have h : (2 : Ordinal) ≤ MetaSN.mu (Trace.delta n) + 6 :=
    le_of_lt (two_lt_mu_delta_add_six n)
  simpa [hA] using Ordinal.opow_le_opow_right omega0_pos h

private theorem omega_le_A {n : Trace} {A : Ordinal}
    (hA : A = omega0 ^ (MetaSN.mu (Trace.delta n) + 6)) :
    (omega0 : Ordinal) ≤ A := by
  have pos : (0 : Ordinal) < MetaSN.mu (Trace.delta n) + 6 :=
    lt_of_le_of_lt (bot_le) (two_lt_mu_delta_add_six n)
  simpa [hA] using Ordinal.left_le_opow (a := omega0) (b := MetaSN.mu (Trace.delta n) + 6) pos

--- not used---
private theorem head_plus_tail_le {b s n : Trace}
    {A B : Ordinal}
    (tail_le_A :
      (omega0 ^ (2 : Ordinal)) * (MetaSN.mu (Trace.recΔ b s n) + 1) + 1 ≤ A)
    (Apos : 0 < A) :
    B + ((omega0 ^ (2 : Ordinal)) * (MetaSN.mu (Trace.recΔ b s n) + 1) + 1) ≤
      A * (B + 1) := by
  -- 1 ▸ `B ≤ A * B`  (since `A > 0`)
  have B_le_AB : B ≤ A * B :=
    le_mul_right (a := B) (b := A) Apos

  have hsum :
      B + ((omega0 ^ (2 : Ordinal)) * (MetaSN.mu (Trace.recΔ b s n) + 1) + 1) ≤
        A * B + A :=

    add_le_add B_le_AB tail_le_A

  have head_dist : A * (B + 1) = A * B + A := by
    simpa using Ordinal.mul_succ A B       -- `a * (b+1) = a * b + a`

  rw [head_dist]; exact hsum


/-- **Strict** monotone: `b < c → ω^b < ω^c`. -/
theorem opow_lt_opow_ω {b c : Ordinal} (h : b < c) :
    omega0 ^ b < omega0 ^ c := by
  simpa using
    ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)

theorem opow_le_opow_ω {p q : Ordinal} (h : p ≤ q) :
    omega0 ^ p ≤ omega0 ^ q := by
  exact Ordinal.opow_le_opow_right omega0_pos h   -- library lemma

theorem three_lt_mu_delta (n : Trace) :
    (3 : Ordinal) < MetaSN.mu (delta n) + 6 := by
  have : (3 : ℕ) < 6 := by decide
  have h₃₆ : (3 : Ordinal) < 6 := by
    simpa using (Nat.cast_lt).2 this
  have hμ : (0 : Ordinal) ≤ MetaSN.mu (delta n) := Ordinal.zero_le _
  have h₆ : (6 : Ordinal) ≤ MetaSN.mu (delta n) + 6 :=
    le_add_of_nonneg_left (a := (6 : Ordinal)) hμ
  exact lt_of_lt_of_le h₃₆ h₆

theorem w3_lt_A (s n : Trace) :
  omega0 ^ (3 : Ordinal) < omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6) := by

  have h₁ : (3 : Ordinal) < MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
    -- 1a  finite part   3 < 6
    have h3_lt_6 : (3 : Ordinal) < 6 := by
      simpa using (natCast_lt).2 (by decide : (3 : ℕ) < 6)
    -- 1b  padding       6 ≤ μ(δ n) + μ s + 6
    have h6_le : (6 : Ordinal) ≤ MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
      -- non-negativity of the middle block
      have hμ : (0 : Ordinal) ≤ MetaSN.mu (delta n) + MetaSN.mu s := by
        have hδ : (0 : Ordinal) ≤ MetaSN.mu (delta n) := Ordinal.zero_le _
        have hs : (0 : Ordinal) ≤ MetaSN.mu s         := Ordinal.zero_le _
        -- 0 + 0 ≤ μ(δ n) + μ s
        simpa [zero_add] using add_le_add hδ hs
      -- 6 ≤ (μ(δ n)+μ s) + 6
      have : (6 : Ordinal) ≤ (MetaSN.mu (delta n) + MetaSN.mu s) + 6 :=
        le_add_of_nonneg_left hμ
      -- reassociate to `μ(δ n)+μ s+6`
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact lt_of_lt_of_le h3_lt_6 h6_le

  exact OperatorKO7.Patch2025_08_10.opow_lt_opow_right h₁

theorem coeff_lt_A (s n : Trace) :
    MetaSN.mu s + 1 < omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 3) := by
  have h₁ : MetaSN.mu s + 1 < MetaSN.mu s + 3 := by
    have h_nat : (1 : Ordinal) < 3 := by
      norm_num
    simpa using (add_lt_add_left h_nat (MetaSN.mu s))

  have h₂ : MetaSN.mu s + 3 ≤ MetaSN.mu (delta n) + MetaSN.mu s + 3 := by
    have hμ : (0 : Ordinal) ≤ MetaSN.mu (delta n) := Ordinal.zero_le _
    have h_le : (MetaSN.mu s) ≤ MetaSN.mu (delta n) + MetaSN.mu s :=
      (le_add_of_nonneg_left hμ)
    simpa [add_comm, add_left_comm, add_assoc]
      using add_le_add_right h_le 3

  have h_chain : MetaSN.mu s + 1 < MetaSN.mu (delta n) + MetaSN.mu s + 3 :=
    lt_of_lt_of_le h₁ h₂

  have h_big : MetaSN.mu (delta n) + MetaSN.mu s + 3 ≤
               omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 3) :=
    le_omega_pow (x := MetaSN.mu (delta n) + MetaSN.mu s + 3)

  exact lt_of_lt_of_le h_chain h_big

theorem head_lt_A (s n : Trace) :
  let A : Ordinal := omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6);
  omega0 ^ (3 : Ordinal) * (MetaSN.mu s + 1) < A := by
  intro A

  have h₁ : omega0 ^ (3 : Ordinal) * (MetaSN.mu s + 1) ≤
            omega0 ^ (MetaSN.mu s + 4) := termA_le (x := MetaSN.mu s)


  have h_left : MetaSN.mu s + 4 < MetaSN.mu s + 6 := by
    have : (4 : Ordinal) < 6 := by
      simpa using (natCast_lt).2 (by decide : (4 : ℕ) < 6)
    simpa using (add_lt_add_left this (MetaSN.mu s))

  -- 2b  insert `μ δ n` on the left using monotonicity
  have h_pad : MetaSN.mu s + 6 ≤ MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
    -- 0 ≤ μ δ n
    have hμ : (0 : Ordinal) ≤ MetaSN.mu (delta n) := Ordinal.zero_le _
    -- μ s ≤ μ δ n + μ s
    have h₀ : (MetaSN.mu s) ≤ MetaSN.mu (delta n) + MetaSN.mu s :=
      le_add_of_nonneg_left hμ
    -- add the finite 6 to both sides
    have h₀' : MetaSN.mu s + 6 ≤ (MetaSN.mu (delta n) + MetaSN.mu s) + 6 :=
      add_le_add_right h₀ 6
    simpa [add_comm, add_left_comm, add_assoc] using h₀'

  -- 2c  combine
  have h_exp : MetaSN.mu s + 4 < MetaSN.mu (delta n) + MetaSN.mu s + 6 :=
    lt_of_lt_of_le h_left h_pad


  have h₂ : omega0 ^ (MetaSN.mu s + 4) <
            omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6) := OperatorKO7.Patch2025_08_10.opow_lt_opow_right h_exp

  have h_final :
      omega0 ^ (3 : Ordinal) * (MetaSN.mu s + 1) <
      omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6) := lt_of_le_of_lt h₁ h₂

  simpa [A] using h_final


private lemma two_lt_three : (2 : Ordinal) < 3 := by
  have : (2 : ℕ) < 3 := by decide
  simpa using (Nat.cast_lt).2 this



@[simp] theorem opow_mul_lt_of_exp_lt
    {β α γ : Ordinal} (hβ : β < α) (hγ : γ < omega0) :
    omega0 ^ β * γ < omega0 ^ α := by

  have hpos : (0 : Ordinal) < omega0 ^ β :=
    Ordinal.opow_pos (a := omega0) (b := β) omega0_pos
  have h₁ : omega0 ^ β * γ < omega0 ^ β * omega0 :=
    Ordinal.mul_lt_mul_of_pos_left hγ hpos


  have h_eq : omega0 ^ β * omega0 = omega0 ^ (β + 1) := by
    simpa [Ordinal.opow_add] using (Ordinal.opow_add omega0 β 1).symm
  have h₁' : omega0 ^ β * γ < omega0 ^ (β + 1) := by
    simpa [h_eq, -opow_succ] using h₁


  have h_exp : β + 1 ≤ α := Order.add_one_le_of_lt hβ  -- FIXED: Use Order.add_one_le_of_lt instead
  have h₂ : omega0 ^ (β + 1) ≤ omega0 ^ α :=
    opow_le_opow_right (a := omega0) omega0_pos h_exp


  exact lt_of_lt_of_le h₁' h₂


lemma omega_pow_add_lt
    {κ α β : Ordinal} (_ : 0 < κ)
    (hα : α < omega0 ^ κ) (hβ : β < omega0 ^ κ) :
    α + β < omega0 ^ κ := by
  have hprin : Principal (fun x y : Ordinal => x + y) (omega0 ^ κ) :=
    Ordinal.principal_add_omega0_opow κ
  exact hprin hα hβ


lemma omega_pow_add3_lt
    {κ α β γ : Ordinal} (hκ : 0 < κ)
    (hα : α < omega0 ^ κ) (hβ : β < omega0 ^ κ) (hγ : γ < omega0 ^ κ) :
    α + β + γ < omega0 ^ κ := by
  have hsum : α + β < omega0 ^ κ :=
    omega_pow_add_lt hκ hα hβ
  have hsum' : α + β + γ < omega0 ^ κ :=
    omega_pow_add_lt hκ (by simpa using hsum) hγ
  simpa [add_assoc] using hsum'


theorem mu_recΔ_plus_3_lt (b s n : Trace)
  (h_bound : omega0 ^ (mu n + mu s + (6 : Ordinal)) + omega0 * (mu b + 1) + 1 + 3 <
             (omega0 ^ (5 : Ordinal)) * (mu n + 1) + 1 + mu s + 6) :
  mu (recΔ b s n) + 3 < mu (delta n) + mu s + 6 := by
  -- Convert both sides using mu definitions - now should match exactly
  simp only [mu]
  exact h_bound




@[simp] lemma add_one_lt_omega0 (k : ℕ) :
    ((k : Ordinal) + 1) < omega0 := by
  -- `k.succ < ω`
  have : ((k.succ : ℕ) : Ordinal) < omega0 := by
    simpa using (nat_lt_omega0 k.succ)
  simpa [Nat.cast_succ, add_comm, add_left_comm, add_assoc,
         add_one_eq_succ] using this

@[simp] lemma one_le_omega0 : (1 : Ordinal) ≤ omega0 :=
  (le_of_lt (by
    have : ((1 : ℕ) : Ordinal) < omega0 := by
      simpa using (nat_lt_omega0 1)
    simpa using this))


lemma add_le_add_of_le_of_nonneg {a b c : Ordinal}
    (h : a ≤ b) (_ : (0 : Ordinal) ≤ c := by exact Ordinal.zero_le _)
    : a + c ≤ b + c :=
  add_le_add_right h c

@[simp] lemma lt_succ (a : Ordinal) : a < Order.succ a := by
  have : a < a + 1 := lt_add_of_pos_right _ OperatorKO7.Patch2025_08_10.zero_lt_one_ordinal
  simpa [Order.succ] using this

-- alias and zero_lt_one are provided by the patch / core

-- Local helper from Termination_C (not strictly needed but useful in proofs)
lemma zero_lt_one : (0 : Ordinal) < 1 := by norm_num

attribute [simp] Ordinal.IsNormal.strictMono

-- Helper for successor positivity
lemma succ_pos (a : Ordinal) : (0 : Ordinal) < Order.succ a := by
  -- Order.succ a = a + 1, and we need 0 < a + 1
  -- This is true because 0 < 1 and a ≥ 0
  have h1 : (0 : Ordinal) ≤ a := Ordinal.zero_le a
  have h2 : (0 : Ordinal) < 1 := OperatorKO7.Patch2025_08_10.zero_lt_one_ordinal
  -- Since Order.succ a = a + 1
  rw [Order.succ]
  -- 0 < a + 1 follows from 0 ≤ a and 0 < 1
  exact lt_of_lt_of_le h2 (le_add_of_nonneg_left h1)

-- duplicate succ_succ removed (defined earlier)
@[simp] lemma succ_succ (a : Ordinal) :
    Order.succ (Order.succ a) = a + 2 := by
  have h1 : Order.succ a = a + 1 := rfl
  rw [h1]
  have h2 : Order.succ (a + 1) = (a + 1) + 1 := rfl
  rw [h2, add_assoc]
  norm_num

lemma add_two (a : Ordinal) :
    a + 2 = Order.succ (Order.succ a) := (succ_succ a).symm

@[simp] theorem opow_lt_opow_right_iff {a b : Ordinal} :
    (omega0 ^ a < omega0 ^ b) ↔ a < b := by
  constructor
  · intro hlt
    by_contra hnb          -- assume ¬ a < b, hence b ≤ a
    have hle : b ≤ a := _root_.le_of_not_gt hnb
    have hle' : omega0 ^ b ≤ omega0 ^ a := opow_le_opow_ω hle
    exact (not_le_of_gt hlt) hle'
  · intro hlt
    exact opow_lt_opow_ω hlt

/-- Strict-mono of ω-powers in the exponent (base `omega0`). --/
@[simp] theorem opow_lt_opow_right {b c : Ordinal} (h : b < c) :
  omega0 ^ b < omega0 ^ c := by
  simpa using ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)


@[simp] theorem le_of_lt_add_of_pos {a c : Ordinal} (hc : (0 : Ordinal) < c) :
    a ≤ a + c := by
  have hc' : (0 : Ordinal) ≤ c := le_of_lt hc
  simpa using (le_add_of_nonneg_right (a := a) hc')


/--  The "tail" payload sits strictly below the big tower `A`. -/
lemma tail_lt_A {b s n : Trace}
  (h_mu_recΔ_bound : omega0 ^ (MetaSN.mu n + MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 + 3 <
                     (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) + 1 + MetaSN.mu s + 6) :
    let A : Ordinal := omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6)
    omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) < A := by
  intro A
  -- Don't define α separately - just use the expression directly

  ---------------------------------------------------------------- 1
  --  ω²·(μ(recΔ)+1) ≤ ω^(μ(recΔ)+3)
  have h₁ : omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) ≤
            omega0 ^ (MetaSN.mu (recΔ b s n) + 3) :=
    termB_le _

  ---------------------------------------------------------------- 2
  --  μ(recΔ) + 3 < μ(δn) + μs + 6 (key exponent inequality)
  have hμ : MetaSN.mu (recΔ b s n) + 3 < MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
    -- Use the parameterized lemma with the ordinal domination assumption
    exact mu_recDelta_plus_3_lt b s n h_mu_recΔ_bound

  --  Therefore exponent inequality:
  have h₂ : MetaSN.mu (recΔ b s n) + 3 < MetaSN.mu (delta n) + MetaSN.mu s + 6 := hμ

  --  Now lift through ω-powers using strict monotonicity
  have h₃ : omega0 ^ (MetaSN.mu (recΔ b s n) + 3) < omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6) :=
    OperatorKO7.Patch2025_08_10.opow_lt_opow_right h₂

  ---------------------------------------------------------------- 3
  --  The final chaining: combine termB_le with the exponent inequality
  have h_final : omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) <
                 omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6) :=
    lt_of_le_of_lt h₁ h₃

  ---------------------------------------------------------------- 4
  --  This is exactly what we needed to prove
  exact h_final



lemma mu_merge_lt_rec {b s n : Trace}
  (h_mu_recΔ_bound : omega0 ^ (MetaSN.mu n + MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 + 3 <
                     (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) + 1 + MetaSN.mu s + 6) :
  MetaSN.mu (merge s (recΔ b s n)) < MetaSN.mu (recΔ b s (delta n)) := by
  -- rename the dominant tower once and for all
  set A : Ordinal := omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6) with hA
  -- ❶  head        (ω³ payload)  < A
  have h_head : omega0 ^ (3 : Ordinal) * (MetaSN.mu s + 1) < A := by
    simpa [hA] using head_lt_A s n
  -- ❷  tail        (ω² payload)  < A  (new lemma)
  have h_tail : omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) < A := by
    simpa [hA] using tail_lt_A (b := b) (s := s) (n := n) h_mu_recΔ_bound
  -- ❸  sum of head + tail + 1 < A.
  have h_sum :
      omega0 ^ (3 : Ordinal) * (MetaSN.mu s + 1) +
      (omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) + 1) < A := by
    -- First fold inner `tail+1` under A.
    have h_tail1 :
        omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) + 1 < A :=

      omega_pow_add_lt (by
        -- Prove positivity of exponent
        have : (0 : Ordinal) < MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
          -- Simple positivity: 0 < 6 ≤ μ(δn) + μs + 6
          have h6_pos : (0 : Ordinal) < 6 := by norm_num
          exact lt_of_lt_of_le h6_pos (le_add_left 6 (MetaSN.mu (delta n) + MetaSN.mu s))
        exact this) h_tail (by
        -- `1 < A` trivially (tower is non‑zero)
        have : (1 : Ordinal) < A := by
          have hpos : (0 : Ordinal) < A := by
            rw [hA]
            exact Ordinal.opow_pos (b := MetaSN.mu (delta n) + MetaSN.mu s + 6) (a0 := omega0_pos)
          -- We need 1 < A. We have 0 < A and 1 ≤ ω, and we need ω ≤ A
          have omega_le_A : omega0 ≤ A := by
            rw [hA]
            -- Need to show MetaSN.mu (delta n) + MetaSN.mu s + 6 > 0
            have hpos : (0 : Ordinal) < MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
              -- Positivity: μ(δn) + μs + 6 ≥ 6 > 0
              have h6_pos : (0 : Ordinal) < 6 := by norm_num
              exact lt_of_lt_of_le h6_pos (le_add_left 6 (MetaSN.mu (delta n) + MetaSN.mu s))
            exact Ordinal.left_le_opow (a := omega0) (b := MetaSN.mu (delta n) + MetaSN.mu s + 6) hpos
          -- Need to show 1 < A. We have 1 ≤ ω ≤ A, so 1 ≤ A. We need strict.
          -- Since A = ω^(μ(δn) + μs + 6) and the exponent > 0, we have ω < A
          have omega_lt_A : omega0 < A := by
            rw [hA]
            -- Use the fact that ω < ω^k when k > 1
            have : (1 : Ordinal) < MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
              -- Positivity: μ(δn) + μs + 6 ≥ 6 > 1
              have h6_gt_1 : (1 : Ordinal) < 6 := by norm_num
              exact lt_of_lt_of_le h6_gt_1 (le_add_left 6 (MetaSN.mu (delta n) + MetaSN.mu s))
            have : omega0 ^ (1 : Ordinal) < omega0 ^ (MetaSN.mu (delta n) + MetaSN.mu s + 6) :=
              OperatorKO7.Patch2025_08_10.opow_lt_opow_right this
            simpa using this
          exact lt_of_le_of_lt one_le_omega0 omega_lt_A
        exact this)
    -- Then fold head + (tail+1).
    have h_fold := omega_pow_add_lt (by
        -- Same positivity proof
        have : (0 : Ordinal) < MetaSN.mu (delta n) + MetaSN.mu s + 6 := by
          -- Simple positivity: 0 < 6 ≤ μ(δn) + μs + 6
          have h6_pos : (0 : Ordinal) < 6 := by norm_num
          exact lt_of_lt_of_le h6_pos (le_add_left 6 (MetaSN.mu (delta n) + MetaSN.mu s))
        exact this) h_head h_tail1
    -- Need to massage the associativity to match expected form
    have : omega0 ^ (3 : Ordinal) * (MetaSN.mu s + 1) + (omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) + 1) < A := by
      -- h_fold has type: ω^3 * (μa + 1) + (ω^2 * (μb + 1) + 1) < ω^(μ(δn) + μs + 6)
      -- A = ω^(μ(δn) + μs + 6) by definition
      rw [hA]
      exact h_fold
    exact this
  -- ❹  RHS is   A + ω·… + 1  >  A  >  LHS.
  have h_rhs_gt_A : A < MetaSN.mu (recΔ b s (delta n)) := by
    -- by definition of μ(recΔ … (δ n)) (see new μ)
    have : A < A + omega0 * (MetaSN.mu b + 1) + 1 := by
      have hpos : (0 : Ordinal) < omega0 * (MetaSN.mu b + 1) + 1 := by
        -- ω*(μb + 1) + 1 ≥ 1 > 0
        have h1_pos : (0 : Ordinal) < 1 := by norm_num
        exact lt_of_lt_of_le h1_pos (le_add_left 1 (omega0 * (MetaSN.mu b + 1)))
      -- A + (ω·(μb + 1) + 1) = (A + ω·(μb + 1)) + 1
      have : A + omega0 * (MetaSN.mu b + 1) + 1 = A + (omega0 * (MetaSN.mu b + 1) + 1) := by
        simp [add_assoc]
      rw [this]
      exact lt_add_of_pos_right A hpos
    rw [hA]
    exact this
  -- ❺  chain inequalities.
  have : MetaSN.mu (merge s (recΔ b s n)) < A := by
    -- rewrite μ(merge …) exactly and apply `h_sum`
    have eq_mu : MetaSN.mu (merge s (recΔ b s n)) =
        omega0 ^ (3 : Ordinal) * (MetaSN.mu s + 1) +
        (omega0 ^ (2 : Ordinal) * (MetaSN.mu (recΔ b s n) + 1) + 1) := by
      -- MetaSN.mu (merge a b) = ω³ * (μa + 1) + ω² * (μb + 1) + 1
      -- This is the definition of mu for merge, but the pattern matching
      -- makes rfl difficult. The issue is associativity: (a + b) + c vs a + (b + c)
      simp only [mu, add_assoc]
    rw [eq_mu]
    exact h_sum
  exact lt_trans this h_rhs_gt_A

@[simp] lemma mu_lt_rec_succ (b s n : Trace)
  (h_mu_recΔ_bound : omega0 ^ (MetaSN.mu n + MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 + 3 <
                     (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) + 1 + MetaSN.mu s + 6) :
  MetaSN.mu (merge s (recΔ b s n)) < MetaSN.mu (recΔ b s (delta n)) := by
  simpa using mu_merge_lt_rec h_mu_recΔ_bound

/-- Helper: lift mu-strict decrease to lexicographic order when kappa is unchanged -/
lemma μ_to_μκ {t t' : Trace} (h : mu t' < mu t) (hk : kappa t' = kappa t) :
  LexNatOrd (μκ t') (μκ t) := by
  unfold LexNatOrd μκ
  rw [hk]
  apply Prod.Lex.right
  exact h

/-- Lexicographic decrease for R_rec_succ: kappa strictly decreases -/
lemma μκ_lt_R_rec_succ (b s n : Trace) :
  LexNatOrd (μκ (app s (recΔ b s n))) (μκ (recΔ b s (delta n))) := by
  unfold LexNatOrd μκ
  apply Prod.Lex.left
  simp [kappa]

/-- κ strictly drops in the rec-successor rule under the current `kappa` definition. -/
@[simp] lemma kappa_drop_recSucc (b s n : Trace) :
  kappa (app s (recΔ b s n)) < kappa (recΔ b s (delta n)) := by
  simp [kappa]

-- Alias: same statement with a clearer name for direct use in step proofs.
lemma μκ_lex_drop_recSucc (b s n : Trace) :
  LexNatOrd (μκ (app s (recΔ b s n))) (μκ (recΔ b s (delta n))) :=
  μκ_lt_R_rec_succ b s n

/-- `R_int_delta`: κ equal (both 0); use μ-drop. -/
lemma μκ_drop_R_int_delta (t : Trace) :
  LexNatOrd (μκ void) (μκ (integrate (delta t))) := by
  have hμ : mu void < mu (integrate (delta t)) := MetaSN.mu_void_lt_integrate_delta t
  have hk : kappa void = kappa (integrate (delta t)) := by simp [kappa]
  exact μ_to_μκ (t' := void) (t := integrate (delta t)) hμ hk

/-- `R_eq_refl`: κ equal (both 0); use μ-drop. -/
lemma μκ_drop_R_eq_refl (a : Trace) :
  LexNatOrd (μκ void) (μκ (eqW a a)) := by
  have hμ : mu void < mu (eqW a a) := MetaSN.mu_void_lt_eq_refl a
  have hk : kappa void = kappa (eqW a a) := by simp [kappa]
  exact μ_to_μκ (t' := void) (t := eqW a a) hμ hk

/-! Dependent lex drops where κ is unchanged because the result is non-`recΔ`. -/

/-- `R_merge_void_right` when result is non-`recΔ`: κ equal (both 0); use μ-drop. -/
lemma μκ_drop_R_merge_void_right_nonrec
  (t : Trace) (h : ¬ ∃ b s n, t = recΔ b s n) :
  LexNatOrd (μκ t) (μκ (merge t void)) := by
  have hμ : mu t < mu (merge t void) := MetaSN.mu_lt_merge_void_right t
  have hk_t : kappa t = 0 := kappa_non_rec t h
  have hk_merge : kappa (merge t void) = 0 := by simp [kappa]
  have hk : kappa t = kappa (merge t void) := by simpa [hk_merge] using hk_t
  exact μ_to_μκ (t' := t) (t := merge t void) hμ hk

/-- `R_merge_cancel` when result is non-`recΔ`: κ equal (both 0); use μ-drop. -/
lemma μκ_drop_R_merge_cancel_nonrec
  (t : Trace) (h : ¬ ∃ b s n, t = recΔ b s n) :
  LexNatOrd (μκ t) (μκ (merge t t)) := by
  have hμ : mu t < mu (merge t t) := MetaSN.mu_lt_merge_cancel t
  have hk_t : kappa t = 0 := kappa_non_rec t h
  have hk_merge : kappa (merge t t) = 0 := by simp [kappa]
  have hk : kappa t = kappa (merge t t) := by simpa [hk_merge] using hk_t
  exact μ_to_μκ (t' := t) (t := merge t t) hμ hk

/-- `R_rec_zero` when `b` is non-`recΔ`: κ strictly drops (0 → 1). -/
lemma μκ_drop_R_rec_zero_nonrec (b s : Trace)
  (h : ¬ ∃ b' s' n', b = recΔ b' s' n') :
  LexNatOrd (μκ b) (μκ (recΔ b s void)) := by
  unfold LexNatOrd μκ
  apply Prod.Lex.left
  have hk_b : kappa b = 0 := kappa_non_rec b h
  simp [kappa, hk_b]


/-- Any non-void trace has `μ ≥ ω`.  Exhaustive on constructors. -/
private theorem nonvoid_mu_ge_omega {t : Trace} (h : t ≠ .void) :
    omega0 ≤ MetaSN.mu t := by
  -- structural recursion accepted via pattern matching on t
  cases t with
  | void => exact (h rfl).elim
  | delta s =>
      -- ω ≤ ω⁵ ≤ ω⁵·(μ s + 1) + 1
      have hω_pow : omega0 ≤ omega0 ^ (5 : Ordinal) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos (by norm_num : (1 : Ordinal) ≤ 5)
      have h_one_le : (1 : Ordinal) ≤ MetaSN.mu s + 1 := by
        have : (0 : Ordinal) ≤ MetaSN.mu s := zero_le _
        simpa [zero_add] using add_le_add_right this 1
      have hmul :
          omega0 ^ (5 : Ordinal) ≤ (omega0 ^ (5 : Ordinal)) * (MetaSN.mu s + 1) := by
        simpa [mul_one] using
          mul_le_mul_left' h_one_le (omega0 ^ (5 : Ordinal))
      have : omega0 ≤ MetaSN.mu (.delta s) := by
        calc
          omega0 ≤ omega0 ^ (5 : Ordinal) := hω_pow
          _      ≤ (omega0 ^ (5 : Ordinal)) * (MetaSN.mu s + 1) := hmul
          _      ≤ (omega0 ^ (5 : Ordinal)) * (MetaSN.mu s + 1) + 1 :=
                   le_add_of_nonneg_right (show (0 : Ordinal) ≤ 1 by
                     simpa using zero_le_one)
          _      = MetaSN.mu (.delta s) := by simp [MetaSN.mu]
      simpa [MetaSN.mu, add_comm, add_left_comm, add_assoc] using this

  | integrate s =>
      -- ω ≤ ω⁴ ≤ ω⁴·(μ s + 1) + 1
      have hω_pow : omega0 ≤ omega0 ^ (4 : Ordinal) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos (by norm_num : (1 : Ordinal) ≤ 4)
      have h_one_le : (1 : Ordinal) ≤ MetaSN.mu s + 1 := by
        have : (0 : Ordinal) ≤ MetaSN.mu s := zero_le _
        simpa [zero_add] using add_le_add_right this 1
      have hmul :
          omega0 ^ (4 : Ordinal) ≤ (omega0 ^ (4 : Ordinal)) * (MetaSN.mu s + 1) := by
        simpa [mul_one] using
          mul_le_mul_left' h_one_le (omega0 ^ (4 : Ordinal))
      have : omega0 ≤ MetaSN.mu (.integrate s) := by
        calc
          omega0 ≤ omega0 ^ (4 : Ordinal) := hω_pow
          _      ≤ (omega0 ^ (4 : Ordinal)) * (MetaSN.mu s + 1) := hmul
          _      ≤ (omega0 ^ (4 : Ordinal)) * (MetaSN.mu s + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = MetaSN.mu (.integrate s) := by simp [MetaSN.mu]
      simpa [MetaSN.mu, add_comm, add_left_comm, add_assoc] using this

  | merge a b =>
      -- ω ≤ ω² ≤ ω²·(μ b + 1) ≤ μ(merge a b)
      have hω_pow : omega0 ≤ omega0 ^ (2 : Ordinal) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos (by norm_num : (1 : Ordinal) ≤ 2)
      have h_one_le : (1 : Ordinal) ≤ MetaSN.mu b + 1 := by
        have : (0 : Ordinal) ≤ MetaSN.mu b := zero_le _
        simpa [zero_add] using add_le_add_right this 1
      have hmul :
          omega0 ^ (2 : Ordinal) ≤ (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) := by
        simpa [mul_one] using
          mul_le_mul_left' h_one_le (omega0 ^ (2 : Ordinal))
      have h_mid :
          omega0 ≤ (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1 := by
        calc
          omega0 ≤ omega0 ^ (2 : Ordinal) := hω_pow
          _      ≤ (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) := hmul
          _      ≤ (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
      have : omega0 ≤ MetaSN.mu (.merge a b) := by
        have h_expand : (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1 ≤
                        (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) + (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1 := by
          -- Goal: ω^2*(μb+1)+1 ≤ ω^3*(μa+1) + ω^2*(μb+1) + 1
          -- Use add_assoc to change RHS from a+(b+c) to (a+b)+c
          rw [add_assoc]
          exact Ordinal.le_add_left ((omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1) ((omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1))
        calc
          omega0 ≤ (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1 := h_mid
          _      ≤ (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) + (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1 := h_expand
          _      = MetaSN.mu (.merge a b) := by simp [MetaSN.mu]
      simpa [MetaSN.mu, add_comm, add_left_comm, add_assoc] using this

  | recΔ b s n =>
      -- ω ≤ ω^(μ n + μ s + 6) ≤ μ(recΔ b s n)
      have six_le : (6 : Ordinal) ≤ MetaSN.mu n + MetaSN.mu s + 6 := by
        have h1 : (0 : Ordinal) ≤ MetaSN.mu n := zero_le _
        have h2 : (0 : Ordinal) ≤ MetaSN.mu s := zero_le _
        have hsum : (0 : Ordinal) ≤ MetaSN.mu n + MetaSN.mu s := by
          simpa [zero_add] using add_le_add h1 h2
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hsum 6
      have one_le : (1 : Ordinal) ≤ MetaSN.mu n + MetaSN.mu s + 6 :=
        le_trans (by norm_num) six_le
      have hω_pow : omega0 ≤ omega0 ^ (MetaSN.mu n + MetaSN.mu s + 6) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos one_le
      have : omega0 ≤ MetaSN.mu (.recΔ b s n) := by
        calc
          omega0 ≤ omega0 ^ (MetaSN.mu n + MetaSN.mu s + 6) := hω_pow
          _      ≤ omega0 ^ (MetaSN.mu n + MetaSN.mu s + 6) + omega0 * (MetaSN.mu b + 1) :=
                   le_add_of_nonneg_right (zero_le _)
          _      ≤ omega0 ^ (MetaSN.mu n + MetaSN.mu s + 6) + omega0 * (MetaSN.mu b + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = MetaSN.mu (.recΔ b s n) := by simp [MetaSN.mu]
      simpa [MetaSN.mu, add_comm, add_left_comm, add_assoc] using this

  | eqW a b =>
      -- ω ≤ ω^(μ a + μ b + 9) ≤ μ(eqW a b)
      have nine_le : (9 : Ordinal) ≤ MetaSN.mu a + MetaSN.mu b + 9 := by
        have h1 : (0 : Ordinal) ≤ MetaSN.mu a := zero_le _
        have h2 : (0 : Ordinal) ≤ MetaSN.mu b := zero_le _
        have hsum : (0 : Ordinal) ≤ MetaSN.mu a + MetaSN.mu b := by
          simpa [zero_add] using add_le_add h1 h2
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hsum 9
      have one_le : (1 : Ordinal) ≤ MetaSN.mu a + MetaSN.mu b + 9 :=
        le_trans (by norm_num) nine_le
      have hω_pow : omega0 ≤ omega0 ^ (MetaSN.mu a + MetaSN.mu b + 9) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos one_le
      have : omega0 ≤ MetaSN.mu (.eqW a b) := by
        calc
          omega0 ≤ omega0 ^ (MetaSN.mu a + MetaSN.mu b + 9) := hω_pow
          _      ≤ omega0 ^ (MetaSN.mu a + MetaSN.mu b + 9) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = MetaSN.mu (.eqW a b) := by simp [MetaSN.mu]
      simpa [MetaSN.mu, add_comm, add_left_comm, add_assoc] using this

  | app a b =>
      -- Direct lower bound: ω ≤ ω³ ≤ ω³·(μ a + 1) ≤ μ(app a b)
      have hω_pow : omega0 ≤ omega0 ^ (3 : Ordinal) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos (by norm_num : (1 : Ordinal) ≤ 3)
      have h_one_le : (1 : Ordinal) ≤ MetaSN.mu a + 1 := by
        have : (0 : Ordinal) ≤ MetaSN.mu a := zero_le _
        simpa [zero_add] using add_le_add_right this 1
      have hmul :
          omega0 ^ (3 : Ordinal) ≤ (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) := by
        simpa [mul_one] using
          mul_le_mul_left' h_one_le (omega0 ^ (3 : Ordinal))
      have : omega0 ≤ MetaSN.mu (.app a b) := by
        calc
          omega0 ≤ omega0 ^ (3 : Ordinal) := hω_pow
          _      ≤ (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) := hmul
          _      ≤ (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) + (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) :=
                   le_add_of_nonneg_right (zero_le _)
          _      ≤ (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) + (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = MetaSN.mu (.app a b) := by simp [MetaSN.mu, add_assoc]
      simpa using this


/-- If `a` and `b` are **not** both `void`, then `ω ≤ μ a + μ b`. -/
theorem mu_sum_ge_omega_of_not_both_void
    {a b : Trace} (h : ¬ (a = .void ∧ b = .void)) :
    omega0 ≤ MetaSN.mu a + MetaSN.mu b := by
  have h_cases : a ≠ .void ∨ b ≠ .void := by
    by_contra hcontra; push_neg at hcontra; exact h hcontra
  cases h_cases with
  | inl ha =>
      have : omega0 ≤ MetaSN.mu a := nonvoid_mu_ge_omega ha
      have : omega0 ≤ MetaSN.mu a + MetaSN.mu b :=
        le_trans this (le_add_of_nonneg_right (zero_le _))
      exact this
  | inr hb =>
      have : omega0 ≤ MetaSN.mu b := nonvoid_mu_ge_omega hb
      have : omega0 ≤ MetaSN.mu a + MetaSN.mu b :=
        le_trans this (le_add_of_nonneg_left (zero_le _))
      exact this

/-- Inner bound used by `mu_lt_eq_diff`. Let `C = μ a + μ b`. Then `μ (merge a b) + 1 < ω^(C + 5)`. -/
private theorem merge_inner_bound_simple (a b : Trace) :
  let C : Ordinal.{0} := MetaSN.mu a + MetaSN.mu b;
  MetaSN.mu (merge a b) + 1 < omega0 ^ (C + 5) := by
  intro C
  -- head and tail bounds
  have h_head : (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) ≤ omega0 ^ (MetaSN.mu a + 4) := MetaSN.termA_le (x := MetaSN.mu a)
  have h_tail : (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) ≤ omega0 ^ (MetaSN.mu b + 3) := MetaSN.termB_le (x := MetaSN.mu b)
  -- each exponent is strictly less than C+5
  have h_exp1 : MetaSN.mu a + 4 < C + 5 := by
    have h1 : MetaSN.mu a ≤ C := Ordinal.le_add_right _ _
    have h2 : MetaSN.mu a + 4 ≤ C + 4 := add_le_add_right h1 4
    have h3 : C + 4 < C + 5 := add_lt_add_left (by norm_num : (4 : Ordinal) < 5) C
    exact lt_of_le_of_lt h2 h3
  have h_exp2 : MetaSN.mu b + 3 < C + 5 := by
    have h1 : MetaSN.mu b ≤ C := Ordinal.le_add_left (MetaSN.mu b) (MetaSN.mu a)
    have h2 : MetaSN.mu b + 3 ≤ C + 3 := add_le_add_right h1 3
    have h3 : C + 3 < C + 5 := add_lt_add_left (by norm_num : (3 : Ordinal) < 5) C
    exact lt_of_le_of_lt h2 h3
  -- use monotonicity of opow
  have h1_pow : omega0 ^ (3 : Ordinal) * (MetaSN.mu a + 1) < omega0 ^ (C + 5) := by
    calc (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1)
        ≤ omega0 ^ (MetaSN.mu a + 4) := h_head
      _ < omega0 ^ (C + 5) := OperatorKO7.Patch2025_08_10.opow_lt_opow_right h_exp1
  have h2_pow : (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) < omega0 ^ (C + 5) := by
    calc (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1)
        ≤ omega0 ^ (MetaSN.mu b + 3) := h_tail
      _ < omega0 ^ (C + 5) := OperatorKO7.Patch2025_08_10.opow_lt_opow_right h_exp2
  -- finite +2 is below ω^(C+5)
  have h_fin : (2 : Ordinal) < omega0 ^ (C + 5) := by
    have two_lt_omega : (2 : Ordinal) < omega0 := nat_lt_omega0 2
    have omega_le : omega0 ≤ omega0 ^ (C + 5) := by
      have one_le_exp : (1 : Ordinal) ≤ C + 5 := by
        have : (1 : Ordinal) ≤ (5 : Ordinal) := by norm_num
        exact le_trans this (le_add_left _ _)
      calc omega0
          = omega0 ^ (1 : Ordinal) := (Ordinal.opow_one omega0).symm
        _ ≤ omega0 ^ (C + 5) := Ordinal.opow_le_opow_right omega0_pos one_le_exp
    exact lt_of_lt_of_le two_lt_omega omega_le
  -- combine pieces directly for μ(merge a b)+1
  have sum_bound : (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) +
                   (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 2 <
                   omega0 ^ (C + 5) := by
    have k_pos : (0 : Ordinal) < C + 5 := by
      have : (0 : Ordinal) < (5 : Ordinal) := by norm_num
      exact lt_of_lt_of_le this (le_add_left _ _)
    exact omega_pow_add3_lt k_pos h1_pow h2_pow h_fin
  have mu_expand : MetaSN.mu (merge a b) + 1 =
      (omega0 ^ (3 : Ordinal)) * (MetaSN.mu a + 1) +
      (omega0 ^ (2 : Ordinal)) * (MetaSN.mu b + 1) + 2 := by
    simp [MetaSN.mu, add_assoc]
  simpa [mu_expand] using sum_bound

/-- Total inequality used in `R_eq_diff`. -/
theorem mu_lt_eq_diff (a b : Trace) :
  MetaSN.mu (integrate (merge a b)) < MetaSN.mu (eqW a b) := by
  by_cases h_both : a = .void ∧ b = .void
  · rcases h_both with ⟨ha, hb⟩
    -- corner case already proven
    simpa [ha, hb] using mu_lt_eq_diff_both_void
  · -- general case
    set C : Ordinal := MetaSN.mu a + MetaSN.mu b with hC
    have hCω : omega0 ≤ C :=
      by
        have := mu_sum_ge_omega_of_not_both_void (a := a) (b := b) h_both
        simpa [hC] using this

    -- inner bound from `merge_inner_bound_simple`
    have h_inner : MetaSN.mu (merge a b) + 1 < omega0 ^ (C + 5) :=
      by
        simpa [hC] using merge_inner_bound_simple a b

    -- lift through `integrate`
    have ω4pos : 0 < omega0 ^ (4 : Ordinal) :=
      (Ordinal.opow_pos (b := (4 : Ordinal)) omega0_pos)
    have h_mul :
        omega0 ^ (4 : Ordinal) * (MetaSN.mu (merge a b) + 1) <
        omega0 ^ (4 : Ordinal) * omega0 ^ (C + 5) :=
      Ordinal.mul_lt_mul_of_pos_left h_inner ω4pos

    -- collapse ω⁴·ω^(C+5)  →  ω^(4+(C+5))
    have h_prod :
        omega0 ^ (4 : Ordinal) * (MetaSN.mu (merge a b) + 1) <
        omega0 ^ (4 + (C + 5)) :=
      by
        have := (Ordinal.opow_add omega0 (4 : Ordinal) (C + 5)).symm
        simpa [this] using h_mul

    -- absorb the finite 4 because ω ≤ C
    have absorb4 : (4 : Ordinal) + C = C :=
      nat_left_add_absorb (h := hCω)
    have exp_eq : (4 : Ordinal) + (C + 5) = C + 5 := by
      calc
        (4 : Ordinal) + (C + 5)
            = ((4 : Ordinal) + C) + 5 := by
                simpa [add_assoc]
          _ = C + 5 := by
                simpa [absorb4]

    -- inequality now at exponent C+5
    have h_prod2 :
        omega0 ^ (4 : Ordinal) * (MetaSN.mu (merge a b) + 1) <
        omega0 ^ (C + 5) := by
      simpa [exp_eq] using h_prod

    -- bump exponent C+5 → C+9
    have exp_lt : omega0 ^ (C + 5) < omega0 ^ (C + 9) :=
      OperatorKO7.Patch2025_08_10.opow_lt_opow_right (add_lt_add_left (by norm_num) C)

    have h_chain :
        omega0 ^ (4 : Ordinal) * (MetaSN.mu (merge a b) + 1) <
        omega0 ^ (C + 9) := lt_trans h_prod2 exp_lt
    -- add +1 on both sides (monotone)
    have hA1 :
        omega0 ^ (4 : Ordinal) * (MetaSN.mu (merge a b) + 1) + 1 ≤
        omega0 ^ (C + 9) :=
      Order.add_one_le_of_lt h_chain
    have h_final :
        omega0 ^ (4 : Ordinal) * (MetaSN.mu (merge a b) + 1) + 1 <
        omega0 ^ (C + 9) + 1 :=
      (Order.lt_add_one_iff (x := _ + 1) (y := omega0 ^ (C + 9))).2 hA1

    -- rewrite both sides in μ-language and conclude
    have hL : MetaSN.mu (integrate (merge a b)) =
        omega0 ^ (4 : Ordinal) * (MetaSN.mu (merge a b) + 1) + 1 := by
      simp [MetaSN.mu]
    have hR : MetaSN.mu (eqW a b) = omega0 ^ (C + 9) + 1 := by
      simp [MetaSN.mu, hC]
    -- final substitution
    simpa [hL, hR]
      using h_final

/-- `R_eq_diff`: κ equal (both 0); use μ-drop. -/
lemma μκ_drop_R_eq_diff (a b : Trace) :
  LexNatOrd (μκ (integrate (merge a b))) (μκ (eqW a b)) := by
  have hμ : mu (integrate (merge a b)) < mu (eqW a b) := mu_lt_eq_diff a b
  have hk : kappa (integrate (merge a b)) = kappa (eqW a b) := by simp [kappa]
  exact μ_to_μκ (t' := integrate (merge a b)) (t := eqW a b) hμ hk


/-- R₂ (left-void): `merge void t → t` strictly drops `μ`. -/
theorem mu_lt_merge_void_left (t : Trace) :
  MetaSN.mu t < MetaSN.mu (.merge .void t) := by
  -- start: μ t < ω²*(μ t + 1) + 1
  have h0 : MetaSN.mu t ≤ MetaSN.mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := MetaSN.mu t) (y := MetaSN.mu t)).2 le_rfl)
  have hpos2 : 0 < (omega0 ^ (2 : Ordinal)) :=
    (Ordinal.opow_pos (b := (2 : Ordinal)) omega0_pos)
  have h1 : MetaSN.mu t + 1 ≤ (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := MetaSN.mu t + 1) (b := (omega0 ^ (2 : Ordinal))) hpos2)
  have hY : MetaSN.mu t ≤ (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1) := le_trans h0 h1
  have hlt : MetaSN.mu t < (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := MetaSN.mu t) (y := (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1))).2 hY

  -- pad on the left with the ω³ "head" of `merge`
  have hpad :
      (omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1) + 1 ≤
      (omega0 ^ (3 : Ordinal)) + ((omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1) + 1) :=
    Ordinal.le_add_left _ _

  have hfin :
      MetaSN.mu t <
      (omega0 ^ (3 : Ordinal)) + ((omega0 ^ (2 : Ordinal)) * (MetaSN.mu t + 1) + 1) :=
    lt_of_lt_of_le hlt hpad

  simpa [MetaSN.mu, add_assoc] using hfin

/-- `R_merge_void_left` when result is non-`recΔ`: κ equal (both 0); use μ-drop. -/
lemma μκ_drop_R_merge_void_left_nonrec
  (t : Trace) (h : ¬ ∃ b s n, t = recΔ b s n) :
  LexNatOrd (μκ t) (μκ (merge void t)) := by
  have hμ : mu t < mu (merge void t) := mu_lt_merge_void_left t
  have hk_t : kappa t = 0 := kappa_non_rec t h
  have hk_merge : kappa (merge void t) = 0 := by simp [kappa]
  have hk : kappa t = kappa (merge void t) := by simpa [hk_merge] using hk_t
  exact μ_to_μκ (t' := t) (t := merge void t) hμ hk


/-- `R₅ (rec base): `recΔ b s void → b` strictly drops `μ`. -/
theorem mu_lt_rec_base (b s : Trace) :
  MetaSN.mu b < MetaSN.mu (.recΔ b s .void) := by
  -- μ b < μ b + 1
  have h1 : MetaSN.mu b < MetaSN.mu b + 1 := by
    simpa using (lt_add_one (MetaSN.mu b))
  -- μ b + 1 ≤ ω * (μ b + 1)
  have h2 : MetaSN.mu b + 1 ≤ omega0 * (MetaSN.mu b + 1) :=
    Ordinal.le_mul_right (a := MetaSN.mu b + 1) (b := omega0) omega0_pos
  have h3 : MetaSN.mu b < omega0 * (MetaSN.mu b + 1) :=
    lt_of_lt_of_le h1 h2
  -- ω * (μ b + 1) ≤ ω^(μ s + 6) + ω * (μ b + 1) ≤ μ(recΔ b s void)
  have step1 :
      omega0 * (MetaSN.mu b + 1) ≤ omega0 * (MetaSN.mu b + 1) + 1 :=
    le_add_of_nonneg_right (show (0 : Ordinal) ≤ (1 : Ordinal) by exact zero_le _)
  have step2 :
      omega0 * (MetaSN.mu b + 1) + 1 ≤
      omega0 ^ (MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 := by
    have hpad :
        omega0 * (MetaSN.mu b + 1) ≤
        omega0 ^ (MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) :=
      Ordinal.le_add_left _ _
    exact add_le_add_right hpad 1
  have h4 :
      omega0 * (MetaSN.mu b + 1) ≤
      omega0 ^ (MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 :=
    le_trans step1 step2
  have : MetaSN.mu b < omega0 ^ (MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 :=
    lt_of_lt_of_le h3 h4
  simpa [MetaSN.mu] using this

-- Alias from Termination_C: base-case decrease under the name `mu_lt_rec_zero`
-- Same statement as `mu_lt_rec_base`; kept for parity with Termination_C.
-- theorem mu_lt_rec_zero (b s : Trace) :
--     mu b < mu (.recΔ b s .void) := by
--   simpa using (mu_lt_rec_base b s)

/-- Base-case decrease: `recΔ … void`. -/
theorem mu_lt_rec_zero (b s : Trace) :
    mu b < mu (.recΔ b s .void) := by

  have h0 : (mu b) ≤ mu b + 1 :=
    le_of_lt (lt_add_one (mu b))

  have h1 : mu b + 1 ≤ omega0 * (mu b + 1) :=
    Ordinal.le_mul_right (a := mu b + 1) (b := omega0) omega0_pos

  have hle : mu b ≤ omega0 * (mu b + 1) := le_trans h0 h1

  have hlt : mu b < omega0 * (mu b + 1) + 1 := lt_of_le_of_lt hle (lt_add_of_pos_right _ zero_lt_one)

  have hpad :
      omega0 * (mu b + 1) + 1 ≤
      omega0 ^ (mu s + 6) + omega0 * (mu b + 1) + 1 := by
    --  ω^(μ s+6) is non-negative, so adding it on the left preserves ≤
    have : (0 : Ordinal) ≤ omega0 ^ (mu s + 6) :=
      Ordinal.zero_le _
    have h₂ :
        omega0 * (mu b + 1) ≤
        omega0 ^ (mu s + 6) + omega0 * (mu b + 1) :=
      le_add_of_nonneg_left this
    exact add_le_add_right h₂ 1

  have : mu b <
         omega0 ^ (mu s + 6) + omega0 * (mu b + 1) + 1 := lt_of_lt_of_le hlt hpad

  simpa [mu] using this
 -- unfold RHS once


/-! ### Combined termination measure

We avoid the currently unproven domination inequality needed for a direct
`μ` drop on the `recΔ` successor rule by introducing a primary counter that
counts `delta` constructors. The `recΔ` successor rule removes exactly one
outer `delta`, so the primary component strictly decreases there. For all
other rules the `delta` count is unchanged or decreases; when unchanged we
use the existing strict μ drop lemmas. This yields a lexicographic decrease
without new ordinal theory. -/

/-! ### Unconditional μ decrease for recΔ successor and SN via μ -/

/-- μ n + 2 ≤ μ (delta n). -/
lemma mu_n_add_two_le_mu_delta (n : Trace) : MetaSN.mu n + 2 ≤ MetaSN.mu (.delta n) := by
  -- μ(δ n) = ω^5*(μ n + 1) + 1; obviously μ n + 2 ≤ ω^5*(μ n + 1) since ω^5*(μ n +1) dominates μ n +1.
  have h0 : MetaSN.mu n + 1 ≤ (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) := by
    -- Establish 1 ≤ ω^5 via ω ≤ ω^5 and 1 ≤ ω
    have hone : (1 : Ordinal) ≤ omega0 := by simpa using one_le_omega0
    have hωle : omega0 ≤ omega0 ^ (5 : Ordinal) := by
      simpa [Ordinal.opow_one] using
        (Ordinal.opow_le_opow_right omega0_pos (by norm_num : (1 : Ordinal) ≤ (5 : Ordinal)))
    have hge : (1 : Ordinal) ≤ omega0 ^ (5 : Ordinal) := le_trans hone hωle
    -- multiply on the right by (μ n + 1)
    simpa [one_mul] using (mul_le_mul_right' hge (MetaSN.mu n + 1))
  -- Step 2: add one on both sides and close by definition of μ (delta n)
  have h1 : MetaSN.mu n + 2 ≤ (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) + 1 := by
    have := add_le_add_right h0 (1 : Ordinal)
    simpa [add_assoc, succ_succ_eq_add_two, Ordinal.add_one_eq_succ] using this
  simpa [MetaSN.mu, add_assoc] using h1

/-! #### New auxiliary lemmas for unconditional rec successor -/

/-- Strict inequality `μ n < μ (delta n)` (immediate from the δ-case of `mu`). -/
lemma mu_lt_mu_delta (n : Trace) : MetaSN.mu n < MetaSN.mu (.delta n) := by
  -- μ n ≤ ω^5*(μ n +1) implies μ n < ω^5*(μ n +1) + 1 = μ (δ n)
  have h0 : MetaSN.mu n ≤ MetaSN.mu n + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := MetaSN.mu n) (y := MetaSN.mu n)).2 le_rfl)
  have hb : 0 < (omega0 ^ (5 : Ordinal)) :=
    (Ordinal.opow_pos (b := (5 : Ordinal)) (a0 := omega0_pos))
  have h1 : MetaSN.mu n + 1 ≤ (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) := by
    simpa using (Ordinal.le_mul_right (a := MetaSN.mu n + 1) (b := (omega0 ^ (5 : Ordinal))) hb)
  have hle : MetaSN.mu n ≤ (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) := le_trans h0 h1
  have : MetaSN.mu n < (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1) + 1 :=
    (Order.lt_add_one_iff (x := MetaSN.mu n) (y := (omega0 ^ (5 : Ordinal)) * (MetaSN.mu n + 1))).2 hle
  simpa [MetaSN.mu, add_assoc] using this

-- Additional lemma from Termination_C: pointwise delta increase on μ
theorem mu_lt_delta (t : Trace) : mu t < mu (.delta t) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (5 : Ordinal)) :=
    (Ordinal.opow_pos (b := (5 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (5 : Ordinal)) * (mu t + 1) := by
    simpa using (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (5 : Ordinal))) hb)
  have h : mu t ≤ (omega0 ^ (5 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have : mu t < (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff (x := mu t) (y := (omega0 ^ (5 : Ordinal)) * (mu t + 1))).2 h
  simpa [mu] using this

-- Exponent bump comment: aiming at `μ n + μ s + 6 < μ (delta n) + μ s + 6` is
-- invalid without extra hypotheses; right-add strict monotonicity fails in ordinals.
-- We avoid any unconditional version here.

/-- Generic product absorption: if `X < ω^α` and `(k:Ordinal)+α ≤ β` then `ω^k * X < ω^β`.
    (Finite `k`, used with k=2.) -/
lemma omega_pow_fin_mul_cnf_lt {k : ℕ} {α β X : Ordinal}
  (_hk : 0 < k) (hX : X < omega0 ^ α) (hExp : (k : Ordinal) + α ≤ β) :
  omega0 ^ (k : Ordinal) * X < omega0 ^ β := by
  have hpos : (0 : Ordinal) < omega0 ^ (k : Ordinal) :=
    Ordinal.opow_pos (a := omega0) (b := (k : Ordinal)) omega0_pos
  -- step 1: multiply inequality on right factor
  have h1 : omega0 ^ (k : Ordinal) * X < omega0 ^ (k : Ordinal) * (omega0 ^ α) :=
    Ordinal.mul_lt_mul_of_pos_left hX hpos
  -- collapse product of towers
  have h2 : omega0 ^ (k : Ordinal) * X < omega0 ^ ((k : Ordinal) + α) := by
    -- rewrite product of towers via opow_add
    simpa [Ordinal.opow_add, mul_comm, mul_left_comm, mul_assoc]
      using h1
  -- monotone in exponent
  have hmono : omega0 ^ ((k : Ordinal) + α) ≤ omega0 ^ β :=
    Ordinal.opow_le_opow_right omega0_pos hExp
  exact lt_of_lt_of_le h2 hmono


def StepRev (R : Trace → Trace → Prop) : Trace → Trace → Prop := fun a b => R b a

def KernelStep : Trace → Trace → Prop := fun a b => OperatorKO7.Step a b

theorem strong_normalization_forward_trace
  (R : Trace → Trace → Prop)
  (hdec : ∀ {a b : Trace}, R a b → mu b < mu a) :
  WellFounded (StepRev R) := by
  have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
    InvImage.wf (f := mu) (h := Ordinal.lt_wf)
  have hsub : Subrelation (StepRev R) (fun x y : Trace => mu x < mu y) := by
    intro x y h; exact hdec (a := y) (b := x) h
  exact Subrelation.wf hsub hwf

theorem strong_normalization_backward
  (R : Trace → Trace → Prop)
  (hinc : ∀ {a b : Trace}, R a b → mu a < mu b) :
  WellFounded R := by
  have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
    InvImage.wf (f := mu) (h := Ordinal.lt_wf)
  have hsub : Subrelation R (fun x y : Trace => mu x < mu y) := by
    intro x y h
    exact hinc h
  exact Subrelation.wf hsub hwf

end MetaSN
