import Mathlib
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal

/-!
# Fast-Growing Envelope for `SafeStepCtx`

This module packages the existing `ctxFuel` / `towerBound` derivation-length bound
for `SafeStepCtx` inside an explicit finite-level fast-growing hierarchy envelope.
It does not attempt a full slow-growing / Moser--Weiermann extraction from the
ordinal embedding. Instead, it provides a theorem-backed `F_ω`-style majorant whose
level rises with the structural size parameter.
-/

open Function
open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Finite fast-growing hierarchy on naturals. -/
def fastGrow : Nat → Nat → Nat
  | 0, n => n + 1
  | k + 1, n => (fastGrow k)^[n + 1] n

@[simp] theorem fastGrow_zero (n : Nat) : fastGrow 0 n = n + 1 := rfl

private theorem iterate_mono {f : Nat → Nat} (hf : Monotone f) :
    ∀ n : Nat, Monotone (fun x => (f^[n]) x)
  | 0 => by
      intro a b hab
      simpa using hab
  | n + 1 => by
      intro a b hab
      simpa [Function.iterate_succ_apply] using (iterate_mono hf n) (hf hab)

private theorem iterate_count_mono {f : Nat → Nat} (hf : ∀ x, x ≤ f x) (hmono : Monotone f)
    {m n x : Nat} (h : m ≤ n) : (f^[m]) x ≤ (f^[n]) x := by
  induction h with
  | refl =>
      exact le_rfl
  | @step n h ih =>
      exact le_trans ih (by
        rw [Function.iterate_succ_apply]
        exact (iterate_mono hmono n) (hf x))

private theorem fastGrow_mono_infl :
    ∀ k : Nat, Monotone (fastGrow k) ∧ (∀ n : Nat, n ≤ fastGrow k n)
  | 0 => by
      refine ⟨?_, ?_⟩
      · intro a b hab
        simp [fastGrow]
        omega
      · intro n
        simp [fastGrow]
  | k + 1 => by
      rcases fastGrow_mono_infl k with ⟨hmono, hinfl⟩
      refine ⟨?_, ?_⟩
      · intro a b hab
        have hstart : ((fastGrow k)^[a + 1]) a ≤ ((fastGrow k)^[a + 1]) b := by
          exact (iterate_mono hmono (a + 1)) hab
        have hcount : ((fastGrow k)^[a + 1]) b ≤ ((fastGrow k)^[b + 1]) b := by
          exact iterate_count_mono (f := fastGrow k) hinfl hmono (x := b) (by omega)
        simpa [fastGrow] using le_trans hstart hcount
      · intro n
        simpa [fastGrow] using
          (iterate_count_mono (f := fastGrow k) hinfl hmono (x := n) (by omega : 0 ≤ n + 1))

theorem fastGrow_mono_arg (k : Nat) : Monotone (fastGrow k) :=
  (fastGrow_mono_infl k).1

theorem fastGrow_inflationary (k n : Nat) : n ≤ fastGrow k n :=
  (fastGrow_mono_infl k).2 n

theorem fastGrow_level_step (k n : Nat) : fastGrow k n ≤ fastGrow (k + 1) n := by
  have hiter : ((fastGrow k)^[1]) n ≤ ((fastGrow k)^[n + 1]) n := by
    exact iterate_count_mono (f := fastGrow k) (fun x => fastGrow_inflationary k x) (fastGrow_mono_arg k) (x := n) (by omega)
  simpa [fastGrow] using hiter

theorem fastGrow_level_mono {k l n : Nat} (h : k ≤ l) : fastGrow k n ≤ fastGrow l n := by
  induction h with
  | refl =>
      exact le_rfl
  | @step l h ih =>
      exact le_trans ih (fastGrow_level_step l n)

private theorem iterate_succ_eq_add (r x : Nat) : (Nat.succ^[r]) x = x + r := by
  induction r generalizing x with
  | zero =>
      simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, ih]
      omega

@[simp] theorem fastGrow_one (n : Nat) : fastGrow 1 n = 2 * n + 1 := by
  have hzero : fastGrow 0 = Nat.succ := by
    funext x
    simp [fastGrow]
  rw [fastGrow, hzero, iterate_succ_eq_add]
  omega

private theorem iter_double_add_one_plus_one (r x : Nat) :
    ((fun z : Nat => 2 * z + 1)^[r]) x + 1 = 2 ^ r * (x + 1) := by
  induction r generalizing x with
  | zero =>
      simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, ih]
      rw [pow_succ]
      ring_nf

theorem fastGrow_two_plus_one (n : Nat) :
    fastGrow 2 n + 1 = 2 ^ (n + 1) * (n + 1) := by
  rw [fastGrow]
  have hfun : fastGrow 1 = fun z => 2 * z + 1 := by
    funext z
    exact fastGrow_one z
  rw [hfun]
  exact iter_double_add_one_plus_one (n + 1) n

private theorem fastGrow_two_dominates_pow_add (n x : Nat) (hx : x ≤ n) :
    2 ^ n + x + 1 ≤ fastGrow 2 (n + 1) := by
  have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hmain : 2 ^ n + x + 2 ≤ 2 ^ (n + 2) * (n + 2) := by
    calc
      2 ^ n + x + 2 ≤ 2 ^ n + n + 2 := by omega
      _ ≤ 2 ^ n + 2 ^ n * (n + 2) := by
            have : n + 2 ≤ 2 ^ n * (n + 2) := by
              exact le_trans (by omega) (Nat.mul_le_mul_right (n + 2) hone)
            omega
      _ = 2 ^ n * (n + 3) := by ring_nf
      _ ≤ 2 ^ n * (4 * (n + 2)) := by
            have : n + 3 ≤ 4 * (n + 2) := by omega
            exact Nat.mul_le_mul_left (2 ^ n) this
      _ = 2 ^ (n + 2) * (n + 2) := by
            rw [pow_succ, pow_succ]
            ring_nf
  have hclosed := fastGrow_two_plus_one (n + 1)
  have : 2 ^ n + x + 2 ≤ fastGrow 2 (n + 1) + 1 := by
    simpa [hclosed] using hmain
  omega

/-- A size-indexed fast-growing-hierarchy-style envelope for `SafeStepCtx`. -/
def fgOmegaEnvelope : Nat → Nat
  | 0 => 6
  | n + 1 => fastGrow (n + 2) (2 * fgOmegaEnvelope n + 6)

theorem towerBound_le_fgOmegaEnvelope : ∀ n : Nat, towerBound n ≤ fgOmegaEnvelope n
  | 0 => by
      simp [towerBound, fgOmegaEnvelope]
  | n + 1 => by
      have ih := towerBound_le_fgOmegaEnvelope n
      have hdom :
          2 ^ (2 * towerBound n + 5) + towerBound n + 1 ≤
            fastGrow 2 (2 * fgOmegaEnvelope n + 6) := by
        have hlin : towerBound n ≤ 2 * fgOmegaEnvelope n + 5 := by omega
        have hpow :
            2 ^ (2 * towerBound n + 5) + towerBound n + 1 ≤
              2 ^ (2 * fgOmegaEnvelope n + 5) + (2 * fgOmegaEnvelope n + 5) + 1 := by
          have hp :
              2 ^ (2 * towerBound n + 5) ≤ 2 ^ (2 * fgOmegaEnvelope n + 5) := by
            exact Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hfg :
            2 ^ (2 * fgOmegaEnvelope n + 5) + (2 * fgOmegaEnvelope n + 5) + 1 ≤
              fastGrow 2 (2 * fgOmegaEnvelope n + 6) := by
          have hraw :=
            fastGrow_two_dominates_pow_add (2 * fgOmegaEnvelope n + 5) (2 * fgOmegaEnvelope n + 5) (le_rfl)
          convert hraw using 1
        exact le_trans hpow hfg
      calc
        towerBound (n + 1)
            = 2 ^ (2 * towerBound n + 5) + towerBound n + 1 := by
                simp [towerBound]
        _ ≤ fastGrow 2 (2 * fgOmegaEnvelope n + 6) := hdom
        _ ≤ fastGrow (n + 2) (2 * fgOmegaEnvelope n + 6) := by
              exact fastGrow_level_mono (n := 2 * fgOmegaEnvelope n + 6) (show 2 ≤ n + 2 by omega)
        _ = fgOmegaEnvelope (n + 1) := by
              simp [fgOmegaEnvelope]

/-- The existing contextual derivation-length bound is subsumed by the explicit
finite-level fast-growing envelope `fgOmegaEnvelope`. -/
theorem safestep_length_bounded_by_fgOmegaEnvelope (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ fgOmegaEnvelope (termSize t) := by
  exact le_trans (safestep_length_bounded_by_size t u n h) (towerBound_le_fgOmegaEnvelope _)

end MetaSN_KO7
