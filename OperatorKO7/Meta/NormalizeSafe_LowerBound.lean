import OperatorKO7.Meta.Newman_Safe

/-!
Lower bounds for the certified safe normalizer.

This file adds a small executable cost model `normalizeSafeSteps` that follows the same
deterministic recursion as `normalizeSafe`, but counts root contractions instead of returning
the final normal form.

The first worked family is the left-nested `merge void` spine

`mergeVoidChain n = merge void ( ... (merge void void) ... )`

which contracts by `R_merge_void_left` exactly `n` times to `void`.
-/

open OperatorKO7 Trace
open MetaSN_DM
open OperatorKO7.MetaCM

namespace MetaSN_KO7

/-- Exact-length reflexive-transitive closure of `SafeStep`. -/
inductive SafeStepPow : Trace → Nat → Trace → Prop
| refl (t : Trace) : SafeStepPow t 0 t
| tail {a b c : Trace} (hab : SafeStep a b) (hbc : SafeStepPow b n c) :
    SafeStepPow a (n + 1) c

/-- Forget the exact length and obtain a `SafeStepStar` path. -/
theorem safepow_to_safestar {a b : Trace} {n : Nat}
    (h : SafeStepPow a n b) : SafeStepStar a b := by
  induction h with
  | refl t =>
      exact SafeStepStar.refl t
  | tail hab hbc ih =>
      exact SafeStepStar.tail hab ih

/-- Count the number of deterministic root contractions used by the certified normalizer. -/
def normalizeSafeSteps (t : Trace) : Nat :=
  WellFounded.fix wf_Rμ3 (C := fun _ => Nat)
    (fun t rec =>
      match safeStepWitness? t with
      | some w =>
          let u : Trace := w.1
          let hu : SafeStep t u := w.2
          have hdrop : Rμ3 u t := measure_decreases_safe_c hu
          Nat.succ (rec u hdrop)
      | none =>
          0) t

theorem normalizeSafeSteps_eq (t : Trace) :
    normalizeSafeSteps t =
      match safeStepWitness? t with
      | some w => Nat.succ (normalizeSafeSteps w.1)
      | none => 0 := by
  unfold normalizeSafeSteps
  rw [WellFounded.fix_eq]

/-- The guarded root relation is deterministic. -/
theorem safeStep_deterministic {t u v : Trace}
    (hu : SafeStep t u) (hv : SafeStep t v) : u = v := by
  cases hu <;> cases hv <;> simp at *

/-- `void` is a safe normal form. -/
theorem void_nf_safe : NormalFormSafe void := by
  intro h
  rcases h with ⟨u, hu⟩
  cases hu

/-- The certified normalizer fixes `void`. -/
@[simp] theorem normalizeSafe_void : normalizeSafe void = void := by
  exact normalizeSafe_eq_self_of_nf void void_nf_safe

/-- Left-nested `merge void` spine. -/
@[simp] def mergeVoidChain : Nat → Trace
| 0 => void
| n + 1 => merge void (mergeVoidChain n)

@[simp] theorem deltaFlag_mergeVoidChain (n : Nat) :
    deltaFlag (mergeVoidChain n) = 0 := by
  induction n with
  | zero =>
      simp [mergeVoidChain]
  | succ n ih =>
      simp [mergeVoidChain]

/-- The merge spine contracts to `void` by exactly `n` root steps. -/
theorem mergeVoidChain_pow_void (n : Nat) :
    SafeStepPow (mergeVoidChain n) n void := by
  induction n with
  | zero =>
      simpa [mergeVoidChain] using SafeStepPow.refl void
  | succ n ih =>
      have hstep : SafeStep (mergeVoidChain (n + 1)) (mergeVoidChain n) := by
        simpa [mergeVoidChain, deltaFlag_mergeVoidChain n] using
          (SafeStep.R_merge_void_left (mergeVoidChain n) (deltaFlag_mergeVoidChain n))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mergeVoidChain] using
        (SafeStepPow.tail hstep ih)

/-- The merge spine reaches `void` by the uncounted safe-star relation. -/
theorem mergeVoidChain_star_void (n : Nat) :
    SafeStepStar (mergeVoidChain n) void :=
  safepow_to_safestar (mergeVoidChain_pow_void n)

/-- The certified normalizer returns `void` on the merge spine family. -/
@[simp] theorem normalizeSafe_mergeVoidChain (n : Nat) :
    normalizeSafe (mergeVoidChain n) = void := by
  rw [normalizeSafe_eq_of_star (mergeVoidChain_star_void n), normalizeSafe_void]

@[simp] theorem normalizeSafeSteps_void : normalizeSafeSteps void = 0 := by
  rw [normalizeSafeSteps_eq]
  simp [safeStepWitness?]

/-- One merge-left contraction increments the counted normalization cost by exactly one. -/
@[simp] theorem normalizeSafeSteps_mergeVoidChain_succ (n : Nat) :
    normalizeSafeSteps (mergeVoidChain (n + 1)) =
      Nat.succ (normalizeSafeSteps (mergeVoidChain n)) := by
  have hstep : SafeStep (mergeVoidChain (n + 1)) (mergeVoidChain n) := by
    simpa [mergeVoidChain, deltaFlag_mergeVoidChain n] using
      (SafeStep.R_merge_void_left (mergeVoidChain n) (deltaFlag_mergeVoidChain n))
  rw [normalizeSafeSteps_eq]
  cases hnext : safeStepWitness? (mergeVoidChain (n + 1)) with
  | none =>
      exfalso
      exact (safeStepWitness?_none_no_step hnext _ hstep).elim
  | some w =>
      have hw : SafeStep (mergeVoidChain (n + 1)) w.1 := w.2
      have hEq : w.1 = mergeVoidChain n := safeStep_deterministic hw hstep
      simp [hEq]

/-- Exact cost of certified normalization on the merge spine family. -/
@[simp] theorem normalizeSafeSteps_mergeVoidChain (n : Nat) :
    normalizeSafeSteps (mergeVoidChain n) = n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [normalizeSafeSteps_mergeVoidChain_succ, ih]

/-- Lower-bound corollary phrased in the style needed by the paper. -/
theorem normalizeSafeSteps_mergeVoidChain_lower_bound (n : Nat) :
    n ≤ normalizeSafeSteps (mergeVoidChain n) := by
  simp [normalizeSafeSteps_mergeVoidChain n]

end MetaSN_KO7
