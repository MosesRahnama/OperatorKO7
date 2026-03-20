import OperatorKO7.Meta.NormalizeSafe_LowerBound
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal
import OperatorKO7.Meta.SafeStep_Complexity_MW_Root

/-!
# Root-Normalizer Complexity Bounds

This file packages the certified root normalizer `normalizeSafeSteps` into the
same explicit derivation-length language used for `SafeStepCtx`.

What is proved here:
- the counted normalizer length is realized by an exact `SafeStepPow` path
- therefore it is bounded by the computable `ctxFuel` measure
- hence it is bounded by the explicit size-based tower bound already extracted
  for `SafeStepCtx`

Together with the existing exact merge-spine lower bound, this yields a clean,
fully mechanized algorithmic envelope for the certified root normalizer.
-/

open OperatorKO7 Trace
open OperatorKO7.MetaCM
open MetaSN_DM

namespace MetaSN_KO7

/-- The root-side tail measure `τ` is linear in the structural term size. -/
theorem tau_add_two_le_two_mul_termSize (t : Trace) :
    tau t + 2 ≤ 2 * termSize t := by
  induction t with
  | void =>
      simp [tau, termSize]
  | delta t ih =>
      simp [tau, termSize]
      omega
  | integrate t ih =>
      simp [tau, termSize] at ih ⊢
      omega
  | merge a b iha ihb =>
      simp [tau, termSize] at iha ihb ⊢
      omega
  | app a b iha ihb =>
      simp [tau, termSize] at iha ihb ⊢
      omega
  | recΔ b s n ihb ihs ihn =>
      simp [tau, termSize] at ihb ihs ihn ⊢
      omega
  | eqW a b iha ihb =>
      simp [tau, termSize] at iha ihb ⊢
      omega

/-- Any exact-length guarded root reduction is linearly bounded by the source size. -/
theorem safeStepPow_length_le_linear_termSize {t u : Trace} {n : Nat}
    (h : SafeStepPow t n u) :
    n + 2 ≤ 2 * termSize t := by
  have hτ := safeStepPow_length_le_tau h
  have hsize := tau_add_two_le_two_mul_termSize t
  omega

/-- Every exact-length root path lifts to an exact-length context-closed path. -/
theorem safeStepPow_to_ctxPow {a b : Trace} {n : Nat}
    (h : SafeStepPow a n b) : SafeStepCtxPow n a b := by
  induction h with
  | refl t =>
      exact rfl
  | tail hab hbc ih =>
      exact ⟨_, SafeStepCtx.root hab, ih⟩

/-- The counted root normalizer length is realized by an exact-length `SafeStepPow` path. -/
theorem normalizeSafeSteps_realized :
    ∀ t : Trace, ∃ u : Trace, SafeStepPow t (normalizeSafeSteps t) u := by
  refine WellFounded.fix wf_Rμ3
    (C := fun t => ∃ u : Trace, SafeStepPow t (normalizeSafeSteps t) u) ?_
  intro t rec
  rw [normalizeSafeSteps_eq]
  cases hnext : safeStepWitness? t with
  | none =>
      exact ⟨t, SafeStepPow.refl t⟩
  | some w =>
      have hdrop : Rμ3 w.1 t := measure_decreases_safe_c w.2
      rcases rec w.1 hdrop with ⟨u, hu⟩
      exact ⟨u, by simpa [hnext, Nat.add_comm] using SafeStepPow.tail w.2 hu⟩

/-- The certified root normalizer length is bounded by the computable `ctxFuel`
measure because root safe steps embed into `SafeStepCtx`. -/
theorem normalizeSafeSteps_le_ctxFuel (t : Trace) :
    normalizeSafeSteps t ≤ ctxFuel t := by
  rcases normalizeSafeSteps_realized t with ⟨u, hu⟩
  exact safeStepCtx_length_le_ctxFuel t u (normalizeSafeSteps t) (safeStepPow_to_ctxPow hu)

/-- The certified root normalizer inherits the explicit size-based tower bound. -/
theorem normalizeSafeSteps_le_complexity_bound (t : Trace) :
    normalizeSafeSteps t ≤ complexity_bound (termSize t) := by
  exact le_trans (normalizeSafeSteps_le_ctxFuel t) (ctxFuel_le_towerBound t)

/-- The certified root normalizer also inherits the notation-level MW root bound. -/
theorem normalizeSafeSteps_le_mwRootBound (t : Trace) :
    normalizeSafeSteps t ≤ mwRootBound t := by
  rcases normalizeSafeSteps_realized t with ⟨u, hu⟩
  exact safeStepPow_length_le_mwRootBound hu

/-- The certified root normalizer is linearly bounded by structural term size. -/
theorem normalizeSafeSteps_le_linear_termSize (t : Trace) :
    normalizeSafeSteps t + 2 ≤ 2 * termSize t := by
  rcases normalizeSafeSteps_realized t with ⟨u, hu⟩
  exact safeStepPow_length_le_linear_termSize hu

/-- Exact structural size of the merge-spine lower-bound family. -/
@[simp] theorem termSize_mergeVoidChain (n : Nat) :
    termSize (mergeVoidChain n) = 2 * n + 1 := by
  induction n with
  | zero =>
      simp [mergeVoidChain, termSize]
  | succ n ih =>
      simp [mergeVoidChain, termSize, ih]
      omega

/-- The merge-void chain gives the matching exact lower-bound family already proved in
`NormalizeSafe_LowerBound.lean`, restated here with the new root upper bound. -/
theorem normalizeSafeSteps_has_linear_lower_family (n : Nat) :
    ∃ t : Trace,
      normalizeSafeSteps t = n ∧
      n ≤ normalizeSafeSteps t ∧
      normalizeSafeSteps t ≤ complexity_bound (termSize t) := by
  refine ⟨mergeVoidChain n, ?_, ?_, ?_⟩
  · simp
  · exact normalizeSafeSteps_mergeVoidChain_lower_bound n
  · simpa [normalizeSafeSteps_mergeVoidChain n] using
      normalizeSafeSteps_le_complexity_bound (mergeVoidChain n)

/-- The merge-spine family realizes linear guarded root normalization in term size. -/
theorem normalizeSafeSteps_has_linear_size_family (n : Nat) :
    ∃ t : Trace,
      termSize t = 2 * n + 1 ∧
      normalizeSafeSteps t = n := by
  refine ⟨mergeVoidChain n, termSize_mergeVoidChain n, normalizeSafeSteps_mergeVoidChain n⟩

end MetaSN_KO7
