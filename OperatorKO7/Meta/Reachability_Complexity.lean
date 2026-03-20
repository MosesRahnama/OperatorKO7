import OperatorKO7.Meta.Newman_Safe
import OperatorKO7.Meta.SafeRoot_Complexity

/-!
# Guarded Reachability Complexity Envelope

This file packages the existing guarded normalizer-cost results into an explicit
decision-cost statement for reachability to safe normal-form targets.

The decision procedure is the one already used in `reachability_decidable`:
compute `normalizeSafe t` and compare with the target `c`.
We model its cost as:
- the exact counted root-normalization length `normalizeSafeSteps t`, plus
- one final equality check.

This yields a theorem-backed upper/lower envelope without claiming an exact
machine model or complexity class.
-/

open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Cost model for deciding reachability to a safe normal-form target:
run the certified root normalizer, then perform one equality check. -/
@[simp] def reachabilityDecisionCost (t : Trace) (_c : Trace) : Nat :=
  normalizeSafeSteps t + 1

/-- The guarded reachability test is extensionally the normalizer-equality test already
formalized in `reachability_decidable`. -/
theorem reachability_decision_spec {t c : Trace} (hnf : NormalFormSafe c) :
    SafeStepStar t c ↔ normalizeSafe t = c :=
  safeStepStar_to_nf_iff_normalize_eq hnf

/-- The decision cost inherits the explicit certified upper envelope from the root
normalizer. -/
theorem reachabilityDecisionCost_le_complexity_bound (t : Trace) (_c : Trace) :
    reachabilityDecisionCost t _c ≤ complexity_bound (termSize t) + 1 := by
  unfold reachabilityDecisionCost
  have h := normalizeSafeSteps_le_complexity_bound t
  omega

/-- The guarded reachability decision procedure is linearly bounded in the source size. -/
theorem reachabilityDecisionCost_le_linear_termSize (t : Trace) (_c : Trace) :
    reachabilityDecisionCost t _c + 1 ≤ 2 * termSize t := by
  unfold reachabilityDecisionCost
  have h := normalizeSafeSteps_le_linear_termSize t
  omega

/-- The merge-void chain gives a matching linear lower family for the guarded
reachability decision procedure when the target is the safe normal form `void`. -/
theorem reachabilityDecision_has_linear_lower_family (n : Nat) :
    ∃ t c : Trace,
      NormalFormSafe c ∧
      SafeStepStar t c ∧
      reachabilityDecisionCost t c = n + 1 ∧
      n + 1 ≤ reachabilityDecisionCost t c ∧
      reachabilityDecisionCost t c ≤ complexity_bound (termSize t) + 1 := by
  refine ⟨mergeVoidChain n, void, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (norm_nf_safe void)
  · exact mergeVoidChain_star_void n
  · simp [reachabilityDecisionCost, normalizeSafeSteps_mergeVoidChain]
  · simp [reachabilityDecisionCost, normalizeSafeSteps_mergeVoidChain]
  · simpa [reachabilityDecisionCost, normalizeSafeSteps_mergeVoidChain] using
      reachabilityDecisionCost_le_complexity_bound (mergeVoidChain n) void

/-- The merge-void chain also realizes the linear-size runtime envelope exactly up to constants. -/
theorem reachabilityDecision_has_linear_size_family (n : Nat) :
    ∃ t c : Trace,
      NormalFormSafe c ∧
      SafeStepStar t c ∧
      termSize t = 2 * n + 1 ∧
      reachabilityDecisionCost t c = n + 1 ∧
      reachabilityDecisionCost t c + 1 ≤ 2 * termSize t := by
  refine ⟨mergeVoidChain n, void, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (norm_nf_safe void)
  · exact mergeVoidChain_star_void n
  · exact termSize_mergeVoidChain n
  · simp [reachabilityDecisionCost, normalizeSafeSteps_mergeVoidChain]
  · simpa [reachabilityDecisionCost, normalizeSafeSteps_mergeVoidChain] using
      reachabilityDecisionCost_le_linear_termSize (mergeVoidChain n) void

end MetaSN_KO7
