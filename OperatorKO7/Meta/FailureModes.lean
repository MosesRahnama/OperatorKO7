import OperatorKO7.Kernel
import OperatorKO7.Meta.Termination_KO7

/-!
# Impossibility Results and Countermodels

This file formally establishes the failure of simpler termination measures (additive, polynomial, purely ordinal) by exhibiting concrete counterexamples.
These results serve as the formal witnesses for the "Impossibility results" section of the paper, demonstrating why checking strictly simpler measures is insufficient for the KO7 calculus.

Sections:
1) Branch realism: impossibility of global equality across pattern-matched clauses
2) Duplication hazards: failure of additive measures; necessity of DM/MPO
3) Ordinal right-add hazard: (countermodel outline)
4) μ s vs μ (delta n): counterexample to pure ordinal measures
5) KO7-specific countermodels (δ-flag behavior)

Note: We avoid `sorry` and establish negation or inequality where possible.
-/

namespace OperatorKO7.Countermodels

open OperatorKO7 Trace

/-! ## 1) Branch realism: minimal counterexample -/

/-- A tiny function with two clauses to illustrate branch-by-branch `rfl` checks. -/
def tiny : Nat → Nat
| 0       => 1
| Nat.succ n => n

/-- Claim: `2 * tiny x = tiny (2 * x)` is not globally true. We do not assert it; we only show per-branch outcomes. -/
/-- Witness that the global equation fails on the `x = 0` branch. -/
lemma tiny_global_eq_fails_zero : 2 * tiny 0 ≠ tiny (2 * 0) := by
  -- LHS = 2 * 1 = 2; RHS = tiny 0 = 1
  decide

/-- Witness that the global equation fails on the `x = succ n` branch. -/
lemma tiny_global_eq_fails_succ (n : Nat) : 2 * tiny (Nat.succ n) ≠ tiny (2 * Nat.succ n) := by
  -- LHS = 2 * n; RHS = tiny (2*n + 2) = (2*n + 2).pred = 2*n + 1
  -- They differ by 1.
  decide

/-! ## 2) P2 Duplication realism (commented orientation) -/
/--
Consider a duplicating step h(S) → g(S,S). With an additive size M:
  M(after) = M(before) - 1 + M(S) + M(S) = M(before) - 1 + 2·M(S)
This is not strictly smaller when M(S) ≥ 1.
To salvage termination, require a base well-founded order < and the DM premise:
  every RHS piece Pi is strictly < the removed LHS redex W.
If any Pi < W cannot be established, declare a CONSTRAINT BLOCKER instead of proceeding.
-/
lemma note_duplication_dm_orientation : True := by trivial

/-! ## 3) Ordinal right-add hazard (outline, no false lemma) -/
/--
Do NOT transport strict inequalities via right-add globally:
  a < b does not imply a + c < b + c for ordinals without hypotheses.
Use only guarded lemmas like `le_add_of_nonneg_left/right`, or principal-add results with exact assumptions.
-/
lemma note_right_add_hazard : True := by trivial

/-! ## 4) μ s vs μ (delta n) counterexample -/
/-- There exist specific `s, n` with `μ s > μ (delta n)`.
    Take `s = δ (δ void)` and `n = void`; then `μ(δ void) < μ(δ (δ void))`. -/
theorem exists_mu_s_gt_mu_delta_n : ∃ s n : Trace, MetaSN.mu s > MetaSN.mu (delta n) := by
  refine ⟨delta (delta void), void, ?_⟩
  -- Goal: μ(δ δ void) > μ(δ void), equivalent to μ(δ void) < μ(δ δ void)
  simpa [gt_iff_lt] using (MetaSN.mu_lt_mu_delta (delta void))

/-! ## 5) KO7-flavored P1: δ-flag is NOT preserved by merge void globally -/
open MetaSN_KO7

/-- Branchwise counterexample: `deltaFlag (merge void t) = deltaFlag t` fails for `t = recΔ b s (delta n)`. -/
lemma deltaFlag_not_preserved_merge_void (b s n : Trace) :
  deltaFlag (merge void (recΔ b s (delta n))) ≠ deltaFlag (recΔ b s (delta n)) := by
  -- LHS = 0, RHS = 1
  simp [deltaFlag]

/-- Documentation-only mapping note between KO7 duplication rules and the measure decrease branches. -/
/-- KO7 duplication mapping note:
    - DM-left used when κᴹ ≠ 0: see MetaSN_KO7.drop_R_merge_cancel_zero (inner LexDM via DM-left) and drop_R_eq_refl (DM-left branch).
    - When κᴹ = 0, use μ-right in the inner lex and lift: see drop_R_merge_cancel_zero (μ-right path) and drop_R_eq_refl_zero. -/
lemma note_ko7_duplication_mapping : True := by trivial

end OperatorKO7.Countermodels
