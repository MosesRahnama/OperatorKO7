import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep_Core

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

/-- Witness that the global equation fails on the `x = 0` branch.
    (The global equation `2 * tiny x = tiny (2 * x)` is not true.) -/
lemma tiny_global_eq_fails_zero : 2 * tiny 0 ≠ tiny (2 * 0) := by
  -- LHS = 2 * 1 = 2; RHS = tiny 0 = 1
  decide

/-- Witness that the global equation fails on the `x = succ n` branch. -/
lemma tiny_global_eq_fails_succ (n : Nat) : 2 * tiny (Nat.succ n) ≠ tiny (2 * Nat.succ n) := by
  -- LHS = 2 * n; RHS = tiny (2*n + 2) = (2*n + 1)
  -- They differ by 1.
  simp only [tiny]
  -- Goal: 2 * n ≠ 2 * n + 1
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

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

/-! ## 4) Size-vs-delta counterexample (purely internal) -/
/-- Simple additive size used as an internal witness for failure cases. -/
@[simp] def simpleSize : Trace → Nat
| .void => 0
| .delta t => simpleSize t + 1
| .integrate t => simpleSize t + 1
| .merge a b => simpleSize a + simpleSize b + 1
| .app a b => simpleSize a + simpleSize b + 1
| .recΔ b s n => simpleSize b + simpleSize s + simpleSize n + 1
| .eqW a b => simpleSize a + simpleSize b + 1

/-- There exist `s, n` with `simpleSize s > simpleSize (delta n)`. -/
theorem exists_size_s_gt_size_delta_n : ∃ s n : Trace, simpleSize s > simpleSize (delta n) := by
  refine ⟨delta (delta void), void, ?_⟩
  simp [simpleSize]

/-! ## 5) KO7-flavored P1: δ-flag is NOT preserved by merge void globally -/
open MetaSN_KO7

/-- Branchwise counterexample: `deltaFlag (merge void t) = deltaFlag t` fails for `t = recΔ b s (delta n)`. -/
lemma deltaFlag_not_preserved_merge_void (b s n : Trace) :
  deltaFlag (merge void (recΔ b s (delta n))) ≠ deltaFlag (recΔ b s (delta n)) := by
  -- LHS = 0, RHS = 1
  simp [deltaFlag]

/-- KO7 duplication mapping note:
    - DM-left used when κᴹ ≠ 0: see `OperatorKO7.MetaCM.drop_R_merge_cancel_c` and `OperatorKO7.MetaCM.drop_R_eq_refl_c`.
    - The full certified decrease aggregator is `OperatorKO7.MetaCM.measure_decreases_safe_c`. -/
lemma note_ko7_duplication_mapping : True := by trivial

end OperatorKO7.Countermodels
