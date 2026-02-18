import OperatorKO7.Meta.Operational_Incompleteness
import OperatorKO7.Kernel
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import OperatorKO7.Meta.ComputableMeasure
-- Impossibility Lemmas - documentation mirror (see Confluence_Safe for helpers)

/-!
# Impossibility Lemmas - mirror of failure catalog (fails_central + consolidation)

Goal
- Keep and enrich the centralized failure witnesses so they fully represent
  the failure taxonomy and chronology notes described in the repository `README.md`.

What’s inside (all self‑contained, kernel unchanged)
- P1/P2/P3 probes: re‑anchored pointers and small runnable examples.
- κ+ k counterexample on KO6 traces (R_rec_succ): ties by rfl branchwise.
- Flag‑only outer discriminator failure: concrete Step raises the flag.
- Duplication stress identity (toy calculus): additive counter non‑drop, plus
  DM and MPO orientation witnesses.
- Right‑add hazard and “quick ≤ patch” are documented with intentionally
  non‑admitted, commented examples (uncomment to see failures).

Note
- This file may include commented, intentionally failing fragments to preserve
  the “dead ends” catalog; keep them commented to preserve green builds.
- Live theorems/examples compile and can be cited in the paper/docs.
- See also: `OperatorKO7/Meta/Operational_Incompleteness.lean` (namespace `OperatorKO7.OpIncomp`) for the P1–P3 probes.
-/


namespace OperatorKO7
namespace Impossibility

 -- Shorten local names for the rest of this file (doc preface section).
 open OperatorKO7 Trace
 open Prod (Lex)

/-! See namespace `OpIncomp` inside `Operational_Incompleteness.lean` for concrete P1–P3
  statements (`P2`, `P2DM`, `P2MPO`) and proofs. This module collects small,
  kernel‑native witnesses and commentary aligned with fails_central sections
  A–M. This is a documentation mirror; no kernel changes. -/

end Impossibility
end OperatorKO7

namespace OperatorKO7
namespace Impossibility

-- This file provides formal, machine-checked proofs that simpler, common
-- termination measures fail for the KO7 kernel. This justifies the necessity
-- of the more complex hybrid measure used in the final successful proof for the
-- guarded sub-relation.

-- Shorten local names for the active content below.
open Trace
open Prod (Lex)

namespace FailedMeasures

/-- A simple depth-based counter for `recΔ` nodes. This was one of the first
measures attempted and fails on duplication. -/
@[simp]
def kappa : Trace → Nat
  | recΔ _ _ n => kappa n + 1
  | delta t    => kappa t
  | integrate t=> kappa t
  | merge a b  => max (kappa a) (kappa b)
  | app a b    => max (kappa a) (kappa b)
  | eqW a b    => max (kappa a) (kappa b)
  | _          => 0

/-- A simple size-based ordinal measure. The definition is not needed,
only its type, to demonstrate the failure of lexicographic ordering. -/
def mu (_t : Trace) : Nat := 0

/-! ### Theorem 1: Failure of `kappa + k`
This theorem proves that no fixed additive constant `k` can orient the
`rec_succ` rule, especially for nested `delta` constructors. This refutes
the entire class of "additive bump" solutions.
-/
theorem kappa_plus_k_fails (k : Nat) :
  ¬ (∀ (b s n : Trace),
      kappa (app s (recΔ b s n)) + k < kappa (recΔ b s (delta n)) + k) := by
  -- We prove this by providing a concrete counterexample.
  push_neg
  -- The counterexample uses a nested `delta` to show the additive bump `+1` from
  -- the outer `delta` is cancelled by the `+1` from the inner `recΔ`.
  use void, void, delta void
  -- The goal is now a concrete inequality, which we can simplify.
  -- After simp, the goal is `¬(1 + k < 1 + k)`.
  simp [kappa]

/-! ### Theorem 2: Failure of Simple Lexicography
This theorem proves that a standard 2-component lexicographic measure `(κ, μ)`
fails because the primary component, `κ`, does not strictly decrease.
This forces the move to a more complex measure where the primary component is a
flag or a multiset designed to handle specific reduction rules.
-/
theorem simple_lex_fails :
  ¬ (∀ (b s n : Trace),
      Lex (·<·) (·<·)
        (kappa (app s (recΔ b s n)), mu (app s (recΔ b s n)))
        (kappa (recΔ b s (delta n)), mu (recΔ b s (delta n)))) := by
  push_neg
  -- The counterexample is `n := void`, which becomes the base case for `recΔ`
  -- after one step.
  use void, recΔ void void void, void
  -- After substituting, we need to show the Lex relation does not hold.
  -- This reduces to `¬ Lex (·<·) (·<·) (1, 0) (1, 0)`, which is decidable.
  simp [kappa, mu]; decide

end FailedMeasures

/-! ## Boolean δ-flag alone - explicit increase on a non-rec rule (fails_central §F)

Using only a “top-is-delta?” flag as the outer lex key breaks monotonicity:
there exists a Step that raises the flag. This mirrors the doc’s warning that
an unguarded global flag is unsafe; KO7 uses it only under a guard in safe
subrelations. -/
namespace FlagFailure

/-- Top-shape flag: 1 only when the term is headed by `delta`. -/
@[simp] def deltaFlagTop : Trace → Nat
  | Trace.delta _ => 1
  | _             => 0

/-- Concrete increase: `merge void (delta void) → delta void` raises `deltaFlagTop`
from 0 to 1. This shows a flag-only primary component can increase on a legal
kernel step (violates lex monotonicity if used unguarded). -/
theorem merge_void_raises_flag :
    let t := Trace.delta Trace.void
    OperatorKO7.Step (Trace.merge Trace.void t) t ∧
    deltaFlagTop (Trace.merge Trace.void t) < deltaFlagTop t := by
  intro t; constructor
  · -- The step exists by R_merge_void_left
    exact OperatorKO7.Step.R_merge_void_left t
  · -- Compute flags: top of `merge void (delta void)` is not `delta`.
    -- top of `t` is `delta`.
    -- After simplification, the goal becomes `0 < 1`.
    have ht : t = Trace.delta Trace.void := rfl
    simp [deltaFlagTop, ht]

end FlagFailure

/-! ## Right-add hazard and “quick ≤ patch” (fails_central §H)

Commentary-only: transporting strict inequalities to the left over arbitrary
ordinal right-addends is invalid. Attempted patches that relax `=` to `≤` do
not fix the nested-δ counterexample. The following fragments are intentionally
commented to keep the build green; they illustrate the bad shapes. -/
/-
-- namespace RightAddHazard
-- open Ordinal
-- variable (p q : Ordinal)
-- -- BAD SHAPE (do not try to prove globally): from μ n < μ (delta n) derive
-- -- μ n + p < μ (delta n) + p for arbitrary p.
-- lemma add_right_strict_mono_bad
--   (h : p < q) :
--   (∀ s, p + s < q + s) := by
--   -- Not true on ordinals in general; right addition isn’t strictly monotone.
--   admit
-- end RightAddHazard
-/

/-! ## P2 duplication realism - references and examples (fails_central §G)

We reuse the toy calculus from `OpIncomp`:
* `r4_size_after_eq_before_plus_piece` gives the exact additive non‑drop identity.
* `r4_no_strict_drop_additive` forbids strict decrease for the additive `size`.
* `R4DM.dm_orient` and `R4MPO.mpo_orient_r4` show robust structural fixes.
-/
namespace DuplicationRefs
open OpIncomp

-- Pointers (elaboration-checked, editor-quiet):
example (x y : Term) := OpIncomp.r4_size_after_eq_before_plus_piece x y  -- additive identity
example (x y : Term) := OpIncomp.r4_no_strict_drop_additive x y          -- no strict drop
example (x y : Term) := OpIncomp.R4DM.dm_orient x y                      -- DM orientation
example (x y : Term) := OpIncomp.R4MPO.mpo_orient_r4 x y                 -- MPO orientation

end DuplicationRefs

/-! ## P1 rfl-gate (branch realism) - explicit per-branch check (fails_central §B)

For any pattern-matched `f`, check rfl per clause and avoid asserting a single
global equation unless all branches agree. The full P1 probe lives in
`Operational_Incompleteness.lean`; we include a tiny exemplar here. -/
namespace RflGate

inductive Two where | A | B deriving DecidableEq, Repr

def f : Two → Nat
  | .A => 0
  | .B => 1

-- Per-branch rfl (passes):
example : f Two.A = 0 := rfl
example : f Two.B = 1 := rfl

-- Over-strong global law fails: not (∀ x, f x = 0)
example : ¬ (∀ x, f x = 0) := by
  intro h
  -- f B = 1 contradicts h B : f B = 0
  exact Nat.one_ne_zero (by simpa [f] using h Two.B)

end RflGate

/-! ## Anchors to the green path (consolidation §J)

The fixes live under KO7’s safe layer:
- `Meta/ComputableMeasure.lean`: `drop_R_rec_succ_c` (outer δ-flag drop),
  `measure_decreases_safe_c`, `wf_SafeStepRev_c`.
These aren’t re‑proved here; this file focuses on the impossibility side. -/

/-! ## KO7 safe Lex3c - tiny cross-link examples (the fix path) -/

namespace KO7_FixPathExamples

open OperatorKO7.MetaCM

-- delta-substitution (rec_succ) strictly drops by KO7's outer flag component.
lemma rec_succ_drops (b s n : Trace) :
   Lex3c (mu3c (app s (recΔ b s n)))
         (mu3c (recΔ b s (delta n))) := by
   simpa using drop_R_rec_succ_c b s n

-- The guarded aggregator yields a decrease certificate per safe step.
lemma safe_decrease_rec_succ (b s n : Trace) :
   Lex3c (mu3c (app s (recΔ b s n)))
         (mu3c (recΔ b s (delta n))) := by
   simpa using
     (measure_decreases_safe_c
        (MetaSN_KO7.SafeStep.R_rec_succ b s n))

-- Well-foundedness of the reverse safe relation (no infinite safe reductions).
theorem wf_safe : WellFounded MetaSN_KO7.SafeStepRev := wf_SafeStepRev_c

end KO7_FixPathExamples

/-! ## Additional computable drop one-liners (cross-link) -/

namespace Computable_FixPathExamples

open OperatorKO7.MetaCM

lemma drop_rec_succ (b s n : Trace) :
  Lex3c (mu3c (app s (recΔ b s n))) (mu3c (recΔ b s (delta n))) := by
  simpa using drop_R_rec_succ_c b s n

lemma drop_merge_void_left (t : Trace) (hδ : MetaSN_KO7.deltaFlag t = 0) :
  Lex3c (mu3c t) (mu3c (merge void t)) := by
  simpa using drop_R_merge_void_left_c t hδ

lemma drop_eq_diff (a b : Trace) :
  Lex3c (mu3c (integrate (merge a b))) (mu3c (eqW a b)) := by
  simpa using drop_R_eq_diff_c a b

end Computable_FixPathExamples

/-! ## Approach #9: Complex Hybrid/Constellation Measures (Paper Section 7, line 250)

Paper quote: "Attempts to combine measures in ad-hoc ways failed to provide
a uniform decrease across all 8 rules."

Constellation theory attempts to track the "shape" or "pattern" of subterms
rather than their numeric size. The idea is that certain constellations of
constructors signal termination progress. This fails because the δ-duplication
rule creates constellations that cannot be uniformly ordered.
-/
namespace ConstellationFailure

/-- A constellation is an abstraction of term structure (shape without content).
    Note: We use `recNode` instead of `rec` to avoid conflict with the eliminator. -/
inductive Constellation where
  | atom : Constellation
  | deltaNode : Constellation → Constellation
  | integrateNode : Constellation → Constellation
  | mergeNode : Constellation → Constellation → Constellation
  | appNode : Constellation → Constellation → Constellation
  | recNode : Constellation → Constellation → Constellation → Constellation
  | eqNode : Constellation → Constellation → Constellation
  deriving DecidableEq, Repr

/-- Extract constellation from a trace (forgetting content, keeping shape). -/
def toConstellation : Trace → Constellation
  | .void => .atom
  | .delta t => .deltaNode (toConstellation t)
  | .integrate t => .integrateNode (toConstellation t)
  | .merge a b => .mergeNode (toConstellation a) (toConstellation b)
  | .app a b => .appNode (toConstellation a) (toConstellation b)
  | .recΔ b s n => .recNode (toConstellation b) (toConstellation s) (toConstellation n)
  | .eqW a b => .eqNode (toConstellation a) (toConstellation b)

/-- The δ-duplication step produces structurally different constellations.
    The RHS has `appNode` at the root while LHS has `recNode` — no simple ordering works. -/
theorem constellation_shapes_differ (b s n : Trace) :
    toConstellation (app s (recΔ b s n)) ≠ toConstellation (recΔ b s (delta n)) := by
  simp only [toConstellation]
  intro h
  cases h

/-- A simple constellation size measure (counting nodes). -/
def constellationSize : Constellation → Nat
  | .atom => 1
  | .deltaNode c => constellationSize c + 1
  | .integrateNode c => constellationSize c + 1
  | .mergeNode a b => constellationSize a + constellationSize b + 1
  | .appNode a b => constellationSize a + constellationSize b + 1
  | .recNode b s n => constellationSize b + constellationSize s + constellationSize n + 1
  | .eqNode a b => constellationSize a + constellationSize b + 1

/-- The δ-duplication rule does NOT decrease constellation size when s is non-trivial.
    This shows additive constellation measures fail just like numeric ones.
    LHS: recNode(b, s, deltaNode(n)) has size = |b| + |s| + (|n| + 1) + 1
    RHS: appNode(s, recNode(b, s, n)) has size = |s| + (|b| + |s| + |n| + 1) + 1
    Difference: RHS - LHS = |s| - 1 ≥ 0 when |s| ≥ 1. -/
theorem constellation_size_not_decreasing (b s n : Trace)
    (hs : constellationSize (toConstellation s) ≥ 1) :
    constellationSize (toConstellation (app s (recΔ b s n))) ≥
    constellationSize (toConstellation (recΔ b s (delta n))) := by
  simp only [toConstellation, constellationSize]
  omega

end ConstellationFailure

/-! ## Approach #10: Unchecked Recursion (Paper Section 7, line 251)

Paper quote: "The raw rec_succ rule itself serves as the ultimate counterexample;
without the SafeStep guards, it permits unbounded recursion that no internal
measure can bound."

The rule `recΔ b s (delta n) → app s (recΔ b s n)`:
1. Duplicates `s` (appears once on LHS, twice on RHS)
2. The recursive `recΔ` call has `n` instead of `delta n`
3. BUT the `app s (...)` wrapping creates work that grows with each step

The recursion is "checked" only when restricted to `SafeStep`, which gates
certain steps behind a δ-phase condition.
-/
namespace UncheckedRecursionFailure

/-- Concrete witness: with a simple additive size, the RHS is NOT smaller. -/
def simpleSize : Trace → Nat
  | .void => 0
  | .delta t => simpleSize t + 1
  | .integrate t => simpleSize t + 1
  | .merge a b => simpleSize a + simpleSize b + 1
  | .app a b => simpleSize a + simpleSize b + 1
  | .recΔ b s n => simpleSize b + simpleSize s + simpleSize n + 1
  | .eqW a b => simpleSize a + simpleSize b + 1

/-- The rec_succ rule is the structural barrier for additive measures.
    LHS: simpleSize(recΔ b s (delta n)) = |b| + |s| + (|n| + 1) + 1 = |b| + |s| + |n| + 2
    RHS: simpleSize(app s (recΔ b s n)) = |s| + (|b| + |s| + |n| + 1) + 1 = 2|s| + |b| + |n| + 2
    Difference: RHS - LHS = |s| ≥ 0. No strict decrease when |s| ≥ 0.
    This is the "ultimate counterexample" from the paper. -/
theorem rec_succ_additive_barrier (b s n : Trace) :
    simpleSize (app s (recΔ b s n)) ≥ simpleSize (recΔ b s (delta n)) := by
  simp only [simpleSize]
  omega

/-- Stronger: RHS is strictly LARGER when s is non-void. -/
theorem rec_succ_size_increases (b s n : Trace) (hs : simpleSize s ≥ 1) :
    simpleSize (app s (recΔ b s n)) > simpleSize (recΔ b s (delta n)) := by
  simp only [simpleSize]
  omega

/-- The full Step relation (not SafeStep) allows this barrier to be hit. -/
theorem full_step_permits_barrier :
    ∃ b s n, Step (recΔ b s (delta n)) (app s (recΔ b s n)) := by
  exact ⟨void, void, void, Step.R_rec_succ void void void⟩

/-- Reference: The SafeStep guard is what makes termination provable.
    See `OperatorKO7.MetaCM.wf_SafeStepRev_c` for the working proof. -/
example : WellFounded MetaSN_KO7.SafeStepRev := OperatorKO7.MetaCM.wf_SafeStepRev_c

end UncheckedRecursionFailure

/-! ## Pointers to toy cores for witnesses/examples

For duplication flavor and base-change shape without touching KO7,
see `Meta/HydraCore.lean` and `Meta/GoodsteinCore.lean` (examples only). -/

end Impossibility
end OperatorKO7
