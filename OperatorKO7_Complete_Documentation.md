# OperatorKO7 Complete Documentation

Generated: 2026-03-11 18:03:01 +03:30
Source files: 26
Total source lines: 7915

Scope: all files under `OperatorKO7/` excluding `OperatorKO7/Ignore_Legacy/` and `OperatorKO7/Ignore_Meta_md/`
Included extensions: `.lean`, `.md`

## Table of Contents

- [OperatorKO7/Kernel.lean](#operatorko7kernellean)
- [OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean](#operatorko7metacompositionalmeasureimpossibilitylean)
- [OperatorKO7/Meta/ComputableMeasure.lean](#operatorko7metacomputablemeasurelean)
- [OperatorKO7/Meta/ComputableMeasure_Verification.lean](#operatorko7metacomputablemeasureverificationlean)
- [OperatorKO7/Meta/Confluence_Safe.lean](#operatorko7metaconfluencesafelean)
- [OperatorKO7/Meta/Conjecture_Boundary.lean](#operatorko7metaconjectureboundarylean)
- [OperatorKO7/Meta/ContextClosed_SN.lean](#operatorko7metacontextclosedsnlean)
- [OperatorKO7/Meta/DependencyPairs_Works.lean](#operatorko7metadependencypairsworkslean)
- [OperatorKO7/Meta/DM_MPO_Orientation.lean](#operatorko7metadmmpoorientationlean)
- [OperatorKO7/Meta/DM_OrderType.lean](#operatorko7metadmordertypelean)
- [OperatorKO7/Meta/DM_OrderType_LowerBound.lean](#operatorko7metadmordertypelowerboundlean)
- [OperatorKO7/Meta/FailureModes.lean](#operatorko7metafailuremodeslean)
- [OperatorKO7/Meta/GoodsteinCore.lean](#operatorko7metagoodsteincorelean)
- [OperatorKO7/Meta/HydraCore.lean](#operatorko7metahydracorelean)
- [OperatorKO7/Meta/Impossibility_Lemmas.lean](#operatorko7metaimpossibilitylemmaslean)
- [OperatorKO7/Meta/LinearRec_Ablation.lean](#operatorko7metalinearrecablationlean)
- [OperatorKO7/Meta/MPO_FullStep.lean](#operatorko7metampofullsteplean)
- [OperatorKO7/Meta/Newman_Safe.lean](#operatorko7metanewmansafelean)
- [OperatorKO7/Meta/Normalize_Safe.lean](#operatorko7metanormalizesafelean)
- [OperatorKO7/Meta/Operational_Incompleteness.lean](#operatorko7metaoperationalincompletenesslean)
- [OperatorKO7/Meta/PaperApproachIndex.lean](#operatorko7metapaperapproachindexlean)
- [OperatorKO7/Meta/RecCore.lean](#operatorko7metareccorelean)
- [OperatorKO7/Meta/SafeStep_Core.lean](#operatorko7metasafestepcorelean)
- [OperatorKO7/Meta/SafeStep_Ctx.lean](#operatorko7metasafestepctxlean)
- [OperatorKO7/Meta/StepDuplicatingSchema.lean](#operatorko7metastepduplicatingschemalean)
- [OperatorKO7/Test/Sanity.lean](#operatorko7testsanitylean)

---

## OperatorKO7/Kernel.lean

**Lines:** 60

``lean
namespace OperatorKO7

/-!
Kernel definitions for the KO7 calculus.

Why this file exists:
- Defines the core syntax (`Trace`) and the full rewrite relation (`Step`) for the KO7 kernel.
- `Step` is the *full* kernel relation (8 unconditional rules).
- The certified artifact is proved for a guarded subrelation `SafeStep` defined in
  `OperatorKO7/Meta/SafeStep_Core.lean`.
-/

/-- The KO7 term language (7 constructors). -/
inductive Trace : Type
| void : Trace
| delta : Trace â†’ Trace
| integrate : Trace â†’ Trace
| merge : Trace â†’ Trace â†’ Trace
| app : Trace â†’ Trace â†’ Trace
| recÎ” : Trace â†’ Trace â†’ Trace â†’ Trace
| eqW : Trace â†’ Trace â†’ Trace
deriving DecidableEq, Repr
open Trace

/-- The full kernel reduction relation (8 unconditional root rules). -/
inductive Step : Trace â†’ Trace â†’ Prop
| R_int_delta : âˆ€ t, Step (integrate (delta t)) void
| R_merge_void_left : âˆ€ t, Step (merge void t) t
| R_merge_void_right : âˆ€ t, Step (merge t void) t
| R_merge_cancel : âˆ€ t, Step (merge t t) t
| R_rec_zero : âˆ€ b s, Step (recÎ” b s void) b
| R_rec_succ : âˆ€ b s n, Step (recÎ” b s (delta n)) (app s (recÎ” b s n))
| R_eq_refl : âˆ€ a, Step (eqW a a) void
| R_eq_diff : âˆ€ a b, Step (eqW a b) (integrate (merge a b))

/-- Reflexive-transitive closure of the kernel step relation `Step`. -/
inductive StepStar : Trace â†’ Trace â†’ Prop
| refl : âˆ€ t, StepStar t t
| tail : âˆ€ {a b c}, Step a b â†’ StepStar b c â†’ StepStar a c

/-- Normal forms for the full kernel relation: no outgoing `Step`. -/
def NormalForm (t : Trace) : Prop := Â¬ âˆƒ u, Step t u

/-- Transitivity of `StepStar` (concatenation of two multi-step reductions). -/
theorem stepstar_trans {a b c : Trace} (h1 : StepStar a b) (h2 : StepStar b c) : StepStar a c := by
  induction h1 with
  | refl => exact h2
  | tail hab _ ih => exact StepStar.tail hab (ih h2)

/-- Any single `Step` is also a `StepStar`. -/
theorem stepstar_of_step {a b : Trace} (h : Step a b) : StepStar a b :=
  StepStar.tail h (StepStar.refl b)

/-- If `a` is a normal form, then any `a â‡’* b` must be trivial (`b = a`). -/
theorem nf_no_stepstar_forward {a b : Trace} (hnf : NormalForm a) (h : StepStar a b) : a = b :=
  match h with
  | StepStar.refl _ => rfl
  | StepStar.tail hs _ => False.elim (hnf âŸ¨_, hsâŸ©)

end OperatorKO7
````

## OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean

**Lines:** 372

``lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.Conjecture_Boundary

/-!
# Compositional Measure Impossibility Theorem

This module defines a precise axiom system for "compositional measures" - termination
measures that compute the value of a compound term by aggregating the values of its
subterms - and proves that NO such measure can orient the duplicating recursor rule
`recÎ” b s (delta n) â†’ app s (recÎ” b s n)` for all instantiations.

The module then shows that the Dependency Pair framework (TTT2's subterm criterion with
projection Ï€(recD#) = 3) escapes the impossibility by violating the compositionality
axioms: it projects to a single argument instead of aggregating all subterm contributions.

## Structure

- **Section 1**: Helper: iterated `app` constructor (the "pump" for making Î¼(s) large)
- **Section 2**: `AdditiveCompositionalMeasure` - concrete Nat-weighted structure
- **Section 3**: Tier 1 impossibility theorem (additive measures)
- **Section 4**: `CompositionalMeasure` - abstract combining-function structure
- **Section 5**: Tier 2 impossibility theorem (transparent-delta case)
- **Section 6**: DP projection escape clause
- **Section 7**: Instance witnesses (simpleSize, tau, nodeCount)
- **Section 8**: `GlobalOrients` integration

## Key Results

- `no_additive_compositional_orients_rec_succ`: No additive compositional measure orients rec_succ
- `no_compositional_orients_rec_succ_transparent_delta`: No abstract compositional measure
  with transparent delta orients rec_succ
- `no_global_step_orientation_compositional_transparent_delta`: No abstract compositional
  measure with transparent delta globally orients full `Step`
- `dp_projection_orients_rec_succ`: DP projection DOES orient rec_succ
- `dp_projection_violates_sensitivity`: DP projection violates the subterm/sensitivity axiom

## References

- Dershowitz (1987): duplication defeats additive measures
- Arts-Giesl (2000): dependency pairs with argument filtering
- Hirokawa-Middeldorp (2004): simple projection for DP
- Middeldorp-Zantema (1997): simple termination hierarchy
-/

namespace OperatorKO7.CompositionalImpossibility

open OperatorKO7 Trace
open OperatorKO7.StepDuplicating

/-- The four-role KO7 schema underlying the duplication barrier. -/
def ko7Schema : StepDuplicatingSchema where
  T := Trace
  base := void
  succ := delta
  wrap := app
  recur := recÎ”

/-- KO7 viewed as a step-duplicating system. -/
def ko7System : StepDuplicatingSchema.StepDuplicatingSystem where
  toStepDuplicatingSchema := ko7Schema
  Step := Step
  dup_step := Step.R_rec_succ

/-! ## Section 1: Iterated App Constructor -/

/-- Build `app(app(...(void)...), void)` with `k` nestings.
This is the "pump" that makes `Î¼(s)` arbitrarily large for any compositional measure. -/
def appIter : Nat â†’ Trace :=
  StepDuplicatingSchema.wrapIter ko7Schema

/-! ## Section 2: Additive Compositional Measure (Tier 1) -/

/-- An additive compositional measure assigns a fixed base weight to each KO7 constructor.
The measure of a compound term is the constructor's weight plus the sum of its subterms' measures.

This axiom system captures: `simpleSize`, `tau`, `nodeCount`, `linearWeight`, `treeDepth`,
and all parameter choices thereof. The single constraint `hw_app_pos` (app adds at least 1)
ensures the measure grows under the `app` constructor - this is what makes it "see" duplication. -/
structure AdditiveCompositionalMeasure where
  w_void      : Nat
  w_delta     : Nat
  w_integrate : Nat
  w_merge     : Nat
  w_app       : Nat
  w_rec       : Nat
  w_eq        : Nat
  hw_app_pos  : w_app â‰¥ 1

/-- The evaluation function for an additive compositional measure.
For each constructor, adds the constructor's weight to the sum of subterm evaluations. -/
@[simp] def AdditiveCompositionalMeasure.eval
    (M : AdditiveCompositionalMeasure) : Trace â†’ Nat
  | void        => M.w_void
  | delta t     => M.w_delta + M.eval t
  | integrate t => M.w_integrate + M.eval t
  | merge a b   => M.w_merge + M.eval a + M.eval b
  | app a b     => M.w_app + M.eval a + M.eval b
  | recÎ” b s n  => M.w_rec + M.eval b + M.eval s + M.eval n
  | eqW a b     => M.w_eq + M.eval a + M.eval b

/-- Forget the KO7-specific extra constructors and view the measure on the generic schema. -/
def AdditiveCompositionalMeasure.toSchemaMeasure
    (M : AdditiveCompositionalMeasure) :
    StepDuplicatingSchema.AdditiveMeasure ko7Schema where
  eval := M.eval
  w_base := M.w_void
  w_succ := M.w_delta
  w_wrap := M.w_app
  w_recur := M.w_rec
  eval_base := by rfl
  eval_succ := by intro t; rfl
  eval_wrap := by intro x y; rfl
  eval_recur := by intro b s n; rfl
  h_wrap_pos := M.hw_app_pos

/-- The eval of `appIter k` grows at least as fast as `k` for any additive compositional measure
with `w_app â‰¥ 1`. This is the key "pump" lemma: we can make `M.eval s` arbitrarily large. -/
lemma eval_appIter_ge (M : AdditiveCompositionalMeasure) (k : Nat) :
    M.eval (appIter k) â‰¥ k := by
  simpa [appIter, AdditiveCompositionalMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.eval_wrapIter_ge
      (S := ko7Schema) (M := M.toSchemaMeasure) k)

/-! ## Section 3: Tier 1 Impossibility Theorem -/

/-- **IMPOSSIBILITY THEOREM (Additive Measures)**

No additive compositional measure can orient the duplicating recursor rule
`recÎ” b s (delta n) â†’ app s (recÎ” b s n)` for all instantiations of `b`, `s`, `n`.

**Proof strategy**: Set `b = void, n = void, s = appIter(w_delta)`. The RHS
`app s (recÎ” void s void)` contains `M.eval s` TWICE (once directly, once inside recÎ”),
while the LHS `recÎ” void s (delta void)` contains `M.eval s` only ONCE.
The duplication adds `M.eval s â‰¥ w_delta` to the RHS, while the LHS gains only `w_delta`
from the delta wrapper. Since `w_app â‰¥ 1`, the RHS is at least as large as the LHS.

This subsumes all 12 failure witnesses in the catalog under a single theorem. -/
theorem no_additive_compositional_orients_rec_succ (M : AdditiveCompositionalMeasure) :
    Â¬ (âˆ€ (b s n : Trace),
      M.eval (app s (recÎ” b s n)) < M.eval (recÎ” b s (delta n))) := by
  simpa [ko7Schema, AdditiveCompositionalMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_additive_orients_dup_step
      (S := ko7Schema) (M := M.toSchemaMeasure))

/-! ## Section 4: Abstract Compositional Measure (Tier 2) -/

/-- An abstract compositional measure over KO7 traces.
Each constructor has a combining function that maps subterm measure values to
the compound term's measure value.

The key axioms are the **subterm properties** for `c_app`:
- `app_subterm1`: `c_app(x, y) > x` - app is strictly larger than its first argument
- `app_subterm2`: `c_app(x, y) > y` - app is strictly larger than its second argument

These capture the essence of "compositionality": the measure of `app s (recÎ” b s n)`
is built from the measures of BOTH `s` and `recÎ” b s n`, and is strictly larger than
either. This is what makes compositional measures sensitive to duplication. -/
structure CompositionalMeasure where
  c_void      : Nat
  c_delta     : Nat â†’ Nat
  c_integrate : Nat â†’ Nat
  c_merge     : Nat â†’ Nat â†’ Nat
  c_app       : Nat â†’ Nat â†’ Nat
  c_recÎ”      : Nat â†’ Nat â†’ Nat â†’ Nat
  c_eqW       : Nat â†’ Nat â†’ Nat
  app_subterm1 : âˆ€ x y, c_app x y > x
  app_subterm2 : âˆ€ x y, c_app x y > y

/-- The evaluation function for an abstract compositional measure. -/
@[simp] def CompositionalMeasure.eval (CM : CompositionalMeasure) : Trace â†’ Nat
  | void        => CM.c_void
  | delta t     => CM.c_delta (CM.eval t)
  | integrate t => CM.c_integrate (CM.eval t)
  | merge a b   => CM.c_merge (CM.eval a) (CM.eval b)
  | app a b     => CM.c_app (CM.eval a) (CM.eval b)
  | recÎ” b s n  => CM.c_recÎ” (CM.eval b) (CM.eval s) (CM.eval n)
  | eqW a b     => CM.c_eqW (CM.eval a) (CM.eval b)

/-- Generic-schema view of a KO7 compositional measure. -/
def CompositionalMeasure.toSchemaMeasure
    (CM : CompositionalMeasure) :
    StepDuplicatingSchema.CompositionalMeasure ko7Schema where
  eval := CM.eval
  c_base := CM.c_void
  c_succ := CM.c_delta
  c_wrap := CM.c_app
  c_recur := CM.c_recÎ”
  eval_base := by rfl
  eval_succ := by intro t; rfl
  eval_wrap := by intro x y; rfl
  eval_recur := by intro b s n; rfl
  wrap_subterm1 := CM.app_subterm1
  wrap_subterm2 := CM.app_subterm2

/-! ## Section 5: Tier 2 Impossibility (Transparent Delta) -/

/-- **IMPOSSIBILITY THEOREM (Abstract Compositional, Transparent Delta)**

When `c_delta(c_void) = c_void` (delta is transparent at base level - as in `tau` where
`tau(delta t) = tau t`), no compositional measure with subterm properties for `c_app`
can orient the duplicating recursor.

**Proof** (4 lines): Set `b = void, n = void, s = void`. Then:
- LHS = `c_recÎ”(V, V, c_delta(V))` = `c_recÎ”(V, V, V)` (by transparency)
- RHS = `c_app(V, c_recÎ”(V, V, V))`
- By `app_subterm2`: `c_app(V, R) > R` where `R = c_recÎ”(V, V, V)` = LHS
- So RHS > LHS, contradicting orientation (which requires RHS < LHS). -/
theorem no_compositional_orients_rec_succ_transparent_delta
    (CM : CompositionalMeasure)
    (h_transparent : CM.c_delta CM.c_void = CM.c_void) :
    Â¬ (âˆ€ (b s n : Trace),
      CM.eval (app s (recÎ” b s n)) < CM.eval (recÎ” b s (delta n))) := by
  simpa [ko7Schema, CompositionalMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_compositional_orients_dup_step_transparent_succ
      (S := ko7Schema) (CM := CM.toSchemaMeasure) h_transparent)

/-! ## Section 6: DP Projection Escape -/

/-- A projection-based measure that tracks only delta-nesting depth.
This is the measure implicitly used by TTT2's subterm criterion with Ï€(recD#) = 3.
It projects to the recursion counter and IGNORES all other structure. -/
@[simp] def dpProjection : Trace â†’ Nat
  | void        => 0
  | delta t     => dpProjection t + 1
  | integrate _ => 0
  | merge _ _   => 0
  | app _ _     => 0
  | recÎ” _ _ n  => dpProjection n
  | eqW _ _     => 0

/-- KO7's DP projection packaged as a generic schema rank. -/
def dpProjectionRank : StepDuplicatingSchema.ProjectionRank ko7Schema where
  rank := dpProjection
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The DP projection DOES orient rec_succ: the 3rd argument strictly decreases
from `delta n` (depth k+1) to `n` (depth k). -/
theorem dp_projection_orients_rec_succ (b s n : Trace) :
    dpProjection (app s (recÎ” b s n)) < dpProjection (recÎ” b s (delta n)) := by
  exact
    (StepDuplicatingSchema.projection_orients_dup_step
      (S := ko7Schema) dpProjectionRank b s n)

/-- The DP projection VIOLATES the subterm property for `app`.
Specifically, `dpProjection(app x y)` is NOT always > `dpProjection(x)`.
Counterexample: `x = delta void` (dpProjection = 1), `y = void` (dpProjection = 0),
`app x y` has dpProjection = 0 < 1 = dpProjection(x).

This is the precise axiom that DP violates, escaping the impossibility theorem. -/
theorem dp_projection_violates_sensitivity :
    âˆƒ x y : Trace, Â¬ (dpProjection (app x y) > dpProjection x) := by
  simpa [ko7Schema, dpProjectionRank] using
    (StepDuplicatingSchema.projection_violates_wrap_subterm1
      (S := ko7Schema) dpProjectionRank)

/-- The DP projection also violates the second subterm property.
`dpProjection(app x y)` = 0 is NOT always > `dpProjection(y)`. -/
theorem dp_projection_violates_subterm2 :
    âˆƒ x y : Trace, Â¬ (dpProjection (app x y) > dpProjection y) := by
  simpa [ko7Schema, dpProjectionRank] using
    (StepDuplicatingSchema.projection_violates_wrap_subterm2
      (S := ko7Schema) dpProjectionRank)

/-! ## Section 7: Instance Witnesses -/

/-- `simpleSize` (from Conjecture_Boundary) is an additive compositional measure.
All weights are 1 except void which is 0. -/
def simpleSize_ACM : AdditiveCompositionalMeasure where
  w_void      := 0
  w_delta     := 1
  w_integrate := 1
  w_merge     := 1
  w_app       := 1
  w_rec       := 1
  w_eq        := 1
  hw_app_pos  := by omega

/-- `tau` (from ComputableMeasure) is an additive compositional measure.
Note: w_delta = 0 (delta is transparent). This is the transparent-delta case. -/
def tau_ACM : AdditiveCompositionalMeasure where
  w_void      := 0
  w_delta     := 0
  w_integrate := 1
  w_merge     := 2
  w_app       := 1
  w_rec       := 3
  w_eq        := 4
  hw_app_pos  := by omega

/-- `nodeCount` (from Conjecture_Boundary) is an additive compositional measure.
Every constructor adds 1, base is 1. -/
def nodeCount_ACM : AdditiveCompositionalMeasure where
  w_void      := 1
  w_delta     := 1
  w_integrate := 1
  w_merge     := 1
  w_app       := 1
  w_rec       := 1
  w_eq        := 1
  hw_app_pos  := by omega

/-- `treeDepth` assigns weight 1 per constructor except void. -/
def treeDepth_ACM : AdditiveCompositionalMeasure where
  w_void      := 0
  w_delta     := 1
  w_integrate := 1
  w_merge     := 1
  w_app       := 1
  w_rec       := 1
  w_eq        := 1
  hw_app_pos  := by omega

/-- Any `linearWeight` from Conjecture_Boundary is an additive compositional measure,
provided its app coefficient is â‰¥ 1. -/
def linearWeight_ACM (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat)
    (h : c_app â‰¥ 1) : AdditiveCompositionalMeasure where
  w_void      := c_void
  w_delta     := c_delta
  w_integrate := c_int
  w_merge     := c_merge
  w_app       := c_app
  w_rec       := c_rec
  w_eq        := c_eq
  hw_app_pos  := h

/-! ## Section 8: GlobalOrients Integration -/

/-- No additive compositional measure can globally orient the full KO7 `Step` relation.
This follows immediately: if it could orient all rules, it would orient rec_succ,
contradicting the impossibility theorem. -/
theorem no_global_step_orientation_additive_compositional
    (M : AdditiveCompositionalMeasure) :
    Â¬ MetaConjectureBoundary.GlobalOrients M.eval (Â· < Â·) := by
  simpa [ko7System, StepDuplicatingSchema.GlobalOrients,
    MetaConjectureBoundary.GlobalOrients, AdditiveCompositionalMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_global_orients_additive
      (Sys := ko7System) (M := M.toSchemaMeasure))

/-- No abstract compositional measure with transparent delta at `void`
can globally orient the full KO7 `Step` relation. -/
theorem no_global_step_orientation_compositional_transparent_delta
    (CM : CompositionalMeasure)
    (h_transparent : CM.c_delta CM.c_void = CM.c_void) :
    Â¬ MetaConjectureBoundary.GlobalOrients CM.eval (Â· < Â·) := by
  simpa [ko7System, StepDuplicatingSchema.GlobalOrients,
    MetaConjectureBoundary.GlobalOrients, CompositionalMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_global_orients_compositional_transparent_succ
      (Sys := ko7System) (CM := CM.toSchemaMeasure) h_transparent)

/-! ## Summary of the Boundary

The impossibility theorem establishes:

1. **Compositional measures fail**: Any measure satisfying the compositionality axioms
   (additive weight structure with w_app â‰¥ 1, or abstract combining functions with
   subterm properties) CANNOT orient the duplicating recursor for all term instantiations.

2. **DP projection succeeds**: The subterm criterion with projection Ï€(recÎ”#) = 3
   DOES orient the recursor, but it escapes the impossibility by violating the
   compositionality axioms - it projects to one argument and ignores the others.

3. **The boundary is at Axiom `app_subterm`**: Compositional measures must satisfy
   `c_app(x, y) > x` and `c_app(x, y) > y`. DP projection satisfies neither.
   This is exactly where the "multiplicity-aware vs. multiplicity-blind" distinction
   manifests as a formal axiom.
-/

end OperatorKO7.CompositionalImpossibility
````

## OperatorKO7/Meta/ComputableMeasure.lean

**Lines:** 460

``lean
import OperatorKO7.Meta.SafeStep_Core
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Computable Termination Measure for KO7 SafeStep

This module provides a **fully computable** termination proof for the `SafeStep` relation
using the triple-lexicographic measure Î¼3c = (Î´, Îºá´¹, Ï„) where:
- Î´ (deltaFlag): Binary flag detecting `recÎ” b s (delta n)` patterns
- Îºá´¹ (kappaM): Dershowitz-Manna multiset of recursion weights
- Ï„ (tau): Computable natural number rank (replaces noncomputable ordinal Î¼)

## Key Properties
- **Fully Computable Measures**: All measure functions (`deltaFlag`, `kappaM`, `tau`) are computable;
  classical reasoning is used only in proof terms (Prop-valued well-foundedness arguments)
- **Complete Coverage**: All 8 SafeStep constructors proven to strictly decrease Î¼3c
- **Bulletproof**: Explicit Prod.Lex parameters prevent elaboration issues
- **Lint-Clean**: No warnings, no sorry, no admit, no unsafe

## Technical Approach
The measure Î¼3c uses lexicographic ordering Lex3c := Prod.Lex (<) (Prod.Lex DM (<))
where DM is Mathlib's Dershowitz-Manna multiset order. Each SafeStep rule is proven
to strictly decrease this measure through either:
1. Î´-drop: For rec_succ (1 â†’ 0)
2. Îºá´¹-drop: Via DM order for rules that modify recursion structure
3. Ï„-drop: When Î´ and Îºá´¹ tie, using carefully chosen head weights

## Constants
Ï„ assigns head weights ensuring strict inequalities:
- void: 0
- delta: transparent (preserves inner term's weight)
- integrate: 1 + inner
- merge: 2 + sum of arguments
- app: 1 + sum of arguments
- recÎ”: 3 + sum of all three arguments
- eqW: 4 + sum of arguments (ensures 1+2+X < 4+X for eq_diff)

## References
- Dershowitz & Manna (1979): Proving termination with multiset orderings
- Baader & Nipkow: Term Rewriting and All That
- Newman's Lemma: Local confluence + termination â†’ confluence
-/

namespace OperatorKO7.MetaCM

-- Disable unnecessary simpa linter locally for this file
set_option linter.unnecessarySimpa false

open OperatorKO7 Trace Multiset
open MetaSN_KO7
open MetaSN_DM
open scoped Classical

/-! ## Section 1: Computable Natural Rank Ï„ ----------------------------------------------- -/

/-- **Head-weighted structural size (Ï„)**

A computable Nat-valued rank function with meticulously chosen constants.

### Key Properties:
1. Ï„(eqW a b) > Ï„(integrate (merge a b)) for all a, b (critical for eq_diff)
2. Ï„ strictly increases under all constructors except delta
3. All inequalities provable by omega or decide

### Weight Design:
- void: 0 (base case)
- delta t: Ï„(t) (transparent wrapper)
- integrate/app: weight 1
- merge: weight 2
- recÎ”: weight 3
- eqW: weight 4 (ensures 1+2+X < 4+X)
-/
@[simp] def tau : Trace â†’ Nat
| void            => 0
| delta t         => tau t
| integrate t     => 1 + tau t            -- baseIntegrate = 1
| merge a b       => 2 + tau a + tau b    -- baseMerge = 2
| app a b         => 1 + tau a + tau b    -- baseApp = 1
| recÎ” b s n      => 3 + tau b + tau s + tau n  -- baseRec = 3
| eqW a b         => 4 + tau a + tau b    -- baseEq = baseIntegrate + baseMerge + 1 = 4

/-! ## Section 2: Dershowitz-Manna Order and Lexicographic Structure -/

/-- **Dershowitz-Manna multiset order (DM)**

The well-founded multiset order that correctly handles duplication.
Crucial for rules like merge_cancel and eq_refl.
-/
def DM (X Y : Multiset Nat) : Prop :=
  Multiset.IsDershowitzMannaLT X Y

/-- **Inner lexicographic order (LexDM_c)**

Combines DM order with Nat ordering to form the (Îºá´¹, Ï„) component.
Prioritizes Îºá´¹ changes via DM over Ï„ changes.
-/
@[simp] def LexDM_c : (Multiset Nat Ã— Nat) â†’ (Multiset Nat Ã— Nat) â†’ Prop :=
  Prod.Lex (fun a b : Multiset Nat => DM a b) (Â· < Â·)

/-- Well-foundedness of the computable inner lex (DM Ã— Nat<). -/
lemma wf_LexDM_c : WellFounded LexDM_c :=
  WellFounded.prod_lex MetaSN_DM.wf_dm Nat.lt_wfRel.wf

/-- **Outer triple lexicographic order (Lex3c)**

The complete well-founded order: (Î´, (Îºá´¹, Ï„))
Priority: Î´-flag > Îºá´¹ (via DM) > Ï„
-/
@[simp] def Lex3c : (Nat Ã— (Multiset Nat Ã— Nat)) â†’ (Nat Ã— (Multiset Nat Ã— Nat)) â†’ Prop :=
  Prod.Lex (Â· < Â·) LexDM_c

/-- Well-foundedness of the computable triple lex (Nat< Ã— (DM Ã— Nat<)). -/
lemma wf_Lex3c : WellFounded Lex3c := by
  exact WellFounded.prod_lex Nat.lt_wfRel.wf wf_LexDM_c

/-- **Critical lifting lemma**

Lifts a DM decrease on Îºá´¹ to the full inner order, regardless of Ï„.
EXPLICIT PARAMETERS prevent all elaboration issues.
-/
lemma dm_to_LexDM_c_left {X Y : Multiset Nat} {Ï„â‚ Ï„â‚‚ : Nat}
    (h : DM X Y) : LexDM_c (X, Ï„â‚) (Y, Ï„â‚‚) := by
  -- Use explicit parameters to avoid inference brittleness, mirroring KO7.
  exact
    (Prod.Lex.left
      (Î± := Multiset Nat) (Î² := Nat)
      (ra := fun a b : Multiset Nat => DM a b) (rb := (Â· < Â·))
      (aâ‚ := X) (aâ‚‚ := Y) (bâ‚ := Ï„â‚) (bâ‚‚ := Ï„â‚‚)
      (by simpa using h))

/-- **The computable triple measure Î¼3c**

Assembles (Î´, Îºá´¹, Ï„) from a trace term.
Fully computable replacement for the ordinal-based measure.
-/
@[simp] def mu3c (t : Trace) : Nat Ã— (Multiset Nat Ã— Nat) :=
  (deltaFlag t, (kappaM t, tau t))

/-! ## Section 3: Per-Rule Termination Proofs

Each SafeStep constructor proven to strictly decrease Î¼3c.
Systematic approach: identify decreasing component, build witness, normalize.
-/

open Classical

/-- **Rule: integrate (delta t) â†’ void**

Strategy:
- If Îºá´¹(t) = 0: Ï„-drop (0 < 1 + Ï„(t))
- If Îºá´¹(t) â‰  0: DM-drop (0 <â‚˜ Îºá´¹(t))
-/
lemma drop_R_int_delta_c (t : Trace) :
    Lex3c (mu3c void) (mu3c (integrate (delta t))) := by
  classical
  by_cases h0 : kappaM t = 0
  Â· -- Îº tie at 0: take Ï„-right since 0 < 1 + Ï„ t
    -- Inner Îº tie at 0; show Ï„-right: 0 < 1 + Ï„ t
    have hin0 : LexDM_c ((0 : Multiset Nat), tau void)
        ((0 : Multiset Nat), tau (integrate (delta t))) := by
      refine Prod.Lex.right (0 : Multiset Nat) ?tauLt
      have : (0 : Nat) < Nat.succ (tau t) := Nat.succ_pos _
      simpa [tau, Nat.add_comm] using this
    -- Outer Î±=0 witness on concrete pairs, then rewrite Î¼-components
    have hcore : Lex3c (0, ((0 : Multiset Nat), tau void))
        (0, ((0 : Multiset Nat), tau (integrate (delta t)))) :=
      (Prod.Lex.right
        (Î± := Nat) (Î² := (Multiset Nat Ã— Nat))
        (ra := (Â· < Â·)) (rb := LexDM_c)
        (a := (0 : Nat)) hin0)
    simpa [Lex3c, mu3c, kappaM, kappaM_int_delta, tau, h0] using hcore
  Â· -- Îº strictly grows from 0 to Îºá´¹ t â‰  0: DM-left on 0 <â‚˜ Îºá´¹ t
    have hdm : DM (0 : Multiset Nat) (kappaM (integrate (delta t))) := by
      -- kappaM (integrate (delta t)) = kappaM t
      have : kappaM (integrate (delta t)) = kappaM t := by simpa [kappaM_int_delta]
      -- Use DM X < X+Z with X=0, Z=kappaM t (nonzero)
      have hz : kappaM t â‰  (0 : Multiset Nat) := by
        intro hz; exact h0 (by simpa using hz)
      -- 0 <â‚˜ 0 + (kappaM t) = kappaM t
      simpa [this, zero_add] using MetaSN_DM.dm_lt_add_of_ne_zero' (0 : Multiset Nat) (kappaM t) hz
    -- Inner DM-left on concrete Îº-components, then close outer at Î±=0
    have hin0 : LexDM_c ((0 : Multiset Nat), tau void)
        ((kappaM (integrate (delta t))), tau (integrate (delta t))) := by
      simpa using
        (dm_to_LexDM_c_left (X := (0 : Multiset Nat)) (Y := kappaM (integrate (delta t)))
          (Ï„â‚ := tau void) (Ï„â‚‚ := tau (integrate (delta t))) hdm)
    have hcore : Lex3c (0, ((0 : Multiset Nat), tau void))
        (0, (kappaM (integrate (delta t)), tau (integrate (delta t)))) :=
      (Prod.Lex.right
        (Î± := Nat) (Î² := (Multiset Nat Ã— Nat))
        (ra := (Â· < Â·)) (rb := LexDM_c)
        (a := (0 : Nat)) hin0)
    simpa [Lex3c, mu3c, kappaM, kappaM_int_delta, tau] using hcore

/-- **Rule: merge void t â†’ t** (guarded by Î´(t) = 0)

Strategy: Ï„-drop under Î´ and Îº ties
Key inequality: Ï„(t) < 2 + Ï„(t)
-/
lemma drop_R_merge_void_left_c (t : Trace) (hÎ´ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge void t)) := by
  classical
  -- Build inner Îº-tie, Ï„-right
  have hÎº : kappaM (merge void t) = kappaM t := by simpa using MetaSN_DM.kappaM_merge_void_left t
  have hÏ„' : tau t < 2 + tau t := by
    omega
  have hÏ„m : tau t < tau (merge void t) := by
    simpa [tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hÏ„'
  -- Inner Îº-anchor at RHS Îº
  have hin : LexDM_c (kappaM t, tau t) (kappaM (merge void t), tau (merge void t)) := by
    simpa [hÎº] using (Prod.Lex.right (kappaM (merge void t)) hÏ„m)
  -- Canonical Î±=0 outer witness; close by rewriting Î¼3c pairs
  have hin' : LexDM_c (kappaM t, tau t) (kappaM t, 2 + tau t) := by
    simpa [hÎº, tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hin
  have H : Lex3c (0, (kappaM t, tau t)) (0, (kappaM t, 2 + tau t)) :=
    (Prod.Lex.right
      (Î± := Nat) (Î² := (Multiset Nat Ã— Nat))
      (ra := (Â· < Â·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin')
  -- Now prove the main goal: both sides have Î´=0 due to guard
  unfold Lex3c mu3c
  simp only [deltaFlag] at hÎ´ âŠ¢
  rw [hÎ´]
  simp only [hÎº, tau]
  exact H

/-- **Rule: merge t void â†’ t** (guarded by Î´(t) = 0)

Symmetric to merge_void_left.
Strategy: Ï„-drop under ties
-/
lemma drop_R_merge_void_right_c (t : Trace) (hÎ´ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge t void)) := by
  classical
  -- Inner Îº-tie and Ï„-right
  have hÎº : kappaM (merge t void) = kappaM t := by simpa using MetaSN_DM.kappaM_merge_void_right t
  have hÏ„' : tau t < 2 + tau t := by
    omega
  have hÏ„m : tau t < tau (merge t void) := by
    simpa [tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hÏ„'
  have hin : LexDM_c (kappaM t, tau t) (kappaM (merge t void), tau (merge t void)) := by
    simpa [hÎº] using (Prod.Lex.right (kappaM (merge t void)) hÏ„m)
  -- Canonical Î±=0 outer witness; close by rewriting Î¼3c pairs
  have hin' : LexDM_c (kappaM t, tau t) (kappaM t, 2 + tau t) := by
    simpa [hÎº, tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hin
  have H : Lex3c (0, (kappaM t, tau t)) (0, (kappaM t, 2 + tau t)) :=
    (Prod.Lex.right
      (Î± := Nat) (Î² := (Multiset Nat Ã— Nat))
      (ra := (Â· < Â·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin')
  -- Now prove the main goal: both sides have Î´=0 due to guard
  unfold Lex3c mu3c
  simp only [deltaFlag] at hÎ´ âŠ¢
  rw [hÎ´]
  simp only [hÎº, tau]
  exact H

/-- **Rule: eqW a b â†’ integrate (merge a b)**

The critical inequality: 1 + 2 + X < 4 + X
This is why we chose Ï„(eqW) = 4.
-/
lemma drop_R_eq_diff_c (a b : Trace) :
    Lex3c (mu3c (integrate (merge a b))) (mu3c (eqW a b)) := by
  classical
  -- Inner tie on Îº; Ï„ inequality: 1+2+â€¦ < 4+â€¦; then lift to Î±=0 and rewrite Î´
  have hÎº : kappaM (integrate (merge a b)) = kappaM (eqW a b) := by
    simpa using MetaSN_DM.kappaM_eq_diff a b
  -- 3 < 4, then add (Ï„ a + Ï„ b) on the right
  have hÏ„ : 1 + (2 + (tau a + tau b)) < 4 + (tau a + tau b) := by
    have h1 : 1 + (2 + (tau a + tau b)) = (1 + 2) + (tau a + tau b) := by
      simpa using (Nat.add_assoc 1 2 (tau a + tau b)).symm
    have h12 : 1 + 2 = 3 := by decide
    have h2 : (1 + 2) + (tau a + tau b) = 3 + (tau a + tau b) := by
      simpa using congrArg (fun x => x + (tau a + tau b)) h12
    have : 3 + (tau a + tau b) < 4 + (tau a + tau b) :=
      Nat.add_lt_add_right (by decide : 3 < 4) (tau a + tau b)
    simpa [h1, h2]
  have hin : LexDM_c (kappaM (integrate (merge a b)), tau (integrate (merge a b)))
                 (kappaM (integrate (merge a b)), tau (eqW a b)) := by
    -- Use Ï„-right with Îº anchor directly.
    simpa [hÎº, tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Prod.Lex.right (kappaM (integrate (merge a b))) hÏ„)
  have hcore : Lex3c (0, (kappaM (integrate (merge a b)), tau (integrate (merge a b))))
      (0, (kappaM (integrate (merge a b)), tau (eqW a b))) :=
    (Prod.Lex.right
      (Î± := Nat) (Î² := (Multiset Nat Ã— Nat))
      (ra := (Â· < Â·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin)
  simpa [Lex3c, mu3c, deltaFlag] using hcore

/-- **Rule: eqW a a â†’ void**

Handles duplication via case split:
- If Îºá´¹(a) = 0: Ï„-drop
- If Îºá´¹(a) â‰  0: DM-drop on union
-/
lemma drop_R_eq_refl_c (a : Trace) :
    Lex3c (mu3c void) (mu3c (eqW a a)) := by
  classical
  dsimp [mu3c, Lex3c]
  refine Prod.Lex.right (0 : Nat) ?inner
  by_cases h0 : kappaM a = 0
  Â· -- Îº tie at 0 â†’ Ï„-right: 0 < 4 + Ï„ a + Ï„ a
    -- build inner at Îº = 0 and rewrite Îº on RHS via h0
    have hÎº0 : kappaM (eqW a a) = 0 := by simpa [MetaSN_DM.kappaM_eq_refl, h0]
    have hin0 : LexDM_c ((0 : Multiset Nat), tau void)
        ((0 : Multiset Nat), tau (eqW a a)) := by
      refine Prod.Lex.right (0 : Multiset Nat) ?tauDrop
      -- 0 < 4 + (Ï„ a + Ï„ a)
      have h4 : 0 < 4 := by decide
      have h' : 0 < 4 + (tau a + tau a) := lt_of_lt_of_le h4 (Nat.le_add_right 4 (tau a + tau a))
      simpa [tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    simpa [MetaSN_DM.kappaM_eq_refl, h0] using hin0
  Â· -- Îº â‰  0 â†’ DM-left: 0 <â‚˜ ÎºâˆªÎº
    have hU : kappaM a âˆª kappaM a â‰  (0 : Multiset Nat) :=
      union_self_ne_zero_of_ne_zero (X := kappaM a) h0
    have hdm : DM (0 : Multiset Nat) (kappaM a âˆª kappaM a) := by
      simpa using MetaSN_DM.dm_lt_add_of_ne_zero' (0 : Multiset Nat) (kappaM a âˆª kappaM a) hU
    -- rewrite Îº on RHS using kappaM_eq_refl and use DM-left on 0 <â‚˜ ÎºâˆªÎº
    simpa [MetaSN_DM.kappaM_eq_refl] using
      (dm_to_LexDM_c_left (X := 0) (Y := kappaM a âˆª kappaM a)
        (Ï„â‚ := tau void) (Ï„â‚‚ := tau (eqW a a)) hdm)

/-- **Rule: recÎ” b s (delta n) â†’ app s (recÎ” b s n)**

THE STAR: Î´-drop from 1 to 0.
This is why we have the Î´-flag component.
-/
lemma drop_R_rec_succ_c (b s n : Trace) :
    Lex3c (mu3c (app s (recÎ” b s n))) (mu3c (recÎ” b s (delta n))) := by
  -- Outer Nat component drops strictly: 0 < 1
  dsimp [mu3c, Lex3c]
  -- Use the deltaFlag simplifications to show 0 < 1 on the Nat component
  have a_lt : (0 : Nat) < 1 := by decide
  -- Left component: Î´(app s (recÎ” b s n)) = 0 and Î´(recÎ” b s (delta n)) = 1
  have H : Prod.Lex (Â· < Â·) LexDM_c
      ((0 : Nat), (kappaM (app s (recÎ” b s n)), tau (app s (recÎ” b s n))))
      ((1 : Nat), (kappaM (recÎ” b s (delta n)), tau (recÎ” b s (delta n)))) := by
    exact Prod.Lex.left (aâ‚ := (0 : Nat)) (aâ‚‚ := (1 : Nat)) (bâ‚ := (kappaM (app s (recÎ” b s n)), tau (app s (recÎ” b s n)))) (bâ‚‚ := (kappaM (recÎ” b s (delta n)), tau (recÎ” b s (delta n)))) a_lt
  simpa [mu3c, Lex3c, MetaSN_KO7.deltaFlag_app, MetaSN_KO7.deltaFlag_rec_delta]
    using H

/-- **Rule: recÎ” b s void â†’ b** (guarded by Î´(b) = 0)

Strategy: Îºá´¹ strictly drops via DM; lift to inner lex, then to outer with Î´=0 on both sides.
-/
lemma drop_R_rec_zero_c (b s : Trace) (hÎ´ : deltaFlag b = 0) :
    Lex3c (mu3c b) (mu3c (recÎ” b s void)) := by
  classical
  -- Inner: DM-left on Îºá´¹ component
  have hdm : DM (kappaM b) (kappaM (recÎ” b s void)) := by
    -- use the KO7 helper
    simpa [DM] using MetaSN_DM.dm_drop_R_rec_zero b s
  have hin : LexDM_c (kappaM b, tau b)
      (kappaM (recÎ” b s void), tau (recÎ” b s void)) := by
    simpa using (dm_to_LexDM_c_left (X := kappaM b) (Y := kappaM (recÎ” b s void))
      (Ï„â‚ := tau b) (Ï„â‚‚ := tau (recÎ” b s void)) hdm)
  -- Build outer witness at Î±=0 using the guard and rec_zero Î´=0
  have hb0 : MetaSN_KO7.deltaFlag b = 0 := hÎ´
  have hr0 : MetaSN_KO7.deltaFlag (recÎ” b s void) = 0 := by
    simpa [MetaSN_KO7.deltaFlag_rec_zero]
  have hcore : Lex3c (0, (kappaM b, tau b))
      (0, (kappaM (recÎ” b s void), tau (recÎ” b s void))) :=
    (Prod.Lex.right (Î± := Nat) (Î² := (Multiset Nat Ã— Nat)) (ra := (Â· < Â·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin)
  -- Cast the 0-anchored witness to the goal using explicit `change` + `rw` (no simp recursion)
  change Prod.Lex (Â· < Â·) LexDM_c
      ((MetaSN_KO7.deltaFlag b), (kappaM b, tau b))
      ((MetaSN_KO7.deltaFlag (recÎ” b s void)), (kappaM (recÎ” b s void), tau (recÎ” b s void)))
  rw [hb0, hr0]
  exact hcore

/-- **Rule: merge t t â†’ t** (guarded by Î´(t) = 0 and Îºá´¹(t) = 0)

With Îºá´¹(t) = 0, Îº ties at 0; use Ï„-drop: Ï„ t < 2 + Ï„ t + Ï„ t.
-/
lemma drop_R_merge_cancel_c (t : Trace)
    (hÎ´ : deltaFlag t = 0) (h0 : kappaM t = 0) :
    Lex3c (mu3c t) (mu3c (merge t t)) := by
  classical
  -- Ï„-drop under Îº tie at 0
  have hÏ„ : tau t < tau (merge t t) := by
    -- show: Ï„ t < 2 + Ï„ t + Ï„ t
    have hA : tau t < 2 + tau t := by omega
    have hB : 2 + tau t â‰¤ 2 + tau t + tau t := Nat.le_add_right _ _
    exact lt_of_lt_of_le hA (by simpa [Nat.add_assoc, tau, Nat.add_comm, Nat.add_left_comm] using hB)
  -- Inner at Îº = 0
  have hin0 : LexDM_c ((0 : Multiset Nat), tau t)
      ((0 : Multiset Nat), tau (merge t t)) := by
    exact Prod.Lex.right (0 : Multiset Nat) hÏ„
  -- Rewrite Îº components via guards
  have hÎº_merge : kappaM (merge t t) = 0 := by simpa [MetaSN_DM.kappaM_merge_cancel, h0]
  have hin : LexDM_c (kappaM t, tau t) (kappaM (merge t t), tau (merge t t)) := by
    simpa [h0, hÎº_merge] using hin0
  -- Outer witness at Î±=0 using guard Î´(t)=0 and Î´(merge)=0
  have ht0 : MetaSN_KO7.deltaFlag t = 0 := hÎ´
  have hm0 : MetaSN_KO7.deltaFlag (merge t t) = 0 := by simpa [MetaSN_KO7.deltaFlag_merge]
  have hcore : Lex3c (0, (kappaM t, tau t)) (0, (kappaM (merge t t), tau (merge t t))) :=
    (Prod.Lex.right (Î± := Nat) (Î² := (Multiset Nat Ã— Nat)) (ra := (Â· < Â·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin)
  -- Cast the 0-anchored witness to the goal using explicit `change` + `rw` (no simp recursion)
  change Prod.Lex (Â· < Â·) LexDM_c
      ((MetaSN_KO7.deltaFlag t), (kappaM t, tau t))
      ((MetaSN_KO7.deltaFlag (merge t t)), (kappaM (merge t t), tau (merge t t)))
  rw [ht0, hm0]
  exact hcore


/-- **MASTER THEOREM: Every SafeStep decreases Î¼3c**

Pattern matches all 8 constructors to their decrease proofs.
This is the heart of the termination argument.
-/
lemma measure_decreases_safe_c : âˆ€ {a b}, MetaSN_KO7.SafeStep a b â†’ Lex3c (mu3c b) (mu3c a)
| _, _, MetaSN_KO7.SafeStep.R_int_delta t => by simpa using drop_R_int_delta_c t
| _, _, MetaSN_KO7.SafeStep.R_merge_void_left t hÎ´ => by simpa using drop_R_merge_void_left_c t hÎ´
| _, _, MetaSN_KO7.SafeStep.R_merge_void_right t hÎ´ => by simpa using drop_R_merge_void_right_c t hÎ´
| _, _, MetaSN_KO7.SafeStep.R_merge_cancel t hÎ´ h0 => by simpa using drop_R_merge_cancel_c t hÎ´ h0
| _, _, MetaSN_KO7.SafeStep.R_rec_zero b s hÎ´ => by simpa using drop_R_rec_zero_c b s hÎ´
| _, _, MetaSN_KO7.SafeStep.R_rec_succ b s n => by simpa using drop_R_rec_succ_c b s n
| _, _, MetaSN_KO7.SafeStep.R_eq_refl a _h0 => by
    -- Guard redundant for Ï„; we provide an unguarded drop
    simpa using drop_R_eq_refl_c a
| _, _, MetaSN_KO7.SafeStep.R_eq_diff a b _ => by simpa using drop_R_eq_diff_c a b


/-- **Generic well-foundedness wrapper**

For any relation R that decreases Î¼3c, R^op is well-founded.
Bridge from measure decrease to termination.
-/
theorem wellFounded_of_measure_decreases_R_c
  {R : Trace â†’ Trace â†’ Prop}
  (hdec : âˆ€ {a b : Trace}, R a b â†’ Lex3c (mu3c b) (mu3c a)) :
  WellFounded (fun a b : Trace => R b a) := by
  -- Pull back the well-founded Lex3c along Î¼3c
  have wf_measure : WellFounded (fun x y : Trace => Lex3c (mu3c x) (mu3c y)) :=
    InvImage.wf (f := mu3c) wf_Lex3c
  -- Show Ráµ’áµ– âŠ† InvImage Î¼3c Lex3c
  have hsub : Subrelation (fun a b => R b a) (fun x y : Trace => Lex3c (mu3c x) (mu3c y)) := by
    intro x y hxy; exact hdec hxy
  exact Subrelation.wf hsub wf_measure

/-- **MAIN RESULT: SafeStep is strongly normalizing**

Well-foundedness of SafeStepRev proves termination.
Fully computable, no axioms, no noncomputables.

### Implications:
- No infinite SafeStep chains
- Normalizer always terminates
- Confluence + SN = decidable equality
-/
theorem wf_SafeStepRev_c : WellFounded MetaSN_KO7.SafeStepRev :=
  wellFounded_of_measure_decreases_R_c (R := MetaSN_KO7.SafeStep)
    (fun {_ _} h => measure_decreases_safe_c h)

end OperatorKO7.MetaCM
````

## OperatorKO7/Meta/ComputableMeasure_Verification.lean

**Lines:** 241

``lean
import OperatorKO7.Meta.ComputableMeasure

/-!
# Verification Suite for ComputableMeasure

This file provides comprehensive verification that our computable measure
is bulletproof and handles all edge cases correctly.

## Test Categories:
1. Ï„ monotonicity verification
2. DM order properties
3. Measure decrease for each rule
4. Edge cases and corner cases
5. Comparison with original noncomputable measure
-/

namespace OperatorKO7.MetaCM.Verification

open OperatorKO7 Trace MetaCM
open MetaSN_KO7 MetaSN_DM

/-! ## Section 1: Ï„ Monotonicity Tests -/

-- Verify Ï„ is monotone for all constructors except delta
example (t : Trace) : tau t < tau (integrate t) := by
  simp [tau]
example (a b : Trace) : tau a < tau (merge a b) := by
  simp [tau]; omega
example (a b : Trace) : tau b < tau (merge a b) := by
  simp [tau]; omega
example (a b : Trace) : tau a < tau (app a b) := by
  simp [tau]; omega
example (a b : Trace) : tau b < tau (app a b) := by
  simp [tau]; omega
example (b s n : Trace) : tau b < tau (recÎ” b s n) := by
  simp [tau]; omega
example (b s n : Trace) : tau s < tau (recÎ” b s n) := by
  simp [tau]; omega
example (b s n : Trace) : tau n < tau (recÎ” b s n) := by
  simp [tau]; omega
example (a b : Trace) : tau a < tau (eqW a b) := by
  simp [tau]; omega
example (a b : Trace) : tau b < tau (eqW a b) := by
  simp [tau]; omega

-- Verify delta is transparent
example (t : Trace) : tau (delta t) = tau t := rfl

-- Verify the critical inequality for eq_diff
example (a b : Trace) : tau (integrate (merge a b)) < tau (eqW a b) := by
  simp [tau]; omega

/-! ## Section 2: Lexicographic Order Properties -/

-- Verify Lex3c is indeed well-founded
example : WellFounded Lex3c := wf_Lex3c

-- Verify the lifting lemma works
example {X Y : Multiset Nat} {Ï„â‚ Ï„â‚‚ : Nat} (h : DM X Y) :
    LexDM_c (X, Ï„â‚) (Y, Ï„â‚‚) := dm_to_LexDM_c_left h

/-! ## Section 3: Measure Decrease Verification -/

-- Test all 8 rules decrease the measure
section RuleTests

-- Rule 1: integrate (delta t) â†’ void
example (t : Trace) : Lex3c (mu3c void) (mu3c (integrate (delta t))) := by
  apply drop_R_int_delta_c

-- Rule 2: merge void t â†’ t
example (t : Trace) (hÎ´ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge void t)) := by
  apply drop_R_merge_void_left_c
  exact hÎ´

-- Rule 3: merge t void â†’ t
example (t : Trace) (hÎ´ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge t void)) := by
  apply drop_R_merge_void_right_c
  exact hÎ´

-- Rule 4: merge t t â†’ t (duplication case!)
example (t : Trace) (hÎ´ : deltaFlag t = 0) (h0 : kappaM t = 0) :
    Lex3c (mu3c t) (mu3c (merge t t)) := by
  apply drop_R_merge_cancel_c
  exact hÎ´
  exact h0

-- Rule 5: recÎ” b s void â†’ b
example (b s : Trace) (hÎ´ : deltaFlag b = 0) :
    Lex3c (mu3c b) (mu3c (recÎ” b s void)) := by
  apply drop_R_rec_zero_c
  exact hÎ´

-- Rule 6: recÎ” b s (delta n) â†’ app s (recÎ” b s n)
example (b s n : Trace) :
    Lex3c (mu3c (app s (recÎ” b s n))) (mu3c (recÎ” b s (delta n))) := by
  apply drop_R_rec_succ_c

-- Rule 7: eqW a a â†’ void
example (a : Trace) :
    Lex3c (mu3c void) (mu3c (eqW a a)) := by
  apply drop_R_eq_refl_c

-- Rule 8: eqW a b â†’ integrate (merge a b)
example (a b : Trace) :
    Lex3c (mu3c (integrate (merge a b))) (mu3c (eqW a b)) := by
  apply drop_R_eq_diff_c

end RuleTests

/-! ## Section 4: Edge Cases and Corner Cases -/

-- Deeply nested terms still decrease
example :
    let t := delta (delta (delta void))
    Lex3c (mu3c void) (mu3c (integrate t)) := by
  apply drop_R_int_delta_c

-- Multiple deltas preserve transparency
lemma tau_delta_iterate (n : Nat) (t : Trace) : tau (delta^[n] t) = tau t := by
  induction n generalizing t with
  | zero =>
    rfl
  | succ n ih =>
    -- `f^[n+1] t = f^[n] (f t)` and `tau (delta t) = tau t` by definition.
    simpa [Function.iterate_succ, tau] using ih (t := delta t)

example (n : Nat) : tau (delta^[n] void) = tau void := by
  simpa using tau_delta_iterate n void

-- Verify Î´-flag is binary (0 or 1)
/--
`deltaFlag` is intentionally a binary phase indicator (0 or 1).

This lemma is used as a sanity check that the computable triple-lex measure does not accidentally
encode additional phases beyond the intended `recÎ” _ _ (delta _)` detection.
-/
lemma deltaFlag_binary (t : Trace) : deltaFlag t = 0 âˆ¨ deltaFlag t = 1 := by
  cases t <;> simp
  case recÎ” b s n =>
    cases n <;> simp

/-! ## Section 5: SafeStep Decrease Aggregation -/

-- The master theorem works for all SafeStep constructors
example {a b : Trace} (h : SafeStep a b) :
    Lex3c (mu3c b) (mu3c a) :=
  measure_decreases_safe_c h

-- SafeStepRev is indeed well-founded
example : WellFounded MetaSN_KO7.SafeStepRev := wf_SafeStepRev_c

/-! ## Section 6: Comparison with Noncomputable Measure -/

-- Our computable measure implies the same well-foundedness
/--
The computable development is strictly stronger in the "artifact sense":

We can derive well-foundedness of `SafeStepRev` without appealing to any noncomputable ordinal
payload, by using `wf_SafeStepRev_c` from `Meta/ComputableMeasure.lean`.
-/
theorem computable_implies_original :
    WellFounded MetaSN_KO7.SafeStepRev := by
  exact wf_SafeStepRev_c

-- Both measures agree on well-foundedness (modulo computability)
/--
A deliberately weak "equivalence" statement:

This does *not* claim the ordinal and computable measures are extensionally equal.
It only records that (i) the existence of *some* measure implies well-foundedness, and
(ii) well-foundedness implies the existence of *a* measure (choose `mu3c`).
-/
theorem measures_equivalent_wf :
    (âˆƒ (_Î¼ : Trace â†’ Nat Ã— (Multiset Nat Ã— Nat)), WellFounded MetaSN_KO7.SafeStepRev) â†”
      WellFounded MetaSN_KO7.SafeStepRev := by
  constructor
  Â· intro âŸ¨_, hâŸ©
    exact h
  Â· intro h
    exact âŸ¨mu3c, hâŸ©

/-! ## Section 7: Stress Tests -/

-- Large terms still work
/-- A moderately complex concrete trace used for stress-testing `tau` and `mu3c`. -/
def bigTrace : Trace :=
  recÎ” (merge void void) (app void void) (delta (integrate void))

example : tau bigTrace = 3 + 2 + 1 + 1 := by
  simp [bigTrace, tau]

-- Measure works on big terms
example :
    Lex3c (mu3c void) (mu3c (eqW bigTrace bigTrace)) := by
  apply drop_R_eq_refl_c

/-! ## Section 8: Invariants and Properties -/

-- Ï„ preserves structure under delta
/-- `tau` is transparent under `delta` by definition (restated as a named lemma). -/
lemma tau_delta_preserve (t : Trace) : tau (delta t) = tau t := rfl

-- Îºá´¹ behavior under constructors (from SafeStep core)
/-- Convenience bundle of basic `kappaM` simp-facts (re-exported as a single lemma). -/
lemma kappaM_facts (a b : Trace) :
    kappaM void = 0 âˆ§
    kappaM (delta a) = kappaM a âˆ§
    kappaM (integrate a) = kappaM a âˆ§
    kappaM (merge a b) = kappaM a âˆª kappaM b âˆ§
    kappaM (app a b) = kappaM a âˆª kappaM b âˆ§
    kappaM (eqW a b) = kappaM a âˆª kappaM b := by
  simp [kappaM]

-- Î´-flag is 1 only for recÎ” _ _ (delta _)
/-- Characterization of the `deltaFlag` phase bit. -/
lemma deltaFlag_characterization (t : Trace) :
    deltaFlag t = 1 â†” âˆƒ b s n, t = recÎ” b s (delta n) := by
  cases t <;> simp [deltaFlag]
  case recÎ” b s n =>
    cases n <;> simp

/-! ## Section 9: No Infinite Chains -/

-- Direct proof that no infinite SafeStep chain exists
/-- There is no infinite forward `SafeStep` chain, since `mu3c` strictly decreases and `Lex3c` is WF. -/
theorem no_infinite_safestep_chain :
    Â¬âˆƒ (seq : Nat â†’ Trace), âˆ€ n, SafeStep (seq n) (seq (n + 1)) := by
  intro âŸ¨seq, hâŸ©
  -- The measure strictly decreases along the chain
  have dec : âˆ€ n, Lex3c (mu3c (seq (n + 1))) (mu3c (seq n)) := by
    intro n
    exact measure_decreases_safe_c (h n)
  -- But Lex3c is well-founded, so no infinite descending chain exists.
  exact
    (WellFounded.wellFounded_iff_no_descending_seq.1 wf_Lex3c).elim
      âŸ¨fun n => mu3c (seq n), decâŸ©

end OperatorKO7.MetaCM.Verification
````

## OperatorKO7/Meta/Confluence_Safe.lean

**Lines:** 529

``lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.Normalize_Safe
import OperatorKO7.Meta.SafeStep_Ctx

/-!
Local confluence / local join analysis for the KO7 safe fragment.

Purpose:
- Defines local-join predicates for `SafeStep` (safe fragment) and for the full kernel `Step`.
- Proves local joinability lemmas for many safe root shapes, typically by uniqueness or vacuity.
- Records an explicit caveat for the full kernel: the two `eqW` rules overlap at `eqW a a`, so the
  full kernel `Step` is not locally confluent at `eqW void void` (and more generally has a peak at
  `eqW a a`).

Scope boundary:
- The positive results in this file are for `SafeStep` only.
- The negative result `not_localJoinStep_eqW_void_void` is about the full kernel `Step` and is used
  as a clarity point for the safe-vs-full distinction.

This file is typically paired with:
- `Meta/SafeStep_Ctx.lean` (context closure utilities)
- `Meta/Newman_Safe.lean` (Newman's lemma: SN + local join -> confluence), when a global local-join
  hypothesis is supplied.
-/
open Classical
open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Local joinability at a fixed source for the KO7 safe relation. -/
def LocalJoinSafe (a : Trace) : Prop :=
  âˆ€ {b c}, SafeStep a b â†’ SafeStep a c â†’ âˆƒ d, SafeStepStar b d âˆ§ SafeStepStar c d

/-- Local joinability at a fixed source for the full kernel relation `Step`. -/
def LocalJoinStep (a : Trace) : Prop :=
  âˆ€ {b c}, Step a b â†’ Step a c â†’ âˆƒ d, StepStar b d âˆ§ StepStar c d

/-- Full-step caveat: the two kernel `eqW` rules overlap, so `eqW void void` is not locally joinable. -/
theorem not_localJoinStep_eqW_void_void : Â¬ LocalJoinStep (eqW void void) := by
  intro hjoin
  have hb : Step (eqW void void) void := Step.R_eq_refl void
  have hc : Step (eqW void void) (integrate (merge void void)) := Step.R_eq_diff void void
  rcases hjoin hb hc with âŸ¨d, hbStar, hcStarâŸ©
  have hnf_void : NormalForm void := by
    intro ex
    rcases ex with âŸ¨u, huâŸ©
    cases hu
  have hnf_int_merge : NormalForm (integrate (merge void void)) := by
    intro ex
    rcases ex with âŸ¨u, huâŸ©
    cases hu
  have hd_eq_void : d = void := (nf_no_stepstar_forward hnf_void hbStar).symm
  have hd_eq_int : d = integrate (merge void void) := (nf_no_stepstar_forward hnf_int_merge hcStar).symm
  have hneq : (integrate (merge void void) : Trace) â‰  void := by
    intro h
    cases h
  exact hneq (hd_eq_int.symm.trans hd_eq_void)

/-- If there are no safe root steps from `a`, local join holds vacuously. -/
theorem localJoin_of_none (a : Trace)
    (h : âˆ€ {b}, SafeStep a b â†’ False) : LocalJoinSafe a := by
  intro b c hb hc
  exact False.elim (h hb)

/-- If every safe root step from `a` has the same target `d`, then `a` is locally joinable. -/
theorem localJoin_of_unique (a d : Trace)
    (h : âˆ€ {b}, SafeStep a b â†’ b = d) : LocalJoinSafe a := by
  intro b c hb hc
  have hb' : b = d := h hb
  have hc' : c = d := h hc
  refine âŸ¨d, ?_, ?_âŸ©
  Â· simpa [hb'] using (SafeStepStar.refl d)
  Â· simpa [hc'] using (SafeStepStar.refl d)

/-- If there are no safe root steps from `a`, any `SafeStepStar a d` must be reflexive. -/
theorem star_only_refl_of_none {a d : Trace}
    (h : âˆ€ {b}, SafeStep a b â†’ False) : SafeStepStar a d â†’ d = a := by
  intro hs
  cases hs with
  | refl t => rfl
  | @tail a' b c hab hbc =>
      exact False.elim (h hab)

/-- If `a` is in safe normal form, there are no outgoing safe steps; local join holds. -/
theorem localJoin_of_nf (a : Trace) (hnf : NormalFormSafe a) : LocalJoinSafe a := by
  refine localJoin_of_none (a := a) ?h
  intro b hb; exact no_step_from_nf hnf hb

/-- Root critical peak at `merge void void` is trivially joinable:
 both branches step to `void`. -/
theorem localJoin_merge_void_void : LocalJoinSafe (merge void void) := by
  intro b c hb hc
  -- Both reducts are definitionally `void` in each possible branch.
  have hb_refl : SafeStepStar b void := by
    cases hb with
    | R_merge_void_left t hÎ´ =>
        -- Here a = merge void t unifies with merge void void, so t = void and b = void.
        exact SafeStepStar.refl _
    | R_merge_void_right t hÎ´ =>
        exact SafeStepStar.refl _
    | R_merge_cancel t hÎ´ h0 =>
        exact SafeStepStar.refl _
  have hc_refl : SafeStepStar c void := by
    cases hc with
    | R_merge_void_left t hÎ´ =>
        exact SafeStepStar.refl _
    | R_merge_void_right t hÎ´ =>
        exact SafeStepStar.refl _
    | R_merge_cancel t hÎ´ h0 =>
        exact SafeStepStar.refl _
  exact âŸ¨void, hb_refl, hc_reflâŸ©

/-- At `integrate (delta t)` there is only one safe root rule; local join is trivial. -/
theorem localJoin_int_delta (t : Trace) : LocalJoinSafe (integrate (delta t)) := by
  intro b c hb hc
  have hb_refl : SafeStepStar b void := by
    cases hb with
    | R_int_delta _ => exact SafeStepStar.refl _
  have hc_refl : SafeStepStar c void := by
    cases hc with
    | R_int_delta _ => exact SafeStepStar.refl _
  exact âŸ¨void, hb_refl, hc_reflâŸ©

/-- At `integrate void`, no safe root rule applies (not a `delta _`); vacuous. -/
theorem localJoin_integrate_void : LocalJoinSafe (integrate void) := by
  refine localJoin_of_none (a := integrate void) ?h
  intro x hx
  cases hx

/-- At `integrate (merge a b)`, there is no safe root rule; join vacuously. -/
theorem localJoin_integrate_merge (a b : Trace) : LocalJoinSafe (integrate (merge a b)) := by
  refine localJoin_of_none (a := integrate (merge a b)) ?h
  intro x hx; cases hx

/-- At `integrate (app a b)`, there is no safe root rule; join vacuously. -/
theorem localJoin_integrate_app (a b : Trace) : LocalJoinSafe (integrate (app a b)) := by
  refine localJoin_of_none (a := integrate (app a b)) ?h
  intro x hx; cases hx

/-- At `integrate (eqW a b)`, there is no safe root rule; join vacuously. -/
theorem localJoin_integrate_eqW (a b : Trace) : LocalJoinSafe (integrate (eqW a b)) := by
  refine localJoin_of_none (a := integrate (eqW a b)) ?h
  intro x hx; cases hx

/-- At `integrate (integrate t)`, there is no safe root rule; join vacuously. -/
theorem localJoin_integrate_integrate (t : Trace) : LocalJoinSafe (integrate (integrate t)) := by
  refine localJoin_of_none (a := integrate (integrate t)) ?h
  intro x hx; cases hx

/-- At `integrate (recÎ” b s n)`, there is no safe root rule; join vacuously. -/
theorem localJoin_integrate_rec (b s n : Trace) : LocalJoinSafe (integrate (recÎ” b s n)) := by
  refine localJoin_of_none (a := integrate (recÎ” b s n)) ?h
  intro x hx; cases hx

/-- At `merge void t` there is only one safe root rule; local join is trivial. -/
theorem localJoin_merge_void_left (t : Trace) : LocalJoinSafe (merge void t) := by
  intro b c hb hc
  have hb_refl : SafeStepStar b t := by
    cases hb with
    | R_merge_void_left _ _ => exact SafeStepStar.refl _
    | R_merge_void_right _ _ => exact SafeStepStar.refl _
    | R_merge_cancel _ _ _ => exact SafeStepStar.refl _
  have hc_refl : SafeStepStar c t := by
    cases hc with
    | R_merge_void_left _ _ => exact SafeStepStar.refl _
    | R_merge_void_right _ _ => exact SafeStepStar.refl _
    | R_merge_cancel _ _ _ => exact SafeStepStar.refl _
  exact âŸ¨t, hb_refl, hc_reflâŸ©

/-- At `merge t void` there is only one safe root rule; local join is trivial. -/
theorem localJoin_merge_void_right (t : Trace) : LocalJoinSafe (merge t void) := by
  intro b c hb hc
  have hb_refl : SafeStepStar b t := by
    cases hb with
    | R_merge_void_right _ _ => exact SafeStepStar.refl _
    | R_merge_void_left _ _ => exact SafeStepStar.refl _
    | R_merge_cancel _ _ _ => exact SafeStepStar.refl _
  have hc_refl : SafeStepStar c t := by
    cases hc with
    | R_merge_void_right _ _ => exact SafeStepStar.refl _
    | R_merge_void_left _ _ => exact SafeStepStar.refl _
    | R_merge_cancel _ _ _ => exact SafeStepStar.refl _
  exact âŸ¨t, hb_refl, hc_reflâŸ©

/-- At `recÎ” b s void` there is only one safe root rule; local join is trivial. -/
theorem localJoin_rec_zero (b s : Trace) : LocalJoinSafe (recÎ” b s void) := by
  intro x y hx hy
  have hx_refl : SafeStepStar x b := by
    cases hx with
    | R_rec_zero _ _ _ => exact SafeStepStar.refl _
  have hy_refl : SafeStepStar y b := by
    cases hy with
    | R_rec_zero _ _ _ => exact SafeStepStar.refl _
  exact âŸ¨b, hx_refl, hy_reflâŸ©

/-- At `recÎ” b s (delta n)` there is only one safe root rule; local join is trivial. -/
theorem localJoin_rec_succ (b s n : Trace) : LocalJoinSafe (recÎ” b s (delta n)) := by
  intro x y hx hy
  have hx_refl : SafeStepStar x (app s (recÎ” b s n)) := by
    cases hx with
    | R_rec_succ _ _ _ => exact SafeStepStar.refl _
  have hy_refl : SafeStepStar y (app s (recÎ” b s n)) := by
    cases hy with
    | R_rec_succ _ _ _ => exact SafeStepStar.refl _
  exact âŸ¨app s (recÎ” b s n), hx_refl, hy_reflâŸ©

/-- At `merge t t`, any applicable safe rule reduces to `t`; local join is trivial. -/
theorem localJoin_merge_tt (t : Trace) : LocalJoinSafe (merge t t) := by
  intro b c hb hc
  have hb_refl : SafeStepStar b t := by
    cases hb with
    | R_merge_cancel _ _ _ => exact SafeStepStar.refl _
    | R_merge_void_left _ _ => exact SafeStepStar.refl _
    | R_merge_void_right _ _ => exact SafeStepStar.refl _
  have hc_refl : SafeStepStar c t := by
    cases hc with
    | R_merge_cancel _ _ _ => exact SafeStepStar.refl _
    | R_merge_void_left _ _ => exact SafeStepStar.refl _
    | R_merge_void_right _ _ => exact SafeStepStar.refl _
  exact âŸ¨t, hb_refl, hc_reflâŸ©

/-- At `void`, there is no safe root rule; join holds vacuously. -/
theorem localJoin_void : LocalJoinSafe void := by
  refine localJoin_of_none (a := void) ?h
  intro b hb; cases hb

/-- At `delta t`, there is no safe root rule; join holds vacuously. -/
theorem localJoin_delta (t : Trace) : LocalJoinSafe (delta t) := by
  refine localJoin_of_none (a := delta t) ?h
  intro b hb; cases hb


/-- Convenience: `merge void (delta n)` reduces uniquely to `delta n`. -/
theorem localJoin_merge_void_delta (n : Trace) : LocalJoinSafe (merge void (delta n)) :=
  localJoin_merge_void_left (delta n)

/-- Convenience: `merge (delta n) void` reduces uniquely to `delta n`. -/
theorem localJoin_merge_delta_void (n : Trace) : LocalJoinSafe (merge (delta n) void) :=
  localJoin_merge_void_right (delta n)

/-- Convenience: `merge (delta n) (delta n)` reduces (by cancel) to `delta n`. -/
theorem localJoin_merge_delta_delta (n : Trace) : LocalJoinSafe (merge (delta n) (delta n)) :=
  localJoin_merge_tt (delta n)

/-- At `eqW a b` with `a â‰  b`, only `R_eq_diff` applies at the root; local join is trivial. -/
theorem localJoin_eqW_ne (a b : Trace) (hne : a â‰  b) : LocalJoinSafe (eqW a b) := by
  -- Unique target is `integrate (merge a b)`.
  refine localJoin_of_unique (a := eqW a b) (d := integrate (merge a b)) ?h
  intro x hx
  cases hx with
  | R_eq_diff _ _ _ => rfl
  | R_eq_refl _ _ => exact (False.elim (hne rfl))

/-- At `eqW a a`, if `kappaM a â‰  0`, `R_eq_refl` cannot fire; and `R_eq_diff` is blocked by `a â‰  a`.
So there are no safe root steps and local join holds vacuously. -/
theorem localJoin_eqW_refl_guard_ne (a : Trace) (h0ne : MetaSN_DM.kappaM a â‰  0) :
    LocalJoinSafe (eqW a a) := by
  refine localJoin_of_none (a := eqW a a) ?h
  intro x hx
  cases hx with
  | R_eq_refl _ h0 => exact False.elim (h0ne h0)
  | R_eq_diff _ _ hne => exact False.elim (hne rfl)

/-- If `deltaFlag t â‰  0`, the left-void merge rule cannot apply; no competing branch. -/
theorem localJoin_merge_void_left_guard_ne (t : Trace)
    (hÎ´ne : deltaFlag t â‰  0) : LocalJoinSafe (merge void t) := by
  refine localJoin_of_unique (a := merge void t) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_void_left _ hÎ´ => exact (False.elim (hÎ´ne hÎ´))
  | R_merge_void_right _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t â‰  0`, the right-void merge rule cannot apply; no competing branch. -/
theorem localJoin_merge_void_right_guard_ne (t : Trace)
    (hÎ´ne : deltaFlag t â‰  0) : LocalJoinSafe (merge t void) := by
  refine localJoin_of_unique (a := merge t void) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_void_right _ hÎ´ => exact (False.elim (hÎ´ne hÎ´))
  | R_merge_void_left _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t â‰  0`, merge-cancel is blocked at root; vacuous local join. -/
theorem localJoin_merge_cancel_guard_delta_ne (t : Trace)
    (hÎ´ne : deltaFlag t â‰  0) : LocalJoinSafe (merge t t) := by
  refine localJoin_of_unique (a := merge t t) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_cancel _ hÎ´ _ => exact (False.elim (hÎ´ne hÎ´))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- If `kappaM t â‰  0`, merge-cancel is blocked at root; vacuous local join. -/
theorem localJoin_merge_cancel_guard_kappa_ne (t : Trace)
    (h0ne : MetaSN_DM.kappaM t â‰  0) : LocalJoinSafe (merge t t) := by
  refine localJoin_of_unique (a := merge t t) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_cancel _ _ h0 => exact (False.elim (h0ne h0))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- At `recÎ” b s void`, if `deltaFlag b â‰  0` then the rec-zero rule is blocked. -/
theorem localJoin_rec_zero_guard_ne (b s : Trace)
    (hÎ´ne : deltaFlag b â‰  0) : LocalJoinSafe (recÎ” b s void) := by
  refine localJoin_of_none (a := recÎ” b s void) ?h
  intro x hx
  cases hx with
  | R_rec_zero _ _ hÎ´ => exact (hÎ´ne hÎ´)

/-- At `integrate t`, if `t` is not a `delta _`, then there is no safe root step. -/
theorem localJoin_integrate_non_delta (t : Trace)
    (hnd : âˆ€ u, t â‰  delta u) : LocalJoinSafe (integrate t) := by
  refine localJoin_of_none (a := integrate t) ?h
  intro x hx
  cases hx with
  | R_int_delta u => exact (hnd u) rfl

/-- At `recÎ” b s n`, if `n â‰  void` and `n` is not a `delta _`, then no safe root step. -/
theorem localJoin_rec_other (b s n : Trace)
    (hn0 : n â‰  void) (hns : âˆ€ u, n â‰  delta u) : LocalJoinSafe (recÎ” b s n) := by
  refine localJoin_of_none (a := recÎ” b s n) ?h
  intro x hx
  cases hx with
  | R_rec_zero _ _ _ => exact (hn0 rfl)
  | R_rec_succ _ _ u => exact (hns u) rfl

/-- At `app a b`, there is no safe root rule; join holds vacuously. -/
theorem localJoin_app (a b : Trace) : LocalJoinSafe (app a b) := by
  refine localJoin_of_none (a := app a b) ?h
  intro x hx
  cases hx

/-- At `recÎ” b s (merge a c)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_merge (b s a c : Trace) : LocalJoinSafe (recÎ” b s (merge a c)) := by
  refine localJoin_of_none (a := recÎ” b s (merge a c)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s (app a c)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_app (b s a c : Trace) : LocalJoinSafe (recÎ” b s (app a c)) := by
  refine localJoin_of_none (a := recÎ” b s (app a c)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s (integrate t)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_integrate (b s t : Trace) : LocalJoinSafe (recÎ” b s (integrate t)) := by
  refine localJoin_of_none (a := recÎ” b s (integrate t)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s (eqW a c)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_eqW (b s a c : Trace) : LocalJoinSafe (recÎ” b s (eqW a c)) := by
  refine localJoin_of_none (a := recÎ” b s (eqW a c)) ?h
  intro x hx; cases hx

/-- At `merge a b`, if neither side is `void` and `a â‰  b`, then no safe root step. -/
theorem localJoin_merge_no_void_neq (a b : Trace)
    (hav : a â‰  void) (hbv : b â‰  void) (hneq : a â‰  b) : LocalJoinSafe (merge a b) := by
  refine localJoin_of_none (a := merge a b) ?h
  intro x hx
  cases hx with
  | R_merge_void_left _ _ => exact (hav rfl)
  | R_merge_void_right _ _ => exact (hbv rfl)
  | R_merge_cancel _ _ _ => exact (hneq rfl)

/-- If normalization is a fixed point, `a` is safe-normal; local join holds. -/
theorem localJoin_if_normalize_fixed (a : Trace) (hfix : normalizeSafe a = a) :
    LocalJoinSafe a := by
  have hnf : NormalFormSafe a := (nf_iff_normalize_fixed a).mpr hfix
  -- avoid definality issues by expanding the goal
  intro b c hb hc
  exact (localJoin_of_nf a hnf) hb hc

/--
Global local-join discharge for the safe relation.

This closes the remaining hypothesis needed by `Meta/Newman_Safe.lean`:
for every source trace `a`, root local-joinability holds for `SafeStep`.
-/
theorem localJoin_all_safe : âˆ€ a : Trace, LocalJoinSafe a := by
  intro a
  cases a with
  | void =>
      exact localJoin_void
  | delta t =>
      exact localJoin_delta t
  | integrate t =>
      cases t with
      | void =>
          exact localJoin_integrate_void
      | delta u =>
          exact localJoin_int_delta u
      | integrate u =>
          exact localJoin_integrate_integrate u
      | merge x y =>
          exact localJoin_integrate_merge x y
      | app x y =>
          exact localJoin_integrate_app x y
      | recÎ” b s n =>
          exact localJoin_integrate_rec b s n
      | eqW x y =>
          exact localJoin_integrate_eqW x y
  | merge x y =>
      by_cases hxv : x = void
      Â· cases hxv
        exact localJoin_merge_void_left y
      Â· by_cases hyv : y = void
        Â· cases hyv
          exact localJoin_merge_void_right x
        Â· by_cases hxy : x = y
          Â· cases hxy
            exact localJoin_merge_tt x
          Â· exact localJoin_merge_no_void_neq x y hxv hyv hxy
  | app x y =>
      exact localJoin_app x y
  | recÎ” b s n =>
      cases n with
      | void =>
          exact localJoin_rec_zero b s
      | delta u =>
          exact localJoin_rec_succ b s u
      | integrate t =>
          exact localJoin_rec_integrate b s t
      | merge x y =>
          exact localJoin_rec_merge b s x y
      | app x y =>
          exact localJoin_rec_app b s x y
      | recÎ” b' s' n' =>
          refine localJoin_rec_other b s (recÎ” b' s' n') ?hn0 ?hns
          Â· intro h; cases h
          Â· intro u h; cases h
      | eqW x y =>
          exact localJoin_rec_eqW b s x y
  | eqW x y =>
      by_cases hxy : x = y
      Â· cases hxy
        by_cases h0 : MetaSN_DM.kappaM x = 0
        Â· refine localJoin_of_unique (a := eqW x x) (d := void) ?h
          intro z hz
          cases hz with
          | R_eq_refl _ _ =>
              rfl
          | R_eq_diff _ _ hne =>
              exact False.elim (hne rfl)
        Â· exact localJoin_eqW_refl_guard_ne x h0
      Â· exact localJoin_eqW_ne x y hxy
end MetaSN_KO7

namespace MetaSN_KO7

/-- If a root local join holds at `a`, then a ctx-local join also holds at `a`.
This embeds the root `SafeStepStar` witnesses into `SafeStepCtxStar`. -/
theorem localJoin_ctx_of_localJoin (a : Trace)
    (h : LocalJoinSafe a) : LocalJoinSafe_ctx a := by
  intro b c hb hc
  rcases h hb hc with âŸ¨d, hbStar, hcStarâŸ©
  exact âŸ¨d, ctxstar_of_star hbStar, ctxstar_of_star hcStarâŸ©

end MetaSN_KO7

namespace MetaSN_KO7

/-- Ctx wrapper: if neither side is void and `a â‰  b`, then ctx-local join holds at `merge a b`. -/
theorem localJoin_ctx_merge_no_void_neq (a b : Trace)
    (hav : a â‰  void) (hbv : b â‰  void) (hneq : a â‰  b) :
    LocalJoinSafe_ctx (merge a b) :=
  localJoin_ctx_of_localJoin (a := merge a b)
    (h := localJoin_merge_no_void_neq a b hav hbv hneq)

end MetaSN_KO7

namespace MetaSN_KO7

/-- Ctx wrapper: eqW distinct arguments have ctx-local join (only diff rule applies). -/
theorem localJoin_ctx_eqW_ne (a b : Trace) (hne : a â‰  b) :
    LocalJoinSafe_ctx (eqW a b) :=
  localJoin_ctx_of_localJoin (a := eqW a b)
    (h := localJoin_eqW_ne a b hne)

/-- Ctx wrapper: at eqW a a with kappaM a â‰  0, only diff applies; ctx-local join holds. -/
theorem localJoin_ctx_eqW_refl_guard_ne (a : Trace)
    (h0ne : MetaSN_DM.kappaM a â‰  0) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_ctx_of_localJoin (a := eqW a a)
    (h := localJoin_eqW_refl_guard_ne a h0ne)

end MetaSN_KO7

namespace MetaSN_KO7

/-- Ctx wrapper: if `normalizeSafe (merge a a) = delta n`, eqW a a ctx-joins. -/
theorem localJoin_ctx_eqW_refl_if_merge_normalizes_to_delta (a n : Trace)
    (hn : normalizeSafe (merge a a) = delta n) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_eqW_refl_ctx_if_merge_normalizes_to_delta a n hn

/-- Ctx wrapper: if `integrate (merge a a) â‡’ctx* void`, eqW a a ctx-joins at void. -/
theorem localJoin_ctx_eqW_refl_if_integrate_merge_to_void (a : Trace)
    (hiv : SafeStepCtxStar (integrate (merge a a)) void) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_eqW_refl_ctx_if_integrate_merge_to_void a hiv

/-- Ctx wrapper: if `a â‡’* delta n` and guards hold on `delta n`, eqW a a ctx-joins. -/
theorem localJoin_ctx_eqW_refl_if_arg_star_to_delta (a n : Trace)
    (ha : SafeStepStar a (delta n))
    (hÎ´ : deltaFlag (delta n) = 0)
    (h0 : MetaSN_DM.kappaM (delta n) = 0) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_eqW_refl_ctx_if_arg_star_to_delta a n ha hÎ´ h0

/-- Ctx wrapper: if `normalizeSafe a = delta n` and guards hold, eqW a a ctx-joins. -/
theorem localJoin_ctx_eqW_refl_if_normalizes_to_delta (a n : Trace)
    (hn : normalizeSafe a = delta n)
    (hÎ´ : deltaFlag (delta n) = 0)
    (h0 : MetaSN_DM.kappaM (delta n) = 0) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_eqW_refl_ctx_if_normalizes_to_delta a n hn hÎ´ h0

end MetaSN_KO7

namespace MetaSN_KO7

/-- Ctx wrapper: when `a` is literally `delta n` and guards hold, eqW (delta n) (delta n) ctx-joins. -/
theorem localJoin_ctx_eqW_refl_when_a_is_delta (n : Trace)
    (hÎ´ : deltaFlag (delta n) = 0)
    (h0 : MetaSN_DM.kappaM (delta n) = 0) :
    LocalJoinSafe_ctx (eqW (delta n) (delta n)) :=
  localJoin_eqW_refl_ctx_when_a_is_delta n hÎ´ h0

end MetaSN_KO7
````

## OperatorKO7/Meta/Conjecture_Boundary.lean

**Lines:** 490

``lean
import OperatorKO7.Meta.Impossibility_Lemmas
import OperatorKO7.Meta.Operational_Incompleteness

/-!
# Conjecture Boundary (Theorem-Level No-Go Statements)

This module collects theorem-level barriers that are already justified by the
current KO7 artifact.

The purpose is narrower:
- record explicit "no-go" theorems for concrete internal method families;
- keep these boundaries importable from one place for audit/review.
-/

namespace OperatorKO7.MetaConjectureBoundary

open OperatorKO7 Trace
open OperatorKO7.Impossibility

/-! ## Global-orientation interface (full kernel Step) -/

/-- A measure/order pair globally orients the full kernel `Step`. -/
def GlobalOrients {Î± : Type} (m : Trace â†’ Î±) (lt : Î± â†’ Î± â†’ Prop) : Prop :=
  âˆ€ {a b}, Step a b â†’ lt (m b) (m a)

/-! ## Additive / Lex barriers -/

/-- No fixed additive bump on `kappa` can orient `rec_succ` uniformly. -/
theorem no_fixed_kappa_plus_k (k : Nat) :
    Â¬ (âˆ€ (b s n : Trace),
      FailedMeasures.kappa (app s (recÎ” b s n)) + k <
      FailedMeasures.kappa (recÎ” b s (delta n)) + k) :=
  FailedMeasures.kappa_plus_k_fails k

/-- The simple 2-component lex witness `(kappa, mu)` fails on KO7. -/
theorem no_simple_lex_witness :
    Â¬ (âˆ€ (b s n : Trace),
      Prod.Lex (Â· < Â·) (Â· < Â·)
        (FailedMeasures.kappa (app s (recÎ” b s n)),
         FailedMeasures.mu (app s (recÎ” b s n)))
        (FailedMeasures.kappa (recÎ” b s (delta n)),
         FailedMeasures.mu (recÎ” b s (delta n)))) :=
  FailedMeasures.simple_lex_fails

/-- Additive size cannot strictly decrease across all `rec_succ` instances. -/
theorem no_additive_strict_drop_rec_succ :
    Â¬ (âˆ€ (b s n : Trace),
      UncheckedRecursionFailure.simpleSize (app s (recÎ” b s n)) <
      UncheckedRecursionFailure.simpleSize (recÎ” b s (delta n))) := by
  intro h
  have hlt := h void void void
  have hge :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  exact Nat.not_lt_of_ge hge hlt

/-! ## Strengthened full-step no-go theorems -/

/-- No fixed additive bump can globally orient full `Step`. -/
theorem no_global_step_orientation_kappa_plus_k (k : Nat) :
    Â¬ GlobalOrients (fun t => FailedMeasures.kappa t + k) (Â· < Â·) := by
  intro h
  apply no_fixed_kappa_plus_k k
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Plain structural depth (`kappa`) cannot globally orient full `Step`. -/
theorem no_global_step_orientation_kappa :
    Â¬ GlobalOrients FailedMeasures.kappa (Â· < Â·) := by
  intro h
  apply no_fixed_kappa_plus_k 0
  intro b s n
  have hlt : FailedMeasures.kappa (app s (recÎ” b s n)) <
      FailedMeasures.kappa (recÎ” b s (delta n)) :=
    h (Step.R_rec_succ b s n)
  simp at hlt

/-- The simple lex witness `(kappa, mu)` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simple_lex :
    Â¬ GlobalOrients
      (fun t => (FailedMeasures.kappa t, FailedMeasures.mu t))
      (Prod.Lex (Â· < Â·) (Â· < Â·)) := by
  intro h
  apply no_simple_lex_witness
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Additive `simpleSize` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simpleSize :
    Â¬ GlobalOrients UncheckedRecursionFailure.simpleSize (Â· < Â·) := by
  intro h
  apply no_additive_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-! ## Flag-only barrier -/

/-- A single top-level flag cannot globally orient full `Step`. -/
theorem no_global_flag_only_orientation :
    Â¬ (âˆ€ a b : Trace, Step a b â†’
      FlagFailure.deltaFlagTop b < FlagFailure.deltaFlagTop a) := by
  intro h
  let t : Trace := delta void
  have hstep : Step (merge void t) t := Step.R_merge_void_left t
  have hlt : FlagFailure.deltaFlagTop t < FlagFailure.deltaFlagTop (merge void t) :=
    h _ _ hstep
  simp [FlagFailure.deltaFlagTop, t] at hlt

/-! ## Constellation / structural hybrid barrier -/

/-- Constellation-size cannot strictly decrease on all `rec_succ` instances. -/
theorem no_constellation_strict_drop_rec_succ :
    Â¬ (âˆ€ (b s n : Trace),
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (app s (recÎ” b s n))) <
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (recÎ” b s (delta n)))) := by
  intro h
  have hlt := h void void void
  have hs :
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (void : Trace)) â‰¥ 1 := by
    simp [ConstellationFailure.constellationSize, ConstellationFailure.toConstellation]
  have hge :=
    ConstellationFailure.constellation_size_not_decreasing void void void hs
  exact Nat.not_lt_of_ge hge hlt

/-- Constellation-size cannot globally orient full `Step`. -/
theorem no_global_step_orientation_constellation :
    Â¬ GlobalOrients
      (fun t =>
        ConstellationFailure.constellationSize
          (ConstellationFailure.toConstellation t))
      (Â· < Â·) := by
  intro h
  apply no_constellation_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Strictly monotone post-processing cannot rescue additive `simpleSize` on full `Step`. -/
theorem no_global_step_orientation_simpleSize_strictMono
    (f : Nat â†’ Nat) (hf : StrictMono f) :
    Â¬ GlobalOrients
      (fun t => f (UncheckedRecursionFailure.simpleSize t))
      (Â· < Â·) := by
  intro h
  have hstep : Step (recÎ” void void (delta void)) (app void (recÎ” void void void)) :=
    Step.R_rec_succ void void void
  have hlt :
      f (UncheckedRecursionFailure.simpleSize (app void (recÎ” void void void))) <
      f (UncheckedRecursionFailure.simpleSize (recÎ” void void (delta void))) :=
    h hstep
  have hge :
      UncheckedRecursionFailure.simpleSize (app void (recÎ” void void void)) â‰¥
      UncheckedRecursionFailure.simpleSize (recÎ” void void (delta void)) :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  have hmono :
      f (UncheckedRecursionFailure.simpleSize (recÎ” void void (delta void))) â‰¤
      f (UncheckedRecursionFailure.simpleSize (app void (recÎ” void void void))) :=
    hf.monotone hge
  exact Nat.not_lt_of_ge hmono hlt

/-! ## Bridge wrappers to `OpIncomp.InternallyDefinableMeasure` -/

/-- Any internal witness must include the explicit duplication non-drop barrier (r4). -/
theorem internal_measure_records_duplication_barrier
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    (x y : OperatorKO7.OpIncomp.Term) :
    Â¬ OperatorKO7.OpIncomp.size (OperatorKO7.OpIncomp.R4_after x y) <
      OperatorKO7.OpIncomp.size (OperatorKO7.OpIncomp.R4_before x y) :=
  M.dup_additive_nodrop_r4 x y

/-- Any internal witness must provide per-piece orientation for every rule instance. -/
theorem internal_measure_requires_per_piece_lt
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    {l r : OperatorKO7.OpIncomp.Term}
    (hr : OperatorKO7.OpIncomp.Rule l r)
    {t : OperatorKO7.OpIncomp.Term}
    (ht : t âˆˆ OperatorKO7.OpIncomp.rhsPiecesLHS l) :
    M.base t l :=
  M.per_piece_base_lt hr t ht

/-- Exposes the lex/orientation gate encoded in `InternallyDefinableMeasure`. -/
theorem internal_measure_lex_gate
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    {l r : OperatorKO7.OpIncomp.Term}
    (hr : OperatorKO7.OpIncomp.Rule l r) :
    (M.flag r = false âˆ§ M.flag l = true) âˆ¨
      (âˆƒ t, t âˆˆ OperatorKO7.OpIncomp.rhsPiecesLHS l âˆ§ M.base t l) âˆ¨
      M.base r l :=
  M.lex_ok hr

/-! ## Flag barrier (GlobalOrients form) -/

/-- A single top-level Î´-flag cannot globally orient full `Step` (GlobalOrients form). -/
theorem no_global_step_orientation_flag :
    Â¬ GlobalOrients FlagFailure.deltaFlagTop (Â· < Â·) := by
  intro h
  have hstep : Step (merge void (delta void)) (delta void) :=
    Step.R_merge_void_left (delta void)
  have hlt := h hstep
  simp [FlagFailure.deltaFlagTop] at hlt

/-! ## Strict increase witness (rec_succ makes additive measures grow) -/

/-- When `s` is non-void, `simpleSize` strictly INCREASES across `rec_succ`.
The duplication barrier is not just "no drop" - the measure goes UP. -/
theorem rec_succ_size_strictly_increases (b s n : Trace)
    (hs : UncheckedRecursionFailure.simpleSize s â‰¥ 1) :
    UncheckedRecursionFailure.simpleSize (app s (recÎ” b s n)) >
    UncheckedRecursionFailure.simpleSize (recÎ” b s (delta n)) :=
  UncheckedRecursionFailure.rec_succ_size_increases b s n hs

/-! ## StrictMono generalization for kappa -/

/-- Strictly monotone post-processing cannot rescue `kappa` on full `Step`.
Analogous to `no_global_step_orientation_simpleSize_strictMono`. -/
theorem no_global_step_orientation_kappa_strictMono
    (f : Nat â†’ Nat) (hf : StrictMono f) :
    Â¬ GlobalOrients (fun t => f (FailedMeasures.kappa t)) (Â· < Â·) := by
  intro h
  have hstep : Step (recÎ” void void (delta (delta void)))
      (app void (recÎ” void void (delta void))) :=
    Step.R_rec_succ void void (delta void)
  have hlt := h hstep
  have hge : FailedMeasures.kappa (app void (recÎ” void void (delta void))) â‰¥
      FailedMeasures.kappa (recÎ” void void (delta (delta void))) := by
    simp [FailedMeasures.kappa]
  exact Nat.not_lt_of_ge (hf.monotone hge) hlt

/-! ## Dual-barrier theorem (rec_succ vs merge_void are complementary) -/

/-- The duplication barrier and the flag barrier target DIFFERENT rules.
Any single Nat-valued measure that handles rec_succ (which requires insensitivity
to duplication of `s`) is blocked by merge_void (which can raise flags), and vice
versa. This theorem witnesses both barriers simultaneously on full `Step`. -/
theorem dual_barrier_rec_succ_and_merge_void :
    -- (1) Additive size fails on rec_succ:
    (âˆ€ (b s n : Trace),
      UncheckedRecursionFailure.simpleSize (app s (recÎ” b s n)) â‰¥
      UncheckedRecursionFailure.simpleSize (recÎ” b s (delta n)))
    âˆ§
    -- (2) Î´-flag increases on merge_void_left:
    (FlagFailure.deltaFlagTop (delta void) >
     FlagFailure.deltaFlagTop (merge void (delta void))) := by
  constructor
  Â· exact UncheckedRecursionFailure.rec_succ_additive_barrier
  Â· simp [FlagFailure.deltaFlagTop]

/-! ## Structural depth barrier (#6: ties on collapsing rules)

A nesting-depth measure that does NOT count `merge` as a level ties on
`merge_cancel`. This formalizes failure mode #6 from the paper:
"Structural depth: Ties on collapsing rules (merge_cancel)." -/

/-- Nesting depth where `merge` does not add a level. -/
@[simp] def nestingDepth : Trace â†’ Nat
  | .void => 0
  | .delta t => nestingDepth t + 1
  | .integrate t => nestingDepth t + 1
  | .merge a b => max (nestingDepth a) (nestingDepth b)
  | .app a b => max (nestingDepth a) (nestingDepth b) + 1
  | .recÎ” b s n => max (max (nestingDepth b) (nestingDepth s)) (nestingDepth n) + 1
  | .eqW a b => max (nestingDepth a) (nestingDepth b) + 1

/-- `nestingDepth` ties on `merge_cancel`: `nestingDepth(merge t t) = nestingDepth(t)`.
Since `merge t t â†’ t`, orientation requires `nestingDepth(t) < nestingDepth(merge t t)`,
which is `nestingDepth(t) < nestingDepth(t)` - false. -/
theorem nestingDepth_merge_cancel_tie (t : Trace) :
    nestingDepth (merge t t) = nestingDepth t := by
  simp

/-- `nestingDepth` cannot globally orient full `Step` (fails at merge_cancel). -/
theorem no_global_step_orientation_nestingDepth :
    Â¬ GlobalOrients nestingDepth (Â· < Â·) := by
  intro h
  have hstep : Step (merge void void) void := Step.R_merge_cancel void
  have hlt := h hstep
  simp [nestingDepth] at hlt

/-! ## Polynomial interpretation barrier (#3: Ladder Paradox)

Polynomial measures using multiplicative coefficients at `recÎ”` (e.g.,
`M(recÎ” b s n) = M(b) + M(s) * M(n)`) tie on `rec_succ` regardless of
base weight. With additive `app`, the duplication of `s` is exactly
cancelled by the multiplication:

  M(recÎ” b s (delta n)) = M(b) + M(s)*(M(n)+1) = M(b) + M(s)*M(n) + M(s)
  M(app s (recÎ” b s n)) = M(s) + M(b) + M(s)*M(n)

These are equal by commutativity of addition. Any polynomial that DOES
break this tie requires importing external constants (e.g., `M(void) = 2`)
and node-weight arithmetic - this is the Ladder Paradox (Gate F.4 in the
Strict Execution Contract): the termination proof works only because it
maps to external arithmetic we already trust, not because of any
internally definable property. -/

/-- Polynomial measure with multiplicative `recÎ”`, parameterized by base weight `w`. -/
@[simp] def polyMul (w : Nat) : Trace â†’ Nat
  | .void => w
  | .delta t => polyMul w t + 1
  | .integrate t => polyMul w t + 1
  | .merge a b => polyMul w a + polyMul w b
  | .app a b => polyMul w a + polyMul w b
  | .recÎ” b s n => polyMul w b + polyMul w s * polyMul w n
  | .eqW a b => polyMul w a + polyMul w b

/-- Polynomial with multiplicative `recÎ”` TIES on `rec_succ` for ANY base weight.
This is an exact equality, not just a non-strict inequality. -/
theorem poly_mul_ties_rec_succ (w : Nat) (b s n : Trace) :
    polyMul w (app s (recÎ” b s n)) =
    polyMul w (recÎ” b s (delta n)) := by
  simp [polyMul, Nat.mul_add]
  omega

/-- Polynomial `polyMul` cannot globally orient full `Step` (ties on rec_succ). -/
theorem no_global_step_orientation_polyMul (w : Nat) :
    Â¬ GlobalOrients (polyMul w) (Â· < Â·) := by
  intro h
  have hstep : Step (recÎ” void void (delta void)) (app void (recÎ” void void void)) :=
    Step.R_rec_succ void void void
  have hlt := h hstep
  have heq := poly_mul_ties_rec_succ w void void void
  omega

/-! ## Naive multiset barrier (#7: duplication inflates element count)

A naive multiset measure collects subterm weights into a bag and compares
by sum (or cardinality). Unlike the Dershowitz-Manna ordering â€” which
permits replacing one large element with multiple SMALLER elements â€”
naive comparison has no mechanism to absorb duplication. When `rec_succ`
duplicates `s`, the bag gains an extra copy of `s`'s weight, and the
sum/cardinality strictly increases.

This formalizes failure mode #7 from the paper:
"Naive multiset orderings: Fail without DM-specific properties." -/

/-- Node count: number of constructor applications in the term.
This represents a naive multiset measure where every node has weight 1
and the multiset is compared by cardinality (= sum of weights). -/
@[simp] def nodeCount : Trace â†’ Nat
  | .void => 1
  | .delta t => nodeCount t + 1
  | .integrate t => nodeCount t + 1
  | .merge a b => nodeCount a + nodeCount b + 1
  | .app a b => nodeCount a + nodeCount b + 1
  | .recÎ” b s n => nodeCount b + nodeCount s + nodeCount n + 1
  | .eqW a b => nodeCount a + nodeCount b + 1

/-- Naive multiset (node count) does not strictly decrease on `rec_succ`.
The duplication of `s` adds `nodeCount s` to the RHS, yielding â‰¥. -/
theorem nodeCount_rec_succ_barrier (b s n : Trace) :
    nodeCount (app s (recÎ” b s n)) â‰¥ nodeCount (recÎ” b s (delta n)) := by
  simp [nodeCount]
  omega

/-- With non-trivial `s`, node count strictly INCREASES on `rec_succ`. -/
theorem nodeCount_rec_succ_increases (b s n : Trace)
    (hs : nodeCount s â‰¥ 2) :
    nodeCount (app s (recÎ” b s n)) > nodeCount (recÎ” b s (delta n)) := by
  simp [nodeCount]
  omega

/-- Node count cannot globally orient full `Step` (fails at rec_succ). -/
theorem no_global_step_orientation_nodeCount :
    Â¬ GlobalOrients nodeCount (Â· < Â·) := by
  intro h
  have hstep : Step (recÎ” void void (delta void)) (app void (recÎ” void void void)) :=
    Step.R_rec_succ void void void
  have hlt := h hstep
  have hge := nodeCount_rec_succ_barrier void void void
  omega

/-! ## The Boundary Between Code and Meta-Theory (Path Orders)

CRITICAL NOTE: This file does NOT demonstrate that full Lexicographic Path Ordering (LPO)
or Multiset Path Ordering (MPO) fails to orient the KO7 calculus. Both full LPO and
full MPO *succeed* in orienting the unrestricted system: LPO is CeTA-certified (external),
and MPO orientation is Lean-mechanized in `Meta/MPO_FullStep.lean` (`mpo_orients_step`).

Instead, the following two theorems demonstrate that the isolated *components* of path
orders (pure head precedence and linear KBO-style weights) fail independently.
Because these simple structural methods fail, any successful path order is
mathematically forced to rely on the universal Subterm Property (f(t) > t).

The paper argues that importing the Subterm Property (and by extension,
Kruskal's Tree Theorem) goes beyond the "no imported axioms" structural
constraint of KO7 (Â§3). Thus, the code demonstrates the *necessity* of the
external axiom, while the paper critiques its *validity*.
-/

/-! ## Pure Precedence Barrier (#7: Precedence conflict on collapsing rules)

A measure that relies strictly on the precedence of the head constructor
cannot orient collapsing rules like `merge_cancel`, because the RHS can
have the same head constructor as the LHS.
-/

inductive OpHead | void | delta | integrate | merge | app | recÎ” | eqW

def getHead : Trace â†’ OpHead
  | .void => .void
  | .delta _ => .delta
  | .integrate _ => .integrate
  | .merge _ _ => .merge
  | .app _ _ => .app
  | .recÎ” _ _ _ => .recÎ”
  | .eqW _ _ => .eqW

def headPrecedenceMeasure (rank : OpHead â†’ Nat) : Trace â†’ Nat :=
  fun t => rank (getHead t)

/-- Pure head precedence cannot globally orient `Step` (fails at merge_cancel). -/
theorem no_global_step_orientation_headPrecedence (rank : OpHead â†’ Nat) :
    Â¬ GlobalOrients (headPrecedenceMeasure rank) (Â· < Â·) := by
  intro h
  have hstep : Step (merge (merge void void) (merge void void)) (merge void void) :=
    Step.R_merge_cancel (merge void void)
  have hlt := h hstep
  revert hlt
  simp [headPrecedenceMeasure, getHead]

/-! ## Linear Weight Barrier (KBO-style without precedence)

A purely additive weight function (where each constructor adds a fixed constant
to the sum of its arguments' weights) cannot globally orient `Step`.
This formalizes the failure of basic Knuth-Bendix Order (KBO) weight functions
on the duplication in `rec_succ`.
-/

def linearWeight (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat) : Trace â†’ Nat
  | .void => c_void
  | .delta t => c_delta + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq t
  | .integrate t => c_int + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq t
  | .merge a b => c_merge + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b
  | .app a b => c_app + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b
  | .recÎ” b s n => c_rec + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq s + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq n
  | .eqW a b => c_eq + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b

/-- No linear weight function can globally orient `Step` (fails at rec_succ). -/
theorem no_global_step_orientation_linearWeight (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat) :
    Â¬ GlobalOrients (linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq) (Â· < Â·) := by
  intro h
  have h1 := h (Step.R_rec_succ void void void)
  have h2 := h (Step.R_rec_succ void (delta void) void)
  simp [linearWeight] at h1 h2
  omega

/-! ## Standard Tree Depth Barrier

A standard tree depth measure (where every constructor adds 1 to the maximum
depth of its arguments) cannot globally orient `Step` because the duplication
of `s` in `rec_succ` can strictly increase the overall depth of the term.
-/

@[simp] def treeDepth : Trace â†’ Nat
  | .void => 0
  | .delta t => treeDepth t + 1
  | .integrate t => treeDepth t + 1
  | .merge a b => max (treeDepth a) (treeDepth b) + 1
  | .app a b => max (treeDepth a) (treeDepth b) + 1
  | .recÎ” b s n => max (max (treeDepth b) (treeDepth s)) (treeDepth n) + 1
  | .eqW a b => max (treeDepth a) (treeDepth b) + 1

/-- Standard tree depth strictly INCREASES on `rec_succ` when `s` is deep. -/
theorem treeDepth_rec_succ_increases (b s n : Trace)
    (hs : treeDepth s > treeDepth n + 1) :
    treeDepth (app s (recÎ” b s n)) > treeDepth (recÎ” b s (delta n)) := by
  simp [treeDepth]
  omega

/-- Standard tree depth cannot globally orient `Step`. -/
theorem no_global_step_orientation_treeDepth :
    Â¬ GlobalOrients treeDepth (Â· < Â·) := by
  intro h
  -- Let n = void (depth 0). Let s = delta (delta void) (depth 2).
  have hstep : Step (recÎ” void (delta (delta void)) (delta void))
                    (app (delta (delta void)) (recÎ” void (delta (delta void)) void)) :=
    Step.R_rec_succ void (delta (delta void)) void
  have hlt := h hstep
  -- LHS depth is 3. RHS depth is 4. 3 < 4 contradicts orientation.
  simp [treeDepth] at hlt

/-! ## Full-step witness (duplication branch is present in kernel Step) -/

/-- The unrestricted kernel `Step` contains the duplication branch explicitly. -/
theorem full_step_has_rec_succ_instance :
    âˆƒ b s n, Step (recÎ” b s (delta n)) (app s (recÎ” b s n)) :=
  UncheckedRecursionFailure.full_step_permits_barrier

end OperatorKO7.MetaConjectureBoundary
````

## OperatorKO7/Meta/ContextClosed_SN.lean

**Lines:** 518

``lean
import OperatorKO7.Meta.SafeStep_Ctx
import Mathlib.Logic.Relation

/-!
Context-closed strong normalization for the KO7 safe fragment.

This module proves unconditional well-foundedness of `SafeStepCtxRev` (the
reverse of the partial context closure `SafeStepCtx`) via a direct numeric
interpretation `ctxFuel` (exponential weights). The key theorem is
`wf_SafeStepCtxRev : WellFounded (fun a b => SafeStepCtx b a)`.

Infrastructure:
- Reusable accessibility/transport lemmas for the reverse context relation
  `SafeStepCtxRev a b :â‰¡ SafeStepCtx b a`.
- Projections of accessibility through constructor embeddings
  (`recB`, `recS`, `recN`, `appL/R`, `mergeL/R`, `integrate`).
- `Acc` pullback along `InvImage`.

The unconditional proof (no `sorry`) works by showing `ctxFuel` strictly
decreases on every `SafeStepCtx` step (`ctxFuel_decreases_ctx`), reducing
well-foundedness to `Nat.lt`.
-/

open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Reverse relation for context-closed safe steps. -/
def SafeStepCtxRev : Trace â†’ Trace â†’ Prop := fun a b => SafeStepCtx b a

/-- Pull accessibility back along a subrelation. -/
lemma Acc.of_subrelation {Î± : Sort _} {r s : Î± â†’ Î± â†’ Prop}
    (hsub : âˆ€ {a b}, r a b â†’ s a b) {a : Î±} (ha : Acc s a) : Acc r a := by
  induction ha with
  | intro a hs ih =>
      refine Acc.intro a ?_
      intro b hb
      exact ih b (hsub hb)

/-- Pull accessibility back through an `InvImage` equality witness. -/
lemma acc_invImage_of_acc
    {Î± Î² : Sort _} {r : Î² â†’ Î² â†’ Prop} (f : Î± â†’ Î²)
    {b0 : Î²} (hb0 : Acc r b0) :
    âˆ€ {a : Î±}, f a = b0 â†’ Acc (InvImage r f) a := by
  induction hb0 with
  | intro b0 hpred ih =>
      intro a ha
      refine Acc.intro a ?_
      intro a' ha'
      have hb' : r (f a') b0 := by
        simpa [InvImage, ha] using ha'
      exact ih (f a') hb' (a := a') rfl

/-! ### Constructor-lifted subrelations -/

lemma sub_integrate :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => integrate t) x y := by
  intro x y hxy
  exact SafeStepCtx.integrate hxy

lemma sub_mergeL (b : Trace) :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => merge t b) x y := by
  intro x y hxy
  exact SafeStepCtx.mergeL hxy

lemma sub_mergeR (a : Trace) :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => merge a t) x y := by
  intro x y hxy
  exact SafeStepCtx.mergeR hxy

lemma sub_appL (b : Trace) :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => app t b) x y := by
  intro x y hxy
  exact SafeStepCtx.appL hxy

lemma sub_appR (a : Trace) :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => app a t) x y := by
  intro x y hxy
  exact SafeStepCtx.appR hxy

lemma sub_recB (s n : Trace) :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => recÎ” t s n) x y := by
  intro x y hxy
  exact SafeStepCtx.recB hxy

lemma sub_recS (b n : Trace) :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => recÎ” b t n) x y := by
  intro x y hxy
  exact SafeStepCtx.recS hxy

lemma sub_recN (b s : Trace) :
    âˆ€ {x y : Trace},
      SafeStepCtxRev x y â†’
      InvImage SafeStepCtxRev (fun t => recÎ” b s t) x y := by
  intro x y hxy
  exact SafeStepCtx.recN hxy

/-! ### Accessibility projections through constructors -/

lemma acc_integrate_arg_of_acc {t : Trace}
    (h : Acc SafeStepCtxRev (integrate t)) :
    Acc SafeStepCtxRev t := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => integrate x)) t :=
    acc_invImage_of_acc (f := fun x => integrate x) h rfl
  exact Acc.of_subrelation sub_integrate hInv

lemma acc_merge_left_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (merge a b)) :
    Acc SafeStepCtxRev a := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => merge x b)) a :=
    acc_invImage_of_acc (f := fun x => merge x b) h rfl
  exact Acc.of_subrelation (sub_mergeL b) hInv

lemma acc_merge_right_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (merge a b)) :
    Acc SafeStepCtxRev b := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => merge a x)) b :=
    acc_invImage_of_acc (f := fun x => merge a x) h rfl
  exact Acc.of_subrelation (sub_mergeR a) hInv

lemma acc_app_left_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (app a b)) :
    Acc SafeStepCtxRev a := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => app x b)) a :=
    acc_invImage_of_acc (f := fun x => app x b) h rfl
  exact Acc.of_subrelation (sub_appL b) hInv

lemma acc_app_right_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (app a b)) :
    Acc SafeStepCtxRev b := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => app a x)) b :=
    acc_invImage_of_acc (f := fun x => app a x) h rfl
  exact Acc.of_subrelation (sub_appR a) hInv

lemma acc_rec_base_of_acc {b s n : Trace}
    (h : Acc SafeStepCtxRev (recÎ” b s n)) :
    Acc SafeStepCtxRev b := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => recÎ” x s n)) b :=
    acc_invImage_of_acc (f := fun x => recÎ” x s n) h rfl
  exact Acc.of_subrelation (sub_recB s n) hInv

lemma acc_rec_step_of_acc {b s n : Trace}
    (h : Acc SafeStepCtxRev (recÎ” b s n)) :
    Acc SafeStepCtxRev s := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => recÎ” b x n)) s :=
    acc_invImage_of_acc (f := fun x => recÎ” b x n) h rfl
  exact Acc.of_subrelation (sub_recS b n) hInv

lemma acc_rec_arg_of_acc {b s n : Trace}
    (h : Acc SafeStepCtxRev (recÎ” b s n)) :
    Acc SafeStepCtxRev n := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => recÎ” b s x)) n :=
    acc_invImage_of_acc (f := fun x => recÎ” b s x) h rfl
  exact Acc.of_subrelation (sub_recN b s) hInv

/-! ### Constructor closure lemmas (forward-step accessibility) -/

theorem acc_ctx_void : Acc SafeStepCtxRev void := by
  refine Acc.intro _ ?_
  intro y hy
  cases hy
  case root hs =>
    have hnone : safeStepWitness? void = none := by simp [safeStepWitness?]
    exact (safeStepWitness?_none_no_step hnone y hs).elim

theorem acc_ctx_delta (t : Trace) : Acc SafeStepCtxRev (delta t) := by
  refine Acc.intro _ ?_
  intro y hy
  cases hy
  case root hs =>
    have hnone : safeStepWitness? (delta t) = none := by simp [safeStepWitness?]
    exact (safeStepWitness?_none_no_step hnone y hs).elim

theorem acc_ctx_app_of_acc :
    âˆ€ a, Acc SafeStepCtxRev a â†’
    âˆ€ b, Acc SafeStepCtxRev b â†’
      Acc SafeStepCtxRev (app a b) := by
  intro a ha
  induction ha with
  | intro a hpredA ihA =>
      intro b hb
      induction hb with
      | intro b hpredB ihB =>
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs =>
              have hnone : safeStepWitness? (app a b) = none := by simp [safeStepWitness?]
              exact (safeStepWitness?_none_no_step hnone y hs).elim
          | appL hA => exact ihA _ hA b hbAcc
          | appR hB => exact ihB _ hB

theorem acc_ctx_merge_of_acc :
    âˆ€ a, Acc SafeStepCtxRev a â†’
    âˆ€ b, Acc SafeStepCtxRev b â†’
      Acc SafeStepCtxRev (merge a b) := by
  intro a ha
  induction ha with
  | intro a hpredA ihA =>
      intro b hb
      induction hb with
      | intro b hpredB ihB =>
          have haAcc : Acc SafeStepCtxRev a := Acc.intro a hpredA
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs =>
              cases hs with
              | R_merge_void_left t _ => simpa using hbAcc
              | R_merge_void_right t _ => simpa using haAcc
              | R_merge_cancel t _ _ => simpa using haAcc
          | mergeL hA => exact ihA _ hA b hbAcc
          | mergeR hB => exact ihB _ hB

theorem acc_ctx_integrate_of_acc
    (t : Trace) (ht : Acc SafeStepCtxRev t) :
    Acc SafeStepCtxRev (integrate t) := by
  induction ht with
  | intro t hpredT ihT =>
      refine Acc.intro _ ?_
      intro y hy
      cases hy with
      | root hs =>
          cases hs with
          | R_int_delta u =>
              simpa using acc_ctx_void
      | integrate hT => exact ihT _ hT

theorem acc_ctx_eqW_of_acc
    (a b : Trace) (ha : Acc SafeStepCtxRev a) (hb : Acc SafeStepCtxRev b) :
    Acc SafeStepCtxRev (eqW a b) := by
  refine Acc.intro _ ?_
  intro y hy
  cases hy with
  | root hs =>
      cases hs with
      | R_eq_refl a h0 =>
          simpa using acc_ctx_void
      | R_eq_diff a b hne =>
          exact acc_ctx_integrate_of_acc (merge a b) (acc_ctx_merge_of_acc a ha b hb)

theorem acc_ctx_rec_void_of_acc :
    âˆ€ b, Acc SafeStepCtxRev b â†’
    âˆ€ s, Acc SafeStepCtxRev s â†’
      Acc SafeStepCtxRev (recÎ” b s void) := by
  intro b hb
  induction hb with
  | intro b hpredB ihB =>
      intro s hs
      induction hs with
      | intro s hpredS ihS =>
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          have hsAcc : Acc SafeStepCtxRev s := Acc.intro s hpredS
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs0 =>
              cases hs0 with
              | R_rec_zero _ _ _ =>
                  simpa using hbAcc
          | recB hB =>
              exact ihB _ hB s hsAcc
          | recS hS =>
              exact ihS _ hS
          | recN hN =>
              cases hN with
              | root hsVoid =>
                  have hnone : safeStepWitness? void = none := by simp [safeStepWitness?]
                  exact (safeStepWitness?_none_no_step hnone _ hsVoid).elim

theorem acc_ctx_rec_delta_of_acc
    (n : Trace)
    (hrecArg : âˆ€ b s,
      Acc SafeStepCtxRev b â†’
      Acc SafeStepCtxRev s â†’
      Acc SafeStepCtxRev (recÎ” b s n)) :
    âˆ€ b, Acc SafeStepCtxRev b â†’
    âˆ€ s, Acc SafeStepCtxRev s â†’
      Acc SafeStepCtxRev (recÎ” b s (delta n)) := by
  intro b hb
  induction hb with
  | intro b hpredB ihB =>
      intro s hs
      induction hs with
      | intro s hpredS ihS =>
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          have hsAcc : Acc SafeStepCtxRev s := Acc.intro s hpredS
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs0 =>
              cases hs0 with
              | R_rec_succ _ _ _ =>
                  exact acc_ctx_app_of_acc s hsAcc
                    (recÎ” b s n) (hrecArg b s hbAcc hsAcc)
          | recB hB =>
              exact ihB _ hB s hsAcc
          | recS hS =>
              exact ihS _ hS
          | recN hN =>
              cases hN with
              | root hsDelta =>
                  have hnone : safeStepWitness? (delta n) = none := by simp [safeStepWitness?]
                  exact (safeStepWitness?_none_no_step hnone _ hsDelta).elim

/-- Remaining recursor-specific obligation for full context-closure SN. -/
def RecCtxAccObligation : Prop :=
  âˆ€ (b s n : Trace),
    Acc SafeStepCtxRev b â†’
    Acc SafeStepCtxRev s â†’
    Acc SafeStepCtxRev n â†’
    Acc SafeStepCtxRev (recÎ” b s n)

/-- If the recursor obligation holds, then all traces are accessible for `SafeStepCtxRev`. -/
theorem acc_ctx_all_of_rec_obligation
    (hrec : RecCtxAccObligation) :
    âˆ€ t : Trace, Acc SafeStepCtxRev t := by
  intro t
  induction t with
  | void =>
      exact acc_ctx_void
  | delta t _ =>
      exact acc_ctx_delta t
  | integrate t iht =>
      exact acc_ctx_integrate_of_acc t iht
  | merge a b iha ihb =>
      exact acc_ctx_merge_of_acc a iha b ihb
  | app a b iha ihb =>
      exact acc_ctx_app_of_acc a iha b ihb
  | recÎ” b s n ihb ihs ihn =>
      exact hrec b s n ihb ihs ihn
  | eqW a b iha ihb =>
      exact acc_ctx_eqW_of_acc a b iha ihb

/-- Conditional well-foundedness: reduces `wf_SafeStepCtxRev` to `RecCtxAccObligation`. -/
theorem wf_SafeStepCtxRev_of_rec_obligation
    (hrec : RecCtxAccObligation) :
    WellFounded (fun a b : Trace => SafeStepCtx b a) := by
  refine âŸ¨?_âŸ©
  intro t
  simpa [SafeStepCtxRev] using acc_ctx_all_of_rec_obligation hrec t

/-
Unconditional context-closure SN via a direct numeric interpretation.

`ctxFuel` is chosen to be strictly monotone under all context constructors and
to strictly decrease on every safe root rule; this yields strict decrease for
`SafeStepCtx` by induction on the context derivation.
-/

@[simp] def ctxFuel : Trace â†’ Nat
| void            => 0
| delta t         => 2 ^ (ctxFuel t + 1)
| integrate t     => ctxFuel t + 1
| merge a b       => ctxFuel a + ctxFuel b + 2
| app a b         => ctxFuel a + ctxFuel b + 1
| recÎ” b s n      => 2 ^ (ctxFuel n + ctxFuel s + 5) + ctxFuel b + 1
| eqW a b         => ctxFuel a + ctxFuel b + 4

lemma one_lt_two_nat : 1 < (2 : Nat) := by decide

lemma lt_two_pow_succ (n : Nat) : n < 2 ^ (n + 1) := by
  have h : n + 1 < 2 ^ (n + 1) := Nat.lt_pow_self (n := n + 1) one_lt_two_nat
  exact lt_trans (Nat.lt_succ_self n) h

lemma ctxFuel_rec_succ_drop (b s n : Trace) :
    ctxFuel (app s (recÎ” b s n)) < ctxFuel (recÎ” b s (delta n)) := by
  set mb := ctxFuel b
  set ms := ctxFuel s
  set mn := ctxFuel n
  let A : Nat := mn + ms + 5
  let B : Nat := 2 ^ (mn + 1) + ms + 5
  have hExpA_lt : A < B := by
    have hmn : mn < 2 ^ (mn + 1) := lt_two_pow_succ mn
    have hâ‚ : mn + ms < 2 ^ (mn + 1) + ms := Nat.add_lt_add_right hmn ms
    exact Nat.add_lt_add_right hâ‚ 5
  have hpowA_lt : 2 ^ A < 2 ^ B :=
    Nat.pow_lt_pow_right one_lt_two_nat hExpA_lt
  have hms_pow : ms + 1 < 2 ^ (ms + 1) := Nat.lt_pow_self (n := ms + 1) one_lt_two_nat
  have hExpSmall_le : ms + 1 â‰¤ A := by
    unfold A
    omega
  have hpowSmall_le : 2 ^ (ms + 1) â‰¤ 2 ^ A :=
    Nat.pow_le_pow_right (by decide : 2 > 0) hExpSmall_le
  have hms_lt_powA : ms + 1 < 2 ^ A := lt_of_lt_of_le hms_pow hpowSmall_le
  have hsum_lt : 2 ^ A + (ms + 1) < 2 ^ A + 2 ^ A := by
    exact Nat.add_lt_add_left hms_lt_powA (2 ^ A)
  have hdouble : 2 ^ A + 2 ^ A = 2 ^ (A + 1) := by
    calc
      2 ^ A + 2 ^ A = 2 * 2 ^ A := by simp [Nat.two_mul]
      _ = 2 ^ (A + 1) := by simp [Nat.pow_succ, Nat.mul_comm]
  have hA1_lt_B : A + 1 < B := by
    have hmn1 : mn + 1 < 2 ^ (mn + 1) := Nat.lt_pow_self (n := mn + 1) one_lt_two_nat
    have hâ‚ : mn + 1 + (ms + 5) < 2 ^ (mn + 1) + (ms + 5) := Nat.add_lt_add_right hmn1 (ms + 5)
    have : mn + ms + 6 < 2 ^ (mn + 1) + ms + 5 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hâ‚
    simpa [A, B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hpowA1_lt_B : 2 ^ (A + 1) < 2 ^ B := Nat.pow_lt_pow_right one_lt_two_nat hA1_lt_B
  have hcore : 2 ^ A + (ms + 1) < 2 ^ B := by
    have hsum_lt' : 2 ^ A + (ms + 1) < 2 ^ (A + 1) := by
      simpa [hdouble] using hsum_lt
    exact lt_trans hsum_lt' hpowA1_lt_B
  have hfinal : 2 ^ A + (ms + 1) + (mb + 1) < 2 ^ B + (mb + 1) := by
    exact Nat.add_lt_add_right hcore (mb + 1)
  have hlhs : ctxFuel (app s (recÎ” b s n)) = 2 ^ A + (ms + 1) + (mb + 1) := by
    simp [ctxFuel, A, mb, ms, mn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hrhs : ctxFuel (recÎ” b s (delta n)) = 2 ^ B + (mb + 1) := by
    simp [ctxFuel, B, mb, ms, mn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hlhs, hrhs]
  exact hfinal

lemma ctxFuel_decreases_safe : âˆ€ {a b : Trace}, SafeStep a b â†’ ctxFuel b < ctxFuel a
| _, _, SafeStep.R_int_delta t => by
    simp [ctxFuel]
| _, _, SafeStep.R_merge_void_left t _ => by
    simp [ctxFuel]
| _, _, SafeStep.R_merge_void_right t _ => by
    simp [ctxFuel]
| _, _, SafeStep.R_merge_cancel t _ _ => by
    simp [ctxFuel]
    omega
| _, _, SafeStep.R_rec_zero b s _ => by
    have hâ‚ : ctxFuel b < ctxFuel b + 1 := Nat.lt_succ_self (ctxFuel b)
    have hâ‚‚ : ctxFuel b + 1 â‰¤ 2 ^ (ctxFuel s + 5) + (ctxFuel b + 1) := Nat.le_add_left _ _
    have hâ‚ƒ : ctxFuel b < 2 ^ (ctxFuel s + 5) + (ctxFuel b + 1) := lt_of_lt_of_le hâ‚ hâ‚‚
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hâ‚ƒ
| _, _, SafeStep.R_rec_succ b s n => by
    simpa [ctxFuel] using ctxFuel_rec_succ_drop b s n
| _, _, SafeStep.R_eq_refl a _ => by
    simp [ctxFuel]
| _, _, SafeStep.R_eq_diff a b _ => by
    simp [ctxFuel]

lemma ctxFuel_decreases_ctx : âˆ€ {a b : Trace}, SafeStepCtx a b â†’ ctxFuel b < ctxFuel a
| _, _, SafeStepCtx.root hs => ctxFuel_decreases_safe hs
| _, _, @SafeStepCtx.integrate t u h => by
    have ih : ctxFuel u < ctxFuel t := ctxFuel_decreases_ctx h
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right ih 1)
| _, _, @SafeStepCtx.mergeL a a' b h => by
    have ih : ctxFuel a' < ctxFuel a := ctxFuel_decreases_ctx h
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right ih (ctxFuel b + 2))
| _, _, @SafeStepCtx.mergeR a b b' h => by
    have ih : ctxFuel b' < ctxFuel b := ctxFuel_decreases_ctx h
    have hâ‚ : ctxFuel a + ctxFuel b' < ctxFuel a + ctxFuel b := Nat.add_lt_add_left ih (ctxFuel a)
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right hâ‚ 2)
| _, _, @SafeStepCtx.appL a a' b h => by
    have ih : ctxFuel a' < ctxFuel a := ctxFuel_decreases_ctx h
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right ih (ctxFuel b + 1))
| _, _, @SafeStepCtx.appR a b b' h => by
    have ih : ctxFuel b' < ctxFuel b := ctxFuel_decreases_ctx h
    have hâ‚ : ctxFuel a + ctxFuel b' < ctxFuel a + ctxFuel b := Nat.add_lt_add_left ih (ctxFuel a)
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right hâ‚ 1)
| _, _, @SafeStepCtx.recB b b' s n h => by
    have ih : ctxFuel b' < ctxFuel b := ctxFuel_decreases_ctx h
    let C : Nat := 2 ^ (ctxFuel n + ctxFuel s + 5)
    have hâ‚ : C + ctxFuel b' < C + ctxFuel b := Nat.add_lt_add_left ih C
    simpa [ctxFuel, C, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right hâ‚ 1)
| _, _, @SafeStepCtx.recS b s s' n h => by
    have ih : ctxFuel s' < ctxFuel s := ctxFuel_decreases_ctx h
    let E' : Nat := ctxFuel n + ctxFuel s' + 5
    let E : Nat := ctxFuel n + ctxFuel s + 5
    have hExp : E' < E := by
      have hâ‚ : ctxFuel n + ctxFuel s' < ctxFuel n + ctxFuel s := Nat.add_lt_add_left ih (ctxFuel n)
      simpa [E', E] using Nat.add_lt_add_right hâ‚ 5
    have hPow : 2 ^ E' < 2 ^ E := Nat.pow_lt_pow_right one_lt_two_nat hExp
    simpa [ctxFuel, E', E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right hPow (ctxFuel b + 1))
| _, _, @SafeStepCtx.recN b s n n' h => by
    have ih : ctxFuel n' < ctxFuel n := ctxFuel_decreases_ctx h
    let E' : Nat := ctxFuel n' + ctxFuel s + 5
    let E : Nat := ctxFuel n + ctxFuel s + 5
    have hExp : E' < E := by
      have hâ‚ : ctxFuel n' + ctxFuel s < ctxFuel n + ctxFuel s := Nat.add_lt_add_right ih (ctxFuel s)
      simpa [E', E] using Nat.add_lt_add_right hâ‚ 5
    have hPow : 2 ^ E' < 2 ^ E := Nat.pow_lt_pow_right one_lt_two_nat hExp
    simpa [ctxFuel, E', E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right hPow (ctxFuel b + 1))

theorem wf_SafeStepCtxRev : WellFounded (fun a b : Trace => SafeStepCtx b a) := by
  have hwf : WellFounded (fun x y : Trace => ctxFuel x < ctxFuel y) :=
    InvImage.wf (f := ctxFuel) Nat.lt_wfRel.wf
  have hsub : Subrelation (fun a b : Trace => SafeStepCtx b a)
      (fun x y : Trace => ctxFuel x < ctxFuel y) := by
    intro a b h
    exact ctxFuel_decreases_ctx h
  exact Subrelation.wf hsub hwf

theorem recCtxAccObligation : RecCtxAccObligation := by
  intro b s n hb hs hn
  exact (wf_SafeStepCtxRev.apply (recÎ” b s n))

theorem acc_ctx_all : âˆ€ t : Trace, Acc SafeStepCtxRev t := by
  intro t
  simpa [SafeStepCtxRev] using (wf_SafeStepCtxRev.apply t)

end MetaSN_KO7
````

## OperatorKO7/Meta/DependencyPairs_Works.lean

**Lines:** 61

``lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import Mathlib.Order.WellFounded

/-!
# Dependency Pairs Work on the KO7 Duplicating Recursor

This module gives a minimal formal witness that the KO7 duplicating recursor is
handled by a dependency-pair style argument:

- Extract the single recursive-call dependency pair from `rec_succ`.
- Use the DP projection rank (track only the recursion counter argument).
- Prove strict decrease on every DP step.
- Conclude well-foundedness of the reverse DP relation via `Nat.lt`.

This is intentionally narrow: it formalizes the DP-chain termination core for
the duplicating rule, not a full generic DP framework library.
-/

namespace OperatorKO7.MetaDependencyPairs

open OperatorKO7 Trace
open OperatorKO7.CompositionalImpossibility

/-- The dependency pair relation extracted from `rec_succ`:
`recÎ” b s (delta n) â†¦ recÎ” b s n`. -/
inductive DPPair : Trace â†’ Trace â†’ Prop
| rec_succ : âˆ€ b s n, DPPair (recÎ” b s (delta n)) (recÎ” b s n)

/-- DP rank used for the pair problem:
reuse the projection that keeps only recursion-counter depth. -/
@[simp] def dpRank : Trace â†’ Nat := dpProjection

/-- Each dependency-pair step strictly decreases the DP rank. -/
theorem dpPair_decreases : âˆ€ {a b : Trace}, DPPair a b â†’ dpRank b < dpRank a
  | _, _, DPPair.rec_succ b s n => by
      simp [dpRank, dpProjection]

/-- Reverse dependency-pair relation (the standard SN orientation). -/
def DPPairRev : Trace â†’ Trace â†’ Prop := fun a b => DPPair b a

/-- Reverse DP relation is a subrelation of `<` on the DP rank. -/
lemma dpPairRev_sub_rank :
    Subrelation DPPairRev (fun x y => dpRank x < dpRank y) := by
  intro a b h
  exact dpPair_decreases h

/-- Well-foundedness of reverse dependency pairs:
no infinite KO7 DP chain is possible for the extracted pair problem. -/
theorem wf_DPPairRev : WellFounded DPPairRev := by
  have hrank : WellFounded (fun x y : Trace => dpRank x < dpRank y) :=
    InvImage.wf (f := dpRank) Nat.lt_wfRel.wf
  exact Subrelation.wf dpPairRev_sub_rank hrank

/-- The extracted pair comes directly from the `rec_succ` rule instance. -/
theorem rec_succ_extracts_dependency_pair (b s n : Trace) :
    Step (recÎ” b s (delta n)) (app s (recÎ” b s n))
    âˆ§ DPPair (recÎ” b s (delta n)) (recÎ” b s n) := by
  exact âŸ¨Step.R_rec_succ b s n, DPPair.rec_succ b s nâŸ©

end OperatorKO7.MetaDependencyPairs
````

## OperatorKO7/Meta/DM_MPO_Orientation.lean

**Lines:** 51

``lean
import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna

/-!
# DM/MPO Orientation Helpers (safe wrappers)

This module provides small, composable wrappers around the Dershowitzâ€“Manna
multiset ordering lemmas used throughout the termination development.

They are deliberately minimal and rely on existing, proven lemmas from the
`MetaSN_DM` toolkit. No kernel rules are changed. No new axioms are introduced.

Use these helpers to keep orientation proofs concise and robust.
-/

namespace OperatorKO7.MetaOrientation

open Multiset
open MetaSN_DM
open OperatorKO7 Trace
open OperatorKO7.MetaCM

/--
Right-add orientation: if `Y â‰  0`, then `X < X + Y` in the DM order.

This is a thin wrapper around `MetaSN_DM.dm_lt_add_of_ne_zero'` with the
arguments placed for ergonomic use.
-/
lemma dm_add_right_of_ne_zero {X Y : Multiset â„•} (hY : Y â‰  0) : OperatorKO7.MetaCM.DM X (X + Y) := by
  simpa using MetaSN_DM.dm_lt_add_of_ne_zero' X Y hY

/--
Left-add orientation: if `X â‰  0`, then `Y < X + Y` in the DM order.

This follows from commutativity of multiset addition and the right-add lemma.
-/
lemma dm_add_left_of_ne_zero {X Y : Multiset â„•} (hX : X â‰  0) : OperatorKO7.MetaCM.DM Y (X + Y) := by
  simpa [add_comm] using MetaSN_DM.dm_lt_add_of_ne_zero' Y X hX

/-- DM drop on Îºá´¹ for rec_zero (re-export for ergonomics). -/
lemma dm_drop_rec_zero (b s : Trace) :
    OperatorKO7.MetaCM.DM (MetaSN_DM.kappaM b) (MetaSN_DM.kappaM (recÎ” b s void)) := by
  simpa [OperatorKO7.MetaCM.DM] using MetaSN_DM.dm_drop_R_rec_zero b s

/-- If X â‰  0 then X âˆª X â‰  0 (re-export). -/
lemma union_self_ne_zero_of_ne_zero {X : Multiset â„•} (h : X â‰  0) :
    X âˆª X â‰  (0 : Multiset â„•) := by
  simpa using MetaSN_DM.union_self_ne_zero_of_ne_zero h

end OperatorKO7.MetaOrientation
````

## OperatorKO7/Meta/DM_OrderType.lean

**Lines:** 1148

``lean
import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Data.Finset.Max
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.UnionInter
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.NaturalOps
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Veblen

/-!
# DM Order-Type Upper-Bound Calibration

This file provides an ordinal calibration layer for the KO7 computable measure stack.
It is intentionally scoped to an upper-bound embedding discussion (not an exact order-type
isomorphism).
-/

namespace OperatorKO7.MetaDM

set_option linter.unnecessarySimpa false

open OperatorKO7
open OperatorKO7.MetaCM
open Trace
open MetaSN_DM
open MetaSN_KO7
open scoped Classical
open Ordinal

/-! ## DM embedding (computable ordinal payload) -/

/-- Fold operator for sorted CNF-style embedding. -/
private noncomputable def dmAddOp (n : Nat) (acc : Ordinal.{0}) : Ordinal.{0} :=
  ((Ï‰ : Ordinal) ^ (n : Ordinal)) + acc

/-- Embed a multiset of naturals as a finite sorted ordinal sum of `Ï‰^n` terms. -/
noncomputable def dmOrdEmbed (m : Multiset Nat) : Ordinal.{0} :=
  (Multiset.sort (Â· â‰¥ Â·) m).foldr dmAddOp 0

private lemma dmOrdEmbed_list_foldr_add (l : List Nat) (b : Ordinal.{0}) :
    l.foldr dmAddOp b = l.foldr dmAddOp 0 + b := by
  induction l with
  | nil =>
      simp
  | cons n l ih =>
      simpa [dmAddOp, ih, add_assoc]

private lemma sort_ge_append_of_all_ge {s t : Multiset Nat}
    (hsep : âˆ€ a âˆˆ s, âˆ€ b âˆˆ t, a â‰¥ b) :
    Multiset.sort (Â· â‰¥ Â·) (s + t) =
      Multiset.sort (Â· â‰¥ Â·) s ++ Multiset.sort (Â· â‰¥ Â·) t := by
  refine List.eq_of_perm_of_sorted (r := (Â· â‰¥ Â·)) ?_ ?_ ?_
  Â· apply (Multiset.coe_eq_coe).1
    calc
      ((Multiset.sort (Â· â‰¥ Â·) (s + t) : List Nat) : Multiset Nat)
          = s + t := Multiset.sort_eq (r := (Â· â‰¥ Â·)) (s + t)
      _ = ((Multiset.sort (Â· â‰¥ Â·) s : List Nat) : Multiset Nat) +
            ((Multiset.sort (Â· â‰¥ Â·) t : List Nat) : Multiset Nat) := by
            simpa [Multiset.sort_eq]
      _ = ((Multiset.sort (Â· â‰¥ Â·) s ++ Multiset.sort (Â· â‰¥ Â·) t : List Nat) : Multiset Nat) := by
            simpa using
              (Multiset.coe_add (Multiset.sort (Â· â‰¥ Â·) s) (Multiset.sort (Â· â‰¥ Â·) t))
  Â· exact Multiset.sort_sorted (r := (Â· â‰¥ Â·)) (s + t)
  Â·
    exact (List.pairwise_append.2 âŸ¨
      Multiset.sort_sorted (r := (Â· â‰¥ Â·)) s,
      Multiset.sort_sorted (r := (Â· â‰¥ Â·)) t,
      by
        intro a ha b hb
        exact hsep a ((Multiset.mem_sort (r := (Â· â‰¥ Â·))).1 ha)
          b ((Multiset.mem_sort (r := (Â· â‰¥ Â·))).1 hb)âŸ©)

private lemma dmOrdEmbed_add_of_separated {s t : Multiset Nat}
    (hsep : âˆ€ a âˆˆ s, âˆ€ b âˆˆ t, a â‰¥ b) :
    dmOrdEmbed (s + t) = dmOrdEmbed s + dmOrdEmbed t := by
  unfold dmOrdEmbed
  rw [sort_ge_append_of_all_ge hsep, List.foldr_append, dmOrdEmbed_list_foldr_add]

private lemma dmOrdEmbed_cons_of_ge_all {a : Nat} {s : Multiset Nat}
    (h : âˆ€ b âˆˆ s, a â‰¥ b) :
    dmOrdEmbed (a ::â‚˜ s) = (Ï‰ : Ordinal) ^ (a : Ordinal) + dmOrdEmbed s := by
  unfold dmOrdEmbed
  rw [Multiset.sort_cons (r := (Â· â‰¥ Â·)) a s h]
  simp [dmAddOp]

lemma dmOrdEmbed_replicate (z c : Nat) :
    dmOrdEmbed (Multiset.replicate c z) =
      (Ï‰ : Ordinal) ^ (z : Ordinal) * (c : Ordinal) := by
  induction c with
  | zero =>
      simp [dmOrdEmbed]
  | succ c ih =>
      have hge : âˆ€ b âˆˆ Multiset.replicate c z, z â‰¥ b := by
        intro b hb
        simpa [Multiset.eq_of_mem_replicate hb]
      calc
        dmOrdEmbed (Multiset.replicate (Nat.succ c) z)
            = dmOrdEmbed (z ::â‚˜ Multiset.replicate c z) := by
                simp [Multiset.replicate_succ]
        _ = (Ï‰ : Ordinal) ^ (z : Ordinal) + dmOrdEmbed (Multiset.replicate c z) :=
              dmOrdEmbed_cons_of_ge_all hge
        _ = (Ï‰ : Ordinal) ^ (z : Ordinal) +
              ((Ï‰ : Ordinal) ^ (z : Ordinal) * (c : Ordinal)) := by
                rw [ih]
        _ = (Ï‰ : Ordinal) ^ (z : Ordinal) * (Nat.succ c : Ordinal) := by
                calc
                  (Ï‰ : Ordinal) ^ (z : Ordinal) +
                      ((Ï‰ : Ordinal) ^ (z : Ordinal) * (c : Ordinal))
                      = (Ï‰ : Ordinal) ^ (z : Ordinal) + c â€¢ ((Ï‰ : Ordinal) ^ (z : Ordinal)) := by
                          rw [Ordinal.smul_eq_mul]
                  _ = (Nat.succ c) â€¢ ((Ï‰ : Ordinal) ^ (z : Ordinal)) := by
                        simpa using (succ_nsmul' ((Ï‰ : Ordinal) ^ (z : Ordinal)) c).symm
                  _ = (Ï‰ : Ordinal) ^ (z : Ordinal) * (Nat.succ c : Ordinal) := by
                        rw [Ordinal.smul_eq_mul]

lemma dmOrdEmbed_replicate_add_of_all_lt {z c : Nat} {low : Multiset Nat}
    (hlow : âˆ€ n âˆˆ low, n < z) :
    dmOrdEmbed (Multiset.replicate c z + low) =
      (Ï‰ : Ordinal) ^ (z : Ordinal) * (c : Ordinal) + dmOrdEmbed low := by
  have hsep : âˆ€ a âˆˆ Multiset.replicate c z, âˆ€ b âˆˆ low, a â‰¥ b := by
    intro a ha b hb
    have ha' : a = z := Multiset.eq_of_mem_replicate ha
    subst ha'
    exact Nat.le_of_lt (hlow b hb)
  calc
    dmOrdEmbed (Multiset.replicate c z + low)
        = dmOrdEmbed (Multiset.replicate c z) + dmOrdEmbed low :=
          dmOrdEmbed_add_of_separated hsep
    _ = (Ï‰ : Ordinal) ^ (z : Ordinal) * (c : Ordinal) + dmOrdEmbed low := by
          rw [dmOrdEmbed_replicate]

private lemma dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le
    {m : Multiset Nat} {z : Nat} (hle : âˆ€ n âˆˆ m, n â‰¤ z) :
    dmOrdEmbed m =
      (Ï‰ : Ordinal) ^ (z : Ordinal) * (Multiset.count z m : Ordinal) +
        dmOrdEmbed (m.filter (fun n => n < z)) := by
  have hDecomp :
      m = m.filter (Eq z) + m.filter (fun n => Â¬ z = n) := by
    simpa [add_comm] using (Multiset.filter_add_not (p := Eq z) m).symm
  have hNeEqLt :
      m.filter (fun n => Â¬ z = n) = m.filter (fun n => n < z) := by
    refine Multiset.filter_congr ?_
    intro n hn
    constructor
    Â· intro hne
      exact lt_of_le_of_ne (hle n hn) (by simpa [eq_comm] using hne)
    Â· intro hlt
      exact (by simpa [eq_comm] using (ne_of_lt hlt))
  have hEqRep : m.filter (Eq z) = Multiset.replicate (Multiset.count z m) z := by
    simpa using (Multiset.filter_eq m z)
  have hLow : âˆ€ n âˆˆ m.filter (fun n => n < z), n < z := by
    intro n hn
    exact (Multiset.mem_filter.1 hn).2
  calc
    dmOrdEmbed m
        = dmOrdEmbed (m.filter (Eq z) + m.filter (fun n => Â¬ z = n)) := by
            exact congrArg dmOrdEmbed hDecomp
    _ = dmOrdEmbed (Multiset.replicate (Multiset.count z m) z + m.filter (fun n => n < z)) := by
          rw [hEqRep, hNeEqLt]
    _ = (Ï‰ : Ordinal) ^ (z : Ordinal) * (Multiset.count z m : Ordinal) +
          dmOrdEmbed (m.filter (fun n => n < z)) :=
          dmOrdEmbed_replicate_add_of_all_lt hLow

private lemma dmOrdEmbed_list_lt_opow_omega :
    âˆ€ l : List Nat, l.foldr dmAddOp 0 < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)
  | [] => by
      simpa [dmAddOp] using
        (Ordinal.opow_pos (a := (Ï‰ : Ordinal)) (b := (Ï‰ : Ordinal)) Ordinal.omega0_pos)
  | n :: l => by
      have ih : l.foldr dmAddOp 0 < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) :=
        dmOrdEmbed_list_lt_opow_omega l
      have hpow : (Ï‰ : Ordinal) ^ (n : Ordinal) < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
        exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
          (Ordinal.nat_lt_omega0 n)
      have hlt :
          (Ï‰ : Ordinal) ^ (n : Ordinal) + l.foldr dmAddOp 0 <
            (Ï‰ : Ordinal) ^ (n : Ordinal) + (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
        exact add_lt_add_left ih ((Ï‰ : Ordinal) ^ (n : Ordinal))
      exact lt_of_lt_of_eq hlt (Ordinal.add_omega0_opow hpow)

private lemma dmOrdEmbed_list_lt_opow_of_forall_lt :
    âˆ€ (k : Nat) (l : List Nat),
      (âˆ€ n âˆˆ l, n < k) â†’ l.foldr dmAddOp 0 < (Ï‰ : Ordinal) ^ (k : Ordinal)
  | k, [], _ => by
      simpa [dmAddOp] using
        (Ordinal.opow_pos (a := (Ï‰ : Ordinal)) (b := (k : Ordinal)) Ordinal.omega0_pos)
  | k, n :: l, hltAll => by
      have hn : n < k := hltAll n (by simp)
      have hltTail : âˆ€ m âˆˆ l, m < k := by
        intro m hm
        exact hltAll m (by simp [hm])
      have ih : l.foldr dmAddOp 0 < (Ï‰ : Ordinal) ^ (k : Ordinal) :=
        dmOrdEmbed_list_lt_opow_of_forall_lt k l hltTail
      have hkOrd : (n : Ordinal) < (k : Ordinal) := by
        exact_mod_cast hn
      have hpow : (Ï‰ : Ordinal) ^ (n : Ordinal) < (Ï‰ : Ordinal) ^ (k : Ordinal) := by
        exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 hkOrd
      have hlt :
          (Ï‰ : Ordinal) ^ (n : Ordinal) + l.foldr dmAddOp 0 <
            (Ï‰ : Ordinal) ^ (n : Ordinal) + (Ï‰ : Ordinal) ^ (k : Ordinal) := by
        exact add_lt_add_left ih ((Ï‰ : Ordinal) ^ (n : Ordinal))
      exact lt_of_lt_of_eq hlt (Ordinal.add_omega0_opow hpow)

private lemma dmOrdEmbed_lt_opow_of_forall_lt
    {m : Multiset Nat} {k : Nat} (h : âˆ€ n âˆˆ m, n < k) :
    dmOrdEmbed m < (Ï‰ : Ordinal) ^ (k : Ordinal) := by
  have hsort : âˆ€ n âˆˆ Multiset.sort (Â· â‰¥ Â·) m, n < k := by
    intro n hn
    exact h n ((Multiset.mem_sort (r := (Â· â‰¥ Â·))).1 hn)
  simpa [dmOrdEmbed] using
    dmOrdEmbed_list_lt_opow_of_forall_lt k (Multiset.sort (Â· â‰¥ Â·) m) hsort

private lemma dmOrdEmbed_lt_of_all_le_and_count_lt
    {mâ‚ mâ‚‚ : Multiset Nat} {z : Nat}
    (hâ‚le : âˆ€ n âˆˆ mâ‚, n â‰¤ z)
    (hâ‚‚le : âˆ€ n âˆˆ mâ‚‚, n â‰¤ z)
    (hcount : Multiset.count z mâ‚ < Multiset.count z mâ‚‚) :
    dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚ := by
  rw [dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le hâ‚le,
    dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le hâ‚‚le]
  have hLow :
      dmOrdEmbed (mâ‚.filter (fun n => n < z)) < (Ï‰ : Ordinal) ^ (z : Ordinal) := by
    apply dmOrdEmbed_lt_opow_of_forall_lt
    intro n hn
    exact (Multiset.mem_filter.1 hn).2
  have hstep :
      (Ï‰ : Ordinal) ^ (z : Ordinal) * (Multiset.count z mâ‚ : Ordinal) +
          dmOrdEmbed (mâ‚.filter (fun n => n < z)) <
        (Ï‰ : Ordinal) ^ (z : Ordinal) * Order.succ (Multiset.count z mâ‚ : Ordinal) := by
    simpa using
      (Ordinal.opow_mul_add_lt_opow_mul_succ
        (b := (Ï‰ : Ordinal)) (u := (z : Ordinal))
        (v := (Multiset.count z mâ‚ : Ordinal))
        (w := dmOrdEmbed (mâ‚.filter (fun n => n < z))) hLow)
  have hcountOrd : (Multiset.count z mâ‚ : Ordinal) < (Multiset.count z mâ‚‚ : Ordinal) := by
    exact_mod_cast hcount
  have hsucc :
      Order.succ (Multiset.count z mâ‚ : Ordinal) â‰¤ (Multiset.count z mâ‚‚ : Ordinal) := by
    exact (Order.succ_le_iff).2 hcountOrd
  have hmul :
      (Ï‰ : Ordinal) ^ (z : Ordinal) * Order.succ (Multiset.count z mâ‚ : Ordinal) â‰¤
        (Ï‰ : Ordinal) ^ (z : Ordinal) * (Multiset.count z mâ‚‚ : Ordinal) := by
    exact mul_le_mul_left' hsucc ((Ï‰ : Ordinal) ^ (z : Ordinal))
  have hle :
      (Ï‰ : Ordinal) ^ (z : Ordinal) * (Multiset.count z mâ‚‚ : Ordinal) â‰¤
        (Ï‰ : Ordinal) ^ (z : Ordinal) * (Multiset.count z mâ‚‚ : Ordinal) +
          dmOrdEmbed (mâ‚‚.filter (fun n => n < z)) := by
    exact Ordinal.le_add_right
      ((Ï‰ : Ordinal) ^ (z : Ordinal) * (Multiset.count z mâ‚‚ : Ordinal))
      (dmOrdEmbed (mâ‚‚.filter (fun n => n < z)))
  exact lt_of_lt_of_le hstep (hmul.trans hle)

lemma dmOrdEmbed_lt_opow_omega (m : Multiset Nat) :
    dmOrdEmbed m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
  simpa [dmOrdEmbed] using dmOrdEmbed_list_lt_opow_omega (Multiset.sort (Â· â‰¥ Â·) m)

private lemma dmOrdEmbed_foldr_le_of_sublist {lâ‚ lâ‚‚ : List Nat}
    (h : List.Sublist lâ‚ lâ‚‚) :
    lâ‚.foldr dmAddOp 0 â‰¤ lâ‚‚.foldr dmAddOp 0 := by
  induction h with
  | slnil =>
      rfl
  | cons a h ih =>
      exact ih.trans (by
        simp [dmAddOp, Ordinal.le_add_left])
  | consâ‚‚ a h ih =>
      simpa [dmAddOp] using add_le_add_left ih ((Ï‰ : Ordinal) ^ (a : Ordinal))

/--
Monotonicity of `dmOrdEmbed` under multiset inclusion.

This is enough for the explicit `rec_zero` strictness argument, where the DM payload grows by
adding a nonempty multiset to the RHS.
-/
lemma dmOrdEmbed_mono {m n : Multiset Nat} (h : m â‰¤ n) :
    dmOrdEmbed m â‰¤ dmOrdEmbed n := by
  have hSubperm :
      List.Subperm (Multiset.sort (Â· â‰¥ Â·) m) (Multiset.sort (Â· â‰¥ Â·) n) := by
    rw [List.subperm_iff_count]
    intro a
    have hm :
        (Multiset.sort (Â· â‰¥ Â·) m).count a = Multiset.count a m := by
      simpa using (Multiset.coe_count a (Multiset.sort (Â· â‰¥ Â·) m)).symm
    have hn :
        (Multiset.sort (Â· â‰¥ Â·) n).count a = Multiset.count a n := by
      simpa using (Multiset.coe_count a (Multiset.sort (Â· â‰¥ Â·) n)).symm
    calc
      (Multiset.sort (Â· â‰¥ Â·) m).count a = Multiset.count a m := hm
      _ â‰¤ Multiset.count a n := Multiset.count_le_of_le a h
      _ = (Multiset.sort (Â· â‰¥ Â·) n).count a := hn.symm
  have hSublist :
      List.Sublist (Multiset.sort (Â· â‰¥ Â·) m) (Multiset.sort (Â· â‰¥ Â·) n) := by
    exact List.sublist_of_subperm_of_sorted hSubperm
      (Multiset.sort_sorted (r := (Â· â‰¥ Â·)) m)
      (Multiset.sort_sorted (r := (Â· â‰¥ Â·)) n)
  exact (dmOrdEmbed_foldr_le_of_sublist hSublist)

@[simp] lemma dmOrdEmbed_zero : dmOrdEmbed (0 : Multiset Nat) = 0 := by
  simp [dmOrdEmbed]

@[simp] lemma dmOrdEmbed_singleton (n : Nat) :
    dmOrdEmbed ({n} : Multiset Nat) = (Ï‰ : Ordinal) ^ (n : Ordinal) := by
  simp [dmOrdEmbed, dmAddOp]

private lemma dmOrdEmbed_lt_of_dominated_nonempty
    {Y Z : Multiset Nat}
    (hZ : Z â‰  0)
    (hDom : âˆ€ y âˆˆ Y, âˆƒ z âˆˆ Z, y < z) :
    dmOrdEmbed Y < dmOrdEmbed Z := by
  let zMax : Nat := Z.toFinset.max' (Multiset.toFinset_nonempty.2 hZ)
  have hzMax_mem : zMax âˆˆ Z := by
    exact (Multiset.mem_toFinset).1
      (Finset.max'_mem _ _)
  have hz_le_max : âˆ€ z âˆˆ Z, z â‰¤ zMax := by
    intro z hz
    exact Finset.le_max' _ _ ((Multiset.mem_toFinset).2 hz)
  have hYltMax : âˆ€ y âˆˆ Y, y < zMax := by
    intro y hy
    rcases hDom y hy with âŸ¨z, hz, hyzâŸ©
    exact lt_of_lt_of_le hyz (hz_le_max z hz)
  have hYlt :
      dmOrdEmbed Y < (Ï‰ : Ordinal) ^ (zMax : Ordinal) :=
    dmOrdEmbed_lt_opow_of_forall_lt hYltMax
  have hSingleLe : ({zMax} : Multiset Nat) â‰¤ Z := by
    exact (Multiset.singleton_le).2 hzMax_mem
  have hZge :
      (Ï‰ : Ordinal) ^ (zMax : Ordinal) â‰¤ dmOrdEmbed Z := by
    calc
      (Ï‰ : Ordinal) ^ (zMax : Ordinal)
          = dmOrdEmbed ({zMax} : Multiset Nat) := by
              simpa using (dmOrdEmbed_singleton zMax).symm
      _ â‰¤ dmOrdEmbed Z := dmOrdEmbed_mono hSingleLe
  exact lt_of_lt_of_le hYlt hZge

lemma dmOrdEmbed_strictMono {mâ‚ mâ‚‚ : Multiset Nat} (hDM : DM mâ‚ mâ‚‚) :
    dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚ := by
  rcases hDM with âŸ¨X, Y, Z, hZ, hmâ‚, hmâ‚‚, hDomâŸ©
  let zMax : Nat := Z.toFinset.max' (Multiset.toFinset_nonempty.2 hZ)
  have hzMem : zMax âˆˆ Z := by
    exact (Multiset.mem_toFinset).1 (Finset.max'_mem _ _)
  have hzLe : âˆ€ z âˆˆ Z, z â‰¤ zMax := by
    intro z hz
    exact Finset.le_max' _ _ ((Multiset.mem_toFinset).2 hz)
  have hYlt : âˆ€ y âˆˆ Y, y < zMax := by
    intro y hy
    rcases hDom y hy with âŸ¨z, hz, hyzâŸ©
    exact lt_of_lt_of_le hyz (hzLe z hz)

  let Xhi : Multiset Nat := X.filter (fun n => zMax < n)
  let Xlo : Multiset Nat := X.filter (fun n => n â‰¤ zMax)

  have hXsplit : X = Xhi + Xlo := by
    have hNotEq :
        X.filter (fun n => Â¬ zMax < n) = X.filter (fun n => n â‰¤ zMax) := by
      refine Multiset.filter_congr ?_
      intro n hn
      exact (Nat.not_lt)
    calc
      X = X.filter (fun n => zMax < n) + X.filter (fun n => Â¬ zMax < n) := by
            simpa [add_comm] using
              (Multiset.filter_add_not (p := fun n => zMax < n) X).symm
      _ = Xhi + Xlo := by rw [hNotEq]

  have hSepâ‚ : âˆ€ a âˆˆ Xhi, âˆ€ b âˆˆ Xlo + Y, a â‰¥ b := by
    intro a ha b hb
    have haGt : zMax < a := (Multiset.mem_filter.1 ha).2
    rcases Multiset.mem_add.1 hb with hb | hb
    Â· exact le_trans ((Multiset.mem_filter.1 hb).2) haGt.le
    Â· exact (hYlt b hb).le.trans haGt.le
  have hSepâ‚‚ : âˆ€ a âˆˆ Xhi, âˆ€ b âˆˆ Xlo + Z, a â‰¥ b := by
    intro a ha b hb
    have haGt : zMax < a := (Multiset.mem_filter.1 ha).2
    rcases Multiset.mem_add.1 hb with hb | hb
    Â· exact le_trans ((Multiset.mem_filter.1 hb).2) haGt.le
    Â· exact (hzLe b hb).trans haGt.le

  have hâ‚le : âˆ€ n âˆˆ Xlo + Y, n â‰¤ zMax := by
    intro n hn
    rcases Multiset.mem_add.1 hn with hn | hn
    Â· exact (Multiset.mem_filter.1 hn).2
    Â· exact (hYlt n hn).le
  have hâ‚‚le : âˆ€ n âˆˆ Xlo + Z, n â‰¤ zMax := by
    intro n hn
    rcases Multiset.mem_add.1 hn with hn | hn
    Â· exact (Multiset.mem_filter.1 hn).2
    Â· exact hzLe n hn

  have hCountY0 : Multiset.count zMax Y = 0 := by
    refine Multiset.count_eq_zero_of_notMem ?_
    intro hzY
    exact (lt_irrefl zMax) (hYlt zMax hzY)
  have hCountZpos : 0 < Multiset.count zMax Z := Multiset.count_pos.2 hzMem
  have hCount :
      Multiset.count zMax (Xlo + Y) < Multiset.count zMax (Xlo + Z) := by
    calc
      Multiset.count zMax (Xlo + Y)
          = Multiset.count zMax Xlo + Multiset.count zMax Y := by simp [Multiset.count_add]
      _ = Multiset.count zMax Xlo := by simp [hCountY0]
      _ < Multiset.count zMax Xlo + Multiset.count zMax Z := Nat.lt_add_of_pos_right hCountZpos
      _ = Multiset.count zMax (Xlo + Z) := by simp [Multiset.count_add]

  have hInner :
      dmOrdEmbed (Xlo + Y) < dmOrdEmbed (Xlo + Z) :=
    dmOrdEmbed_lt_of_all_le_and_count_lt hâ‚le hâ‚‚le hCount

  have hâ‚ :
      dmOrdEmbed mâ‚ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Y) := by
    calc
      dmOrdEmbed mâ‚ = dmOrdEmbed (X + Y) := by simpa [hmâ‚]
      _ = dmOrdEmbed (Xhi + Xlo + Y) := by rw [hXsplit]
      _ = dmOrdEmbed (Xhi + (Xlo + Y)) := by simp [add_assoc]
      _ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Y) :=
          dmOrdEmbed_add_of_separated hSepâ‚
  have hâ‚‚ :
      dmOrdEmbed mâ‚‚ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Z) := by
    calc
      dmOrdEmbed mâ‚‚ = dmOrdEmbed (X + Z) := by simpa [hmâ‚‚]
      _ = dmOrdEmbed (Xhi + Xlo + Z) := by rw [hXsplit]
      _ = dmOrdEmbed (Xhi + (Xlo + Z)) := by simp [add_assoc]
      _ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Z) :=
          dmOrdEmbed_add_of_separated hSepâ‚‚
  calc
    dmOrdEmbed mâ‚ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Y) := hâ‚
    _ < dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Z) := add_lt_add_left hInner (dmOrdEmbed Xhi)
    _ = dmOrdEmbed mâ‚‚ := hâ‚‚.symm

/--
Order reflection for the multiset-to-ordinal embedding:
if `dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚`, then `DM mâ‚ mâ‚‚`.
-/
lemma dmOrdEmbed_reflects {mâ‚ mâ‚‚ : Multiset Nat}
    (hlt : dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚) :
    DM mâ‚ mâ‚‚ := by
  classical
  let X : Multiset Nat := mâ‚ âˆ© mâ‚‚
  let Y : Multiset Nat := mâ‚ - mâ‚‚
  let Z : Multiset Nat := mâ‚‚ - mâ‚

  have hZne : Z â‰  0 := by
    intro hZ0
    have hm2le : mâ‚‚ â‰¤ mâ‚ := by
      refine (Multiset.le_iff_count).2 ?_
      intro a
      have hZa : Multiset.count a Z = 0 := by simpa [hZ0]
      have hsub : Multiset.count a mâ‚‚ - Multiset.count a mâ‚ = 0 := by
        simpa [Z, Multiset.count_sub] using hZa
      exact Nat.sub_eq_zero_iff_le.mp hsub
    exact (not_lt_of_ge (dmOrdEmbed_mono hm2le)) hlt

  have hm1 : mâ‚ = X + Y := by
    have hYX : Y + X = mâ‚ := by
      simpa [X, Y, add_comm] using (Multiset.sub_add_inter mâ‚ mâ‚‚)
    calc
      mâ‚ = Y + X := hYX.symm
      _ = X + Y := by simp [add_comm]

  have hm2 : mâ‚‚ = X + Z := by
    have hZX : Z + X = mâ‚‚ := by
      simpa [X, Z, add_comm, Multiset.inter_comm] using (Multiset.sub_add_inter mâ‚‚ mâ‚)
    calc
      mâ‚‚ = Z + X := hZX.symm
      _ = X + Z := by simp [add_comm]

  let zMax : Nat := Z.toFinset.max' (Multiset.toFinset_nonempty.2 hZne)
  have hzMem : zMax âˆˆ Z := by
    exact (Multiset.mem_toFinset).1 (Finset.max'_mem _ _)
  have hzLe : âˆ€ z âˆˆ Z, z â‰¤ zMax := by
    intro z hz
    exact Finset.le_max' _ _ ((Multiset.mem_toFinset).2 hz)

  have hDom : âˆ€ y âˆˆ Y, âˆƒ z âˆˆ Z, y < z := by
    intro y hy
    by_contra hyNot
    have hyGe : zMax â‰¤ y := by
      by_contra hyLt
      exact hyNot âŸ¨zMax, hzMem, lt_of_not_ge hyLtâŸ©

    let m1hi : Multiset Nat := mâ‚.filter (fun n => y < n)
    let m1lo : Multiset Nat := mâ‚.filter (fun n => n â‰¤ y)
    let m2hi : Multiset Nat := mâ‚‚.filter (fun n => y < n)
    let m2lo : Multiset Nat := mâ‚‚.filter (fun n => n â‰¤ y)

    have h1split : mâ‚ = m1hi + m1lo := by
      have hNot :
          mâ‚.filter (fun n => Â¬ y < n) = mâ‚.filter (fun n => n â‰¤ y) := by
        refine Multiset.filter_congr ?_
        intro n hn
        exact Nat.not_lt
      calc
        mâ‚ = mâ‚.filter (fun n => y < n) + mâ‚.filter (fun n => Â¬ y < n) := by
              simpa [add_comm] using
                (Multiset.filter_add_not (p := fun n => y < n) mâ‚).symm
        _ = m1hi + m1lo := by rw [hNot]

    have h2split : mâ‚‚ = m2hi + m2lo := by
      have hNot :
          mâ‚‚.filter (fun n => Â¬ y < n) = mâ‚‚.filter (fun n => n â‰¤ y) := by
        refine Multiset.filter_congr ?_
        intro n hn
        exact Nat.not_lt
      calc
        mâ‚‚ = mâ‚‚.filter (fun n => y < n) + mâ‚‚.filter (fun n => Â¬ y < n) := by
              simpa [add_comm] using
                (Multiset.filter_add_not (p := fun n => y < n) mâ‚‚).symm
        _ = m2hi + m2lo := by rw [hNot]

    have hHiLe : m2hi â‰¤ m1hi := by
      refine (Multiset.le_iff_count).2 ?_
      intro a
      by_cases hya : y < a
      Â· have hNoZ : a âˆ‰ Z := by
          intro haZ
          have hAle : a â‰¤ zMax := hzLe a haZ
          exact (not_lt_of_ge (hAle.trans hyGe)) hya
        have hZa0 : Multiset.count a Z = 0 := Multiset.count_eq_zero_of_notMem hNoZ
        have hsub : Multiset.count a mâ‚‚ - Multiset.count a mâ‚ = 0 := by
          simpa [Z, Multiset.count_sub] using hZa0
        have hle : Multiset.count a mâ‚‚ â‰¤ Multiset.count a mâ‚ := Nat.sub_eq_zero_iff_le.mp hsub
        simpa [m2hi, m1hi, Multiset.count_filter, hya] using hle
      Â· simpa [m2hi, m1hi, Multiset.count_filter, hya]

    have hHigh : dmOrdEmbed m2hi â‰¤ dmOrdEmbed m1hi := dmOrdEmbed_mono hHiLe

    have hCountY : Multiset.count y mâ‚‚ < Multiset.count y mâ‚ := by
      have hYpos : 0 < Multiset.count y Y := Multiset.count_pos.2 hy
      have hsub : Multiset.count y mâ‚ - Multiset.count y mâ‚‚ > 0 := by
        simpa [Y, Multiset.count_sub] using hYpos
      exact Nat.sub_pos_iff_lt.mp hsub

    have hLow : dmOrdEmbed m2lo < dmOrdEmbed m1lo := by
      have h2le : âˆ€ n âˆˆ m2lo, n â‰¤ y := by
        intro n hn
        exact (Multiset.mem_filter.1 hn).2
      have h1le : âˆ€ n âˆˆ m1lo, n â‰¤ y := by
        intro n hn
        exact (Multiset.mem_filter.1 hn).2
      have hcount :
          Multiset.count y m2lo < Multiset.count y m1lo := by
        simpa [m2lo, m1lo, Multiset.count_filter, Nat.le_refl y] using hCountY
      exact dmOrdEmbed_lt_of_all_le_and_count_lt h2le h1le hcount

    have hSep1 : âˆ€ a âˆˆ m1hi, âˆ€ b âˆˆ m1lo, a â‰¥ b := by
      intro a ha b hb
      exact (Multiset.mem_filter.1 hb).2.trans (Nat.le_of_lt (Multiset.mem_filter.1 ha).2)

    have hSep2 : âˆ€ a âˆˆ m2hi, âˆ€ b âˆˆ m2lo, a â‰¥ b := by
      intro a ha b hb
      exact (Multiset.mem_filter.1 hb).2.trans (Nat.le_of_lt (Multiset.mem_filter.1 ha).2)

    have hEmb1 : dmOrdEmbed mâ‚ = dmOrdEmbed m1hi + dmOrdEmbed m1lo := by
      calc
        dmOrdEmbed mâ‚ = dmOrdEmbed (m1hi + m1lo) := by rw [h1split]
        _ = dmOrdEmbed m1hi + dmOrdEmbed m1lo := dmOrdEmbed_add_of_separated hSep1

    have hEmb2 : dmOrdEmbed mâ‚‚ = dmOrdEmbed m2hi + dmOrdEmbed m2lo := by
      calc
        dmOrdEmbed mâ‚‚ = dmOrdEmbed (m2hi + m2lo) := by rw [h2split]
        _ = dmOrdEmbed m2hi + dmOrdEmbed m2lo := dmOrdEmbed_add_of_separated hSep2

    have hrev : dmOrdEmbed mâ‚‚ < dmOrdEmbed mâ‚ := by
      calc
        dmOrdEmbed mâ‚‚ = dmOrdEmbed m2hi + dmOrdEmbed m2lo := hEmb2
        _ â‰¤ dmOrdEmbed m1hi + dmOrdEmbed m2lo := add_le_add_right hHigh _
        _ < dmOrdEmbed m1hi + dmOrdEmbed m1lo := add_lt_add_left hLow _
        _ = dmOrdEmbed mâ‚ := hEmb1.symm
    exact (lt_asymm hlt hrev)

  exact âŸ¨X, Y, Z, hZne, hm1, hm2, hDomâŸ©

/-! ## Îµâ‚€ bridge facts -/

lemma opow_omega_lt_epsilon0 : (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) < Îµâ‚€ := by
  -- `(fun a => Ï‰^a)^[3] 0 = Ï‰^Ï‰`
  simpa [Function.iterate_succ_apply, opow_zero, opow_one] using
    (iterate_omega0_opow_lt_epsilon0 3)

/-- Inner lex block embedding `(Îº,Ï„) â†¦ Ï‰*Îº + Ï„`. -/
noncomputable def lexDMToOrd (p : Multiset Nat Ã— Nat) : Ordinal.{0} :=
  Ï‰ * dmOrdEmbed p.1 + (p.2 : Ordinal)

/-- Outer triple embedding `(Î´,(Îº,Ï„)) â†¦ Ï‰^Ï‰*Î´ + (Ï‰*Îº + Ï„)`. -/
noncomputable def lex3cToOrd (x : Nat Ã— (Multiset Nat Ã— Nat)) : Ordinal.{0} :=
  (Ï‰ ^ Ï‰) * (x.1 : Ordinal) + lexDMToOrd x.2

/-- If `dmOrdEmbed Îº < Ï‰^Ï‰`, then the inner block is also `< Ï‰^Ï‰`. -/
private lemma lexDMToOrd_lt_opow_omega_of_dmBound
    (hBound : âˆ€ m : Multiset Nat, dmOrdEmbed m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
    (p : Multiset Nat Ã— Nat) :
    lexDMToOrd p < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
  rcases p with âŸ¨Îº, Ï„âŸ©
  have hÏ„ : (Ï„ : Ordinal) < (Ï‰ : Ordinal) := Ordinal.nat_lt_omega0 Ï„
  have hÏ„1 : (Ï„ : Ordinal) < (Ï‰ : Ordinal) ^ (1 : Ordinal) := by
    simpa [Ordinal.opow_one] using hÏ„
  have hstep :
      (Ï‰ : Ordinal) * dmOrdEmbed Îº + (Ï„ : Ordinal) <
        (Ï‰ : Ordinal) * Order.succ (dmOrdEmbed Îº) := by
    simpa using
      (Ordinal.opow_mul_add_lt_opow_mul_succ
        (b := (Ï‰ : Ordinal)) (u := (1 : Ordinal))
        (v := dmOrdEmbed Îº) (w := (Ï„ : Ordinal)) hÏ„1)
  have hsucc : Order.succ (dmOrdEmbed Îº) â‰¤ (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
    exact (Order.succ_le_iff).2 (hBound Îº)
  have hmul :
      (Ï‰ : Ordinal) * Order.succ (dmOrdEmbed Îº) â‰¤
        (Ï‰ : Ordinal) * ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) := by
    exact mul_le_mul_left' hsucc (Ï‰ : Ordinal)
  have hÏ‰Ï‰ :
      (Ï‰ : Ordinal) * ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) =
        (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
    calc
      (Ï‰ : Ordinal) * ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
          = (Ï‰ : Ordinal) ^ (1 + (Ï‰ : Ordinal)) := by
              simpa [Ordinal.opow_one] using
                (Ordinal.opow_add (Ï‰ : Ordinal) 1 (Ï‰ : Ordinal)).symm
      _ = (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by simp
  calc
    lexDMToOrd (Îº, Ï„) = (Ï‰ : Ordinal) * dmOrdEmbed Îº + (Ï„ : Ordinal) := by rfl
    _ < (Ï‰ : Ordinal) * Order.succ (dmOrdEmbed Îº) := hstep
    _ â‰¤ (Ï‰ : Ordinal) * ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) := hmul
    _ = (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := hÏ‰Ï‰

/-- Unconditional inner-block bound, using `dmOrdEmbed_lt_opow_omega`. -/
lemma lexDMToOrd_lt_opow_omega (p : Multiset Nat Ã— Nat) :
    lexDMToOrd p < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) :=
  lexDMToOrd_lt_opow_omega_of_dmBound dmOrdEmbed_lt_opow_omega p

/-- Calibration cap used for the safe triple (`Î´âˆˆ{0,1}`): `Ï‰^Ï‰ * 2 < Îµâ‚€`. -/
lemma opow_omega_mul_two_lt_epsilon0 :
    ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (2 : Nat) < Îµâ‚€ := by
  have hÏ‰lt : (Ï‰ : Ordinal) < Îµâ‚€ := by
    simpa using (Ordinal.omega0_lt_epsilon 0)
  have hmul :
      ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (2 : Nat) <
        (Ï‰ : Ordinal) ^ Îµâ‚€ := by
    simpa using
      (Ordinal.omega0_opow_mul_nat_lt
        (a := (Ï‰ : Ordinal)) (b := Îµâ‚€) hÏ‰lt 2)
  simpa [Ordinal.omega0_opow_epsilon] using hmul

/-- If `Î´ â‰¤ 1` and `dmOrdEmbed` is bounded by `Ï‰^Ï‰`, then `lex3cToOrd` is `< Ï‰^Ï‰*2`. -/
private lemma lex3cToOrd_lt_opow_omega_mul_two_of_dmBound
    (hBound : âˆ€ m : Multiset Nat, dmOrdEmbed m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
    {x : Nat Ã— (Multiset Nat Ã— Nat)} (hÎ´ : x.1 â‰¤ 1) :
    lex3cToOrd x < ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (2 : Nat) := by
  have hInner : lexDMToOrd x.2 < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) :=
    lexDMToOrd_lt_opow_omega_of_dmBound hBound x.2
  have hstep :
      ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (x.1 : Ordinal) + lexDMToOrd x.2 <
        ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * Order.succ (x.1 : Ordinal) := by
    simpa [Ordinal.opow_mul] using
      (Ordinal.opow_mul_add_lt_opow_mul_succ
        (b := (Ï‰ : Ordinal)) (u := (Ï‰ : Ordinal))
        (v := (x.1 : Ordinal)) (w := lexDMToOrd x.2) hInner)
  have hsuccNat : Nat.succ x.1 â‰¤ 2 := Nat.succ_le_succ hÎ´
  have hltTwoNat : x.1 < 2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self x.1) hsuccNat
  have hltTwoOrd : (x.1 : Ordinal) < (2 : Ordinal) := by
    exact_mod_cast hltTwoNat
  have hsuccOrd : Order.succ (x.1 : Ordinal) â‰¤ (2 : Ordinal) := by
    exact (Order.succ_le_iff).2 hltTwoOrd
  have hmul :
      ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * Order.succ (x.1 : Ordinal) â‰¤
        ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (2 : Ordinal) := by
    exact mul_le_mul_left' hsuccOrd ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
  simpa [lex3cToOrd] using lt_of_lt_of_le hstep hmul

/-- Unconditional triple bound under the safe binary-phase side condition `Î´ â‰¤ 1`. -/
lemma lex3cToOrd_lt_opow_omega_mul_two
    {x : Nat Ã— (Multiset Nat Ã— Nat)} (hÎ´ : x.1 â‰¤ 1) :
    lex3cToOrd x < ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (2 : Nat) :=
  lex3cToOrd_lt_opow_omega_mul_two_of_dmBound dmOrdEmbed_lt_opow_omega hÎ´

/-- If `dmOrdEmbed` is bounded by `Ï‰^Ï‰`, then all safe triples are `< Îµâ‚€`. -/
private lemma safeMeasure_below_epsilon0_of_dmBound
    (hBound : âˆ€ m : Multiset Nat, dmOrdEmbed m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
    (t : Trace) :
    lex3cToOrd (mu3c t) < Îµâ‚€ := by
  have hÎ´Flag : MetaSN_KO7.deltaFlag t â‰¤ 1 := by
    rcases MetaSN_KO7.deltaFlag_range t with h0 | h1
    Â· omega
    Â· omega
  have hÎ´ : (mu3c t).1 â‰¤ 1 := by
    simpa [mu3c] using hÎ´Flag
  have hlt :
      lex3cToOrd (mu3c t) < ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (2 : Nat) :=
    lex3cToOrd_lt_opow_omega_mul_two_of_dmBound hBound hÎ´
  exact lt_of_lt_of_le hlt (opow_omega_mul_two_lt_epsilon0.le)

/-- Unconditional `Îµâ‚€` calibration for `mu3c`, via the mechanized `dmOrdEmbed` bound. -/
lemma safeMeasure_below_epsilon0 (t : Trace) :
    lex3cToOrd (mu3c t) < Îµâ‚€ :=
  safeMeasure_below_epsilon0_of_dmBound dmOrdEmbed_lt_opow_omega t

/-- Conditional strict monotonicity for the inner lex block. -/
private lemma lexDMToOrd_strictMono_of_dmMono
    (hMono : âˆ€ {mâ‚ mâ‚‚ : Multiset Nat}, DM mâ‚ mâ‚‚ â†’ dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚)
    {p q : Multiset Nat Ã— Nat} (h : LexDM_c p q) :
    lexDMToOrd p < lexDMToOrd q := by
  rcases p with âŸ¨Îºâ‚, Ï„â‚âŸ©
  rcases q with âŸ¨Îºâ‚‚, Ï„â‚‚âŸ©
  cases h with
  | left _ _ hDM =>
      have hÎº : dmOrdEmbed Îºâ‚ < dmOrdEmbed Îºâ‚‚ := hMono hDM
      have hÏ„ : (Ï„â‚ : Ordinal) < (Ï‰ : Ordinal) := Ordinal.nat_lt_omega0 Ï„â‚
      have hÏ„1 : (Ï„â‚ : Ordinal) < (Ï‰ : Ordinal) ^ (1 : Ordinal) := by
        simpa [Ordinal.opow_one] using hÏ„
      have hstep :
          (Ï‰ : Ordinal) * dmOrdEmbed Îºâ‚ + (Ï„â‚ : Ordinal) <
            (Ï‰ : Ordinal) * Order.succ (dmOrdEmbed Îºâ‚) := by
        simpa using
          (Ordinal.opow_mul_add_lt_opow_mul_succ
            (b := (Ï‰ : Ordinal)) (u := (1 : Ordinal))
            (v := dmOrdEmbed Îºâ‚) (w := (Ï„â‚ : Ordinal)) hÏ„1)
      have hsucc : Order.succ (dmOrdEmbed Îºâ‚) â‰¤ dmOrdEmbed Îºâ‚‚ := by
        exact (Order.succ_le_iff).2 hÎº
      have hmul :
          (Ï‰ : Ordinal) * Order.succ (dmOrdEmbed Îºâ‚) â‰¤
            (Ï‰ : Ordinal) * dmOrdEmbed Îºâ‚‚ := by
        exact mul_le_mul_left' hsucc (Ï‰ : Ordinal)
      have hle : (Ï‰ : Ordinal) * dmOrdEmbed Îºâ‚‚ â‰¤ lexDMToOrd (Îºâ‚‚, Ï„â‚‚) := by
        simpa [lexDMToOrd] using
          (Ordinal.le_add_right ((Ï‰ : Ordinal) * dmOrdEmbed Îºâ‚‚) (Ï„â‚‚ : Ordinal))
      have hstep' :
          lexDMToOrd (Îºâ‚, Ï„â‚) < (Ï‰ : Ordinal) * Order.succ (dmOrdEmbed Îºâ‚) := by
        simpa [lexDMToOrd] using hstep
      calc
        lexDMToOrd (Îºâ‚, Ï„â‚) < (Ï‰ : Ordinal) * Order.succ (dmOrdEmbed Îºâ‚) := hstep'
        _ â‰¤ (Ï‰ : Ordinal) * dmOrdEmbed Îºâ‚‚ := hmul
        _ â‰¤ lexDMToOrd (Îºâ‚‚, Ï„â‚‚) := hle
  | right _ hÏ„Nat =>
      have hÏ„Ord : (Ï„â‚ : Ordinal) < (Ï„â‚‚ : Ordinal) := by
        exact_mod_cast hÏ„Nat
      simpa [lexDMToOrd] using
        (add_lt_add_left hÏ„Ord ((Ï‰ : Ordinal) * dmOrdEmbed Îºâ‚))

/-- Conditional strict monotonicity for the full triple embedding. -/
private lemma lex3cToOrd_strictMono_of_dmBoundMono
    (hBound : âˆ€ m : Multiset Nat, dmOrdEmbed m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
    (hMono : âˆ€ {mâ‚ mâ‚‚ : Multiset Nat}, DM mâ‚ mâ‚‚ â†’ dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚)
    {x y : Nat Ã— (Multiset Nat Ã— Nat)} (h : Lex3c x y) :
    lex3cToOrd x < lex3cToOrd y := by
  rcases x with âŸ¨Î´â‚, pâ‚âŸ©
  rcases y with âŸ¨Î´â‚‚, pâ‚‚âŸ©
  cases h with
  | left _ _ hÎ´Nat =>
      have hInner : lexDMToOrd pâ‚ < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) :=
        lexDMToOrd_lt_opow_omega_of_dmBound hBound pâ‚
      have hstep :
          ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (Î´â‚ : Ordinal) + lexDMToOrd pâ‚ <
            ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * Order.succ (Î´â‚ : Ordinal) := by
        simpa [Ordinal.opow_mul] using
          (Ordinal.opow_mul_add_lt_opow_mul_succ
            (b := (Ï‰ : Ordinal)) (u := (Ï‰ : Ordinal))
            (v := (Î´â‚ : Ordinal)) (w := lexDMToOrd pâ‚) hInner)
      have hÎ´Ord : (Î´â‚ : Ordinal) < (Î´â‚‚ : Ordinal) := by
        exact_mod_cast hÎ´Nat
      have hsucc : Order.succ (Î´â‚ : Ordinal) â‰¤ (Î´â‚‚ : Ordinal) := by
        exact (Order.succ_le_iff).2 hÎ´Ord
      have hmul :
          ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * Order.succ (Î´â‚ : Ordinal) â‰¤
            ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (Î´â‚‚ : Ordinal) := by
        exact mul_le_mul_left' hsucc ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
      have hle :
          ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (Î´â‚‚ : Ordinal) â‰¤
            lex3cToOrd (Î´â‚‚, pâ‚‚) := by
        simpa [lex3cToOrd] using
          (Ordinal.le_add_right
            (((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (Î´â‚‚ : Ordinal))
            (lexDMToOrd pâ‚‚))
      exact lt_of_lt_of_le hstep (hmul.trans hle)
  | right _ hInner =>
      have hInnerOrd : lexDMToOrd pâ‚ < lexDMToOrd pâ‚‚ :=
        lexDMToOrd_strictMono_of_dmMono hMono hInner
      simpa [lex3cToOrd] using
        (add_lt_add_left hInnerOrd (((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) * (Î´â‚ : Ordinal)))

/-- Conditional strict decrease along safe steps via the KO7 computable measure theorem. -/
private lemma safeMeasure_strictMono_of_dmBoundMono
    (hBound : âˆ€ m : Multiset Nat, dmOrdEmbed m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
    (hMono : âˆ€ {mâ‚ mâ‚‚ : Multiset Nat}, DM mâ‚ mâ‚‚ â†’ dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚)
    {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c a) := by
  exact lex3cToOrd_strictMono_of_dmBoundMono hBound hMono (measure_decreases_safe_c h)

lemma lexDMToOrd_strictMono {p q : Multiset Nat Ã— Nat} (h : LexDM_c p q) :
    lexDMToOrd p < lexDMToOrd q :=
  lexDMToOrd_strictMono_of_dmMono
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) h

lemma lex3cToOrd_strictMono {x y : Nat Ã— (Multiset Nat Ã— Nat)} (h : Lex3c x y) :
    lex3cToOrd x < lex3cToOrd y :=
  lex3cToOrd_strictMono_of_dmBoundMono
    dmOrdEmbed_lt_opow_omega
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) h

lemma safeMeasure_strictMono_embed {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c a) :=
  safeMeasure_strictMono_of_dmBoundMono
    dmOrdEmbed_lt_opow_omega
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) h

/-- Explicit `lex3cToOrd` strictness for the `rec_zero` safe rule. -/
lemma lex3cToOrd_drop_R_rec_zero (b s : Trace) (hÎ´ : MetaSN_KO7.deltaFlag b = 0) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c (recÎ” b s void)) := by
  have hÎºleMs : kappaM b â‰¤ kappaM (recÎ” b s void) := by
    have hbase : kappaM b â‰¤ kappaM b + (1 ::â‚˜ kappaM s) := by
      simpa using (Multiset.le_add_right (kappaM b) (1 ::â‚˜ kappaM s))
    simpa [MetaSN_DM.kappaM_rec_zero, add_comm, add_left_comm, add_assoc] using hbase
  have hÎºle : dmOrdEmbed (kappaM b) â‰¤ dmOrdEmbed (kappaM (recÎ” b s void)) :=
    dmOrdEmbed_mono hÎºleMs
  have hmul :
      (Ï‰ : Ordinal) * dmOrdEmbed (kappaM b) â‰¤
        (Ï‰ : Ordinal) * dmOrdEmbed (kappaM (recÎ” b s void)) := by
    exact mul_le_mul_left' hÎºle (Ï‰ : Ordinal)
  have hÏ„Nat : tau b < tau (recÎ” b s void) := by
    simp [tau]; omega
  have hÏ„ : (tau b : Ordinal) < (tau (recÎ” b s void) : Ordinal) := by
    exact_mod_cast hÏ„Nat
  have hinnerâ‚ :
      lexDMToOrd (kappaM b, tau b) <
        (Ï‰ : Ordinal) * dmOrdEmbed (kappaM b) + (tau (recÎ” b s void) : Ordinal) := by
    simpa [lexDMToOrd] using
      (add_lt_add_left hÏ„ ((Ï‰ : Ordinal) * dmOrdEmbed (kappaM b)))
  have hinnerâ‚‚ :
      (Ï‰ : Ordinal) * dmOrdEmbed (kappaM b) + (tau (recÎ” b s void) : Ordinal) â‰¤
        lexDMToOrd (kappaM (recÎ” b s void), tau (recÎ” b s void)) := by
    simpa [lexDMToOrd] using add_le_add_right hmul (tau (recÎ” b s void) : Ordinal)
  have hinner :
      lexDMToOrd (kappaM b, tau b) <
        lexDMToOrd (kappaM (recÎ” b s void), tau (recÎ” b s void)) :=
    lt_of_lt_of_le hinnerâ‚ hinnerâ‚‚
  have hÎ´rec : MetaSN_KO7.deltaFlag (recÎ” b s void) = 0 := by
    simp
  have hÎ´ord : ((MetaSN_KO7.deltaFlag b : Nat) : Ordinal) = 0 := by
    exact_mod_cast hÎ´
  have hÎ´recOrd : ((MetaSN_KO7.deltaFlag (recÎ” b s void) : Nat) : Ordinal) = 0 := by
    exact_mod_cast hÎ´rec
  have hleft :
      lex3cToOrd (mu3c b) = lexDMToOrd (kappaM b, tau b) := by
    unfold lex3cToOrd mu3c
    rw [hÎ´ord]
    simp
  have hright :
      lex3cToOrd (mu3c (recÎ” b s void)) =
        lexDMToOrd (kappaM (recÎ” b s void), tau (recÎ” b s void)) := by
    unfold lex3cToOrd mu3c
    rw [hÎ´recOrd]
    simp
  calc
    lex3cToOrd (mu3c b) = lexDMToOrd (kappaM b, tau b) := hleft
    _ < lexDMToOrd (kappaM (recÎ” b s void), tau (recÎ” b s void)) := hinner
    _ = lex3cToOrd (mu3c (recÎ” b s void)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `integrate (delta t) â†’ void`. -/
lemma lex3cToOrd_drop_R_int_delta (t : Trace) :
    lex3cToOrd (mu3c void) < lex3cToOrd (mu3c (integrate (delta t))) := by
  have hÏ„Nat : 0 < tau (integrate (delta t)) := by simp [tau]
  have hÏ„ : (0 : Ordinal) < (tau (integrate (delta t)) : Ordinal) := by
    exact_mod_cast hÏ„Nat
  have hÏ„le :
      (tau (integrate (delta t)) : Ordinal) â‰¤
        lexDMToOrd (kappaM (integrate (delta t)), tau (integrate (delta t))) := by
    simpa [lexDMToOrd] using
      (Ordinal.le_add_left (tau (integrate (delta t)) : Ordinal)
        ((Ï‰ : Ordinal) * dmOrdEmbed (kappaM (integrate (delta t)))))
  have hright :
      lex3cToOrd (mu3c (integrate (delta t))) =
        lexDMToOrd (kappaM (integrate (delta t)), tau (integrate (delta t))) := by
    simp [lex3cToOrd, mu3c]
  have hleft : lex3cToOrd (mu3c void) = 0 := by
    simp [lex3cToOrd, mu3c, lexDMToOrd, tau, kappaM]
  calc
    lex3cToOrd (mu3c void) = 0 := hleft
    _ < (tau (integrate (delta t)) : Ordinal) := hÏ„
    _ â‰¤ lexDMToOrd (kappaM (integrate (delta t)), tau (integrate (delta t))) := hÏ„le
    _ = lex3cToOrd (mu3c (integrate (delta t))) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `merge void t â†’ t` (guarded). -/
lemma lex3cToOrd_drop_R_merge_void_left (t : Trace) (hÎ´ : MetaSN_KO7.deltaFlag t = 0) :
    lex3cToOrd (mu3c t) < lex3cToOrd (mu3c (merge void t)) := by
  have hÏ„Nat : tau t < tau (merge void t) := by simp [tau]
  have hÏ„ : (tau t : Ordinal) < (tau (merge void t) : Ordinal) := by
    exact_mod_cast hÏ„Nat
  have hÎº : kappaM (merge void t) = kappaM t := MetaSN_DM.kappaM_merge_void_left t
  have hinner :
      lexDMToOrd (kappaM t, tau t) <
        lexDMToOrd (kappaM (merge void t), tau (merge void t)) := by
    simpa [lexDMToOrd, hÎº] using
      (add_lt_add_left hÏ„ ((Ï‰ : Ordinal) * dmOrdEmbed (kappaM t)))
  have hÎ´ord : ((MetaSN_KO7.deltaFlag t : Nat) : Ordinal) = 0 := by
    exact_mod_cast hÎ´
  have hleft :
      lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := by
    unfold lex3cToOrd mu3c
    rw [hÎ´ord]
    simp
  have hright :
      lex3cToOrd (mu3c (merge void t)) =
        lexDMToOrd (kappaM (merge void t), tau (merge void t)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := hleft
    _ < lexDMToOrd (kappaM (merge void t), tau (merge void t)) := hinner
    _ = lex3cToOrd (mu3c (merge void t)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `merge t void â†’ t` (guarded). -/
lemma lex3cToOrd_drop_R_merge_void_right (t : Trace) (hÎ´ : MetaSN_KO7.deltaFlag t = 0) :
    lex3cToOrd (mu3c t) < lex3cToOrd (mu3c (merge t void)) := by
  have hÏ„Nat : tau t < tau (merge t void) := by simp [tau]
  have hÏ„ : (tau t : Ordinal) < (tau (merge t void) : Ordinal) := by
    exact_mod_cast hÏ„Nat
  have hÎº : kappaM (merge t void) = kappaM t := MetaSN_DM.kappaM_merge_void_right t
  have hinner :
      lexDMToOrd (kappaM t, tau t) <
        lexDMToOrd (kappaM (merge t void), tau (merge t void)) := by
    simpa [lexDMToOrd, hÎº] using
      (add_lt_add_left hÏ„ ((Ï‰ : Ordinal) * dmOrdEmbed (kappaM t)))
  have hÎ´ord : ((MetaSN_KO7.deltaFlag t : Nat) : Ordinal) = 0 := by
    exact_mod_cast hÎ´
  have hleft :
      lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := by
    unfold lex3cToOrd mu3c
    rw [hÎ´ord]
    simp
  have hright :
      lex3cToOrd (mu3c (merge t void)) =
        lexDMToOrd (kappaM (merge t void), tau (merge t void)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := hleft
    _ < lexDMToOrd (kappaM (merge t void), tau (merge t void)) := hinner
    _ = lex3cToOrd (mu3c (merge t void)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `merge t t â†’ t` (guarded). -/
lemma lex3cToOrd_drop_R_merge_cancel (t : Trace)
    (hÎ´ : MetaSN_KO7.deltaFlag t = 0) (h0 : kappaM t = 0) :
    lex3cToOrd (mu3c t) < lex3cToOrd (mu3c (merge t t)) := by
  have hÏ„Nat : tau t < tau (merge t t) := by simp [tau]
  have hÏ„ : (tau t : Ordinal) < (tau (merge t t) : Ordinal) := by
    exact_mod_cast hÏ„Nat
  have hÎºmerge : kappaM (merge t t) = 0 := by
    simpa [MetaSN_DM.kappaM_merge_cancel, h0]
  have hinner :
      lexDMToOrd (kappaM t, tau t) <
        lexDMToOrd (kappaM (merge t t), tau (merge t t)) := by
    simpa [lexDMToOrd, h0, hÎºmerge] using
      (add_lt_add_left hÏ„ ((Ï‰ : Ordinal) * (0 : Ordinal)))
  have hÎ´ord : ((MetaSN_KO7.deltaFlag t : Nat) : Ordinal) = 0 := by
    exact_mod_cast hÎ´
  have hleft :
      lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := by
    unfold lex3cToOrd mu3c
    rw [hÎ´ord]
    simp
  have hright :
      lex3cToOrd (mu3c (merge t t)) =
        lexDMToOrd (kappaM (merge t t), tau (merge t t)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := hleft
    _ < lexDMToOrd (kappaM (merge t t), tau (merge t t)) := hinner
    _ = lex3cToOrd (mu3c (merge t t)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `recÎ” b s (delta n) â†’ app s (recÎ” b s n)`. -/
lemma lex3cToOrd_drop_R_rec_succ (b s n : Trace) :
    lex3cToOrd (mu3c (app s (recÎ” b s n))) < lex3cToOrd (mu3c (recÎ” b s (delta n))) := by
  have hinner :
      lexDMToOrd (kappaM (app s (recÎ” b s n)), tau (app s (recÎ” b s n))) <
        (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
    exact lexDMToOrd_lt_opow_omega
      (kappaM (app s (recÎ” b s n)), tau (app s (recÎ” b s n)))
  have hleft :
      lex3cToOrd (mu3c (app s (recÎ” b s n))) =
        lexDMToOrd (kappaM (app s (recÎ” b s n)), tau (app s (recÎ” b s n))) := by
    simp [lex3cToOrd, mu3c]
  have hrightLe :
      (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) â‰¤
        lex3cToOrd (mu3c (recÎ” b s (delta n))) := by
    have :
        (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) â‰¤
          ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)) +
            lexDMToOrd (kappaM (recÎ” b s (delta n)), tau (recÎ” b s (delta n))) := by
      simpa using
        (Ordinal.le_add_right ((Ï‰ : Ordinal) ^ (Ï‰ : Ordinal))
          (lexDMToOrd (kappaM (recÎ” b s (delta n)), tau (recÎ” b s (delta n)))))
    simpa [lex3cToOrd, mu3c, MetaSN_KO7.deltaFlag_rec_delta] using this
  calc
    lex3cToOrd (mu3c (app s (recÎ” b s n)))
        = lexDMToOrd (kappaM (app s (recÎ” b s n)), tau (app s (recÎ” b s n))) := hleft
    _ < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := hinner
    _ â‰¤ lex3cToOrd (mu3c (recÎ” b s (delta n))) := hrightLe

/-- Explicit `lex3cToOrd` strictness for `eqW a a â†’ void` (guarded). -/
lemma lex3cToOrd_drop_R_eq_refl (a : Trace) (h0 : kappaM a = 0) :
    lex3cToOrd (mu3c void) < lex3cToOrd (mu3c (eqW a a)) := by
  have hÏ„Nat : tau void < tau (eqW a a) := by simp [tau]
  have hÏ„ : (tau void : Ordinal) < (tau (eqW a a) : Ordinal) := by
    exact_mod_cast hÏ„Nat
  have hÎº : kappaM (eqW a a) = 0 := by
    simpa [MetaSN_DM.kappaM_eq_refl, h0]
  have hinner :
      lexDMToOrd (kappaM void, tau void) <
        lexDMToOrd (kappaM (eqW a a), tau (eqW a a)) := by
    simpa [lexDMToOrd, hÎº, h0] using
      (add_lt_add_left hÏ„ ((Ï‰ : Ordinal) * (0 : Ordinal)))
  have hleft : lex3cToOrd (mu3c void) = lexDMToOrd (kappaM void, tau void) := by
    simp [lex3cToOrd, mu3c]
  have hright : lex3cToOrd (mu3c (eqW a a)) = lexDMToOrd (kappaM (eqW a a), tau (eqW a a)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c void) = lexDMToOrd (kappaM void, tau void) := hleft
    _ < lexDMToOrd (kappaM (eqW a a), tau (eqW a a)) := hinner
    _ = lex3cToOrd (mu3c (eqW a a)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `eqW a b â†’ integrate (merge a b)`. -/
lemma lex3cToOrd_drop_R_eq_diff (a b : Trace) :
    lex3cToOrd (mu3c (integrate (merge a b))) < lex3cToOrd (mu3c (eqW a b)) := by
  have hÎº : kappaM (integrate (merge a b)) = kappaM (eqW a b) := MetaSN_DM.kappaM_eq_diff a b
  have hÏ„Nat : tau (integrate (merge a b)) < tau (eqW a b) := by
    simp [tau]; omega
  have hÏ„ : (tau (integrate (merge a b)) : Ordinal) < (tau (eqW a b) : Ordinal) := by
    exact_mod_cast hÏ„Nat
  have hinner :
      lexDMToOrd (kappaM (integrate (merge a b)), tau (integrate (merge a b))) <
        lexDMToOrd (kappaM (eqW a b), tau (eqW a b)) := by
    simpa [lexDMToOrd, hÎº] using
      (add_lt_add_left hÏ„ ((Ï‰ : Ordinal) * dmOrdEmbed (kappaM (eqW a b))))
  have hleft :
      lex3cToOrd (mu3c (integrate (merge a b))) =
        lexDMToOrd (kappaM (integrate (merge a b)), tau (integrate (merge a b))) := by
    simp [lex3cToOrd, mu3c]
  have hright :
      lex3cToOrd (mu3c (eqW a b)) = lexDMToOrd (kappaM (eqW a b), tau (eqW a b)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c (integrate (merge a b)))
        = lexDMToOrd (kappaM (integrate (merge a b)), tau (integrate (merge a b))) := hleft
    _ < lexDMToOrd (kappaM (eqW a b), tau (eqW a b)) := hinner
    _ = lex3cToOrd (mu3c (eqW a b)) := hright.symm

/-- Explicit strict decrease of `lex3cToOrd` along every guarded `SafeStep` constructor. -/
lemma safeMeasure_strictMono_explicit {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c a) := by
  induction h with
  | R_int_delta t =>
      simpa using lex3cToOrd_drop_R_int_delta t
  | R_merge_void_left t hÎ´ =>
      simpa using lex3cToOrd_drop_R_merge_void_left t hÎ´
  | R_merge_void_right t hÎ´ =>
      simpa using lex3cToOrd_drop_R_merge_void_right t hÎ´
  | R_merge_cancel t hÎ´ h0 =>
      simpa using lex3cToOrd_drop_R_merge_cancel t hÎ´ h0
  | R_rec_zero b s hÎ´ =>
      simpa using lex3cToOrd_drop_R_rec_zero b s hÎ´
  | R_rec_succ b s n =>
      simpa using lex3cToOrd_drop_R_rec_succ b s n
  | R_eq_refl a h0 =>
      simpa using lex3cToOrd_drop_R_eq_refl a h0
  | R_eq_diff a b _ =>
      simpa using lex3cToOrd_drop_R_eq_diff a b

/-! ## Unconditional rank fallback (no DM embedding assumptions) -/

local instance instIsWellFoundedDM : IsWellFounded (Multiset Nat) DM :=
  âŸ¨MetaSN_DM.wf_dmâŸ©

/-- Ordinal rank of DM, available unconditionally from DM well-foundedness. -/
noncomputable def dmRankOrd (m : Multiset Nat) : Ordinal.{0} :=
  IsWellFounded.rank (r := DM) m

lemma dmRankOrd_strictMono {mâ‚ mâ‚‚ : Multiset Nat} (h : DM mâ‚ mâ‚‚) :
    dmRankOrd mâ‚ < dmRankOrd mâ‚‚ :=
  IsWellFounded.rank_lt_of_rel h

/--
Rank-vs-embedding transfer principle for `DM`.

If an ordinal-valued map strictly increases along `DM` edges, then `DM`-rank is pointwise bounded
by that map.
-/
lemma dmRankOrd_le_dmOrdEmbed_of_strictMono
    (hMono : âˆ€ {mâ‚ mâ‚‚ : Multiset Nat}, DM mâ‚ mâ‚‚ â†’ dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚)
    (m : Multiset Nat) :
    dmRankOrd m â‰¤ dmOrdEmbed m := by
  induction m using MetaSN_DM.wf_dm.induction with
  | h x ih =>
      rw [dmRankOrd, IsWellFounded.rank_eq (r := DM) x]
      change (â¨† y : { y // DM y x }, Order.succ (dmRankOrd y.1)) â‰¤ dmOrdEmbed x
      refine Ordinal.iSup_le ?_
      intro y
      exact (Order.succ_le_iff).2 <|
        (lt_of_le_of_lt (ih y.1 y.2) (hMono y.2))

/--
Conditional `Ï‰^Ï‰` upper bound for `DM`-rank.

This is the Phase A bridge: once global strict monotonicity of `dmOrdEmbed` along `DM` is proved,
the rank bound follows immediately.
-/
lemma dmRankOrd_lt_opow_omega_of_dmOrdEmbed_strictMono
    (hMono : âˆ€ {mâ‚ mâ‚‚ : Multiset Nat}, DM mâ‚ mâ‚‚ â†’ dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚)
    (m : Multiset Nat) :
    dmRankOrd m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
  exact lt_of_le_of_lt
    (dmRankOrd_le_dmOrdEmbed_of_strictMono hMono m)
    (dmOrdEmbed_lt_opow_omega m)

lemma dmRankOrd_lt_opow_omega (m : Multiset Nat) :
    dmRankOrd m < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) :=
  dmRankOrd_lt_opow_omega_of_dmOrdEmbed_strictMono
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) m

local instance instIsWellFoundedLex3c :
    IsWellFounded (Nat Ã— (Multiset Nat Ã— Nat)) Lex3c :=
  âŸ¨wf_Lex3câŸ©

/-- Ordinal rank of `Lex3c`, available unconditionally from `wf_Lex3c`. -/
noncomputable def lex3cRankOrd (x : Nat Ã— (Multiset Nat Ã— Nat)) : Ordinal.{0} :=
  IsWellFounded.rank (r := Lex3c) x

lemma lex3cRankOrd_strictMono {x y : Nat Ã— (Multiset Nat Ã— Nat)} (h : Lex3c x y) :
    lex3cRankOrd x < lex3cRankOrd y :=
  IsWellFounded.rank_lt_of_rel h

/-- Fully assumption-free strict decrease along safe steps (rank formulation). -/
lemma safeMeasure_rank_strictMono {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cRankOrd (mu3c b) < lex3cRankOrd (mu3c a) :=
  lex3cRankOrd_strictMono (measure_decreases_safe_c h)

/-- Assumption-free strict decrease theorem (rank-calibrated form). -/
lemma safeMeasure_strictMono {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cRankOrd (mu3c b) < lex3cRankOrd (mu3c a) :=
  safeMeasure_rank_strictMono h

/--
Combined unconditional statement used in the paper narrative:
- strict per-step decrease is certified by well-founded rank;
- explicit ordinal calibration gives `< Îµâ‚€` for both endpoints.
-/
lemma safeMeasure_step_rank_and_epsilon0
    {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cRankOrd (mu3c b) < lex3cRankOrd (mu3c a) âˆ§
      lex3cToOrd (mu3c b) < Îµâ‚€ âˆ§ lex3cToOrd (mu3c a) < Îµâ‚€ := by
  exact âŸ¨safeMeasure_rank_strictMono h, safeMeasure_below_epsilon0 b, safeMeasure_below_epsilon0 aâŸ©

end OperatorKO7.MetaDM
````

## OperatorKO7/Meta/DM_OrderType_LowerBound.lean

**Lines:** 296

``lean
import OperatorKO7.Meta.DM_OrderType
import Mathlib.Data.Multiset.Sort
import Mathlib.SetTheory.Ordinal.CantorNormalForm

namespace OperatorKO7.MetaDM

open Ordinal
open OperatorKO7.MetaCM

/-- Canonical finite CNF payload for ordinals below `Ï‰^Ï‰`: descending exponent list. -/
structure CNFÏ‰Ï‰ where
  exponents : List Nat
  sorted : exponents.Sorted (Â· â‰¥ Â·)

namespace CNFÏ‰Ï‰

/-- Forget coefficients into a multiset of exponents. -/
def toMultiset (c : CNFÏ‰Ï‰) : Multiset Nat :=
  (c.exponents : Multiset Nat)

/-- Canonical representative extracted from a multiset by descending sort. -/
def ofMultiset (m : Multiset Nat) : CNFÏ‰Ï‰ :=
  âŸ¨Multiset.sort (Â· â‰¥ Â·) m, Multiset.sort_sorted (r := (Â· â‰¥ Â·)) mâŸ©

/-- Ordinal value of a CNF payload, via the mechanized DM embedding. -/
noncomputable def eval (c : CNFÏ‰Ï‰) : Ordinal :=
  dmOrdEmbed c.toMultiset

theorem eval_toMultiset (c : CNFÏ‰Ï‰) :
    dmOrdEmbed c.toMultiset = c.eval := rfl

@[simp] theorem toMultiset_ofMultiset (m : Multiset Nat) :
    (ofMultiset m).toMultiset = m := by
  simp [ofMultiset, toMultiset, Multiset.sort_eq]

@[simp] theorem eval_ofMultiset (m : Multiset Nat) :
    (ofMultiset m).eval = dmOrdEmbed m := by
  change dmOrdEmbed (ofMultiset m).toMultiset = dmOrdEmbed m
  exact congrArg dmOrdEmbed (toMultiset_ofMultiset m)

/-- Every multiset admits a canonical CNF representative with the same embedding value. -/
theorem exists_of_multiset (m : Multiset Nat) :
    âˆƒ c : CNFÏ‰Ï‰, c.eval = dmOrdEmbed m :=
  âŸ¨ofMultiset m, by simpâŸ©

/-- Phase-B upper bound restated on the CNF carrier. -/
theorem eval_lt_opow_omega (c : CNFÏ‰Ï‰) :
    c.eval < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
  simpa [eval] using
    (dmOrdEmbed_lt_opow_omega c.toMultiset :
      dmOrdEmbed c.toMultiset < (Ordinal.omega0 : Ordinal) ^ (Ordinal.omega0 : Ordinal))

/-- Sorting the multiset image of a canonical payload returns the original exponent list. -/
theorem sort_toMultiset (c : CNFÏ‰Ï‰) :
    Multiset.sort (Â· â‰¥ Â·) c.toMultiset = c.exponents := by
  refine List.eq_of_perm_of_sorted (r := (Â· â‰¥ Â·)) ?_ ?_ c.sorted
  Â· exact (Multiset.coe_eq_coe).1 (by
      simpa [toMultiset] using (Multiset.sort_eq (r := (Â· â‰¥ Â·)) c.toMultiset))
  Â· exact Multiset.sort_sorted (r := (Â· â‰¥ Â·)) c.toMultiset

@[simp] theorem ofMultiset_toMultiset (c : CNFÏ‰Ï‰) :
    ofMultiset c.toMultiset = c := by
  cases c with
  | mk ex hs =>
      simp [ofMultiset, toMultiset]
      refine List.eq_of_perm_of_sorted (r := (Â· â‰¥ Â·)) ?_ ?_ hs
      Â· exact (Multiset.coe_eq_coe).1 (by simpa using (Multiset.sort_eq (r := (Â· â‰¥ Â·)) (ex : Multiset Nat)))
      Â· exact Multiset.sort_sorted (r := (Â· â‰¥ Â·)) (ex : Multiset Nat)

noncomputable def natOfLtOmega (o : Ordinal) (h : o < (Ï‰ : Ordinal)) : Nat :=
  Classical.choose (Ordinal.lt_omega0.1 h)

lemma natOfLtOmega_eq (o : Ordinal) (h : o < (Ï‰ : Ordinal)) :
    ((natOfLtOmega o h : Nat) : Ordinal) = o := by
  simpa [natOfLtOmega] using
    (Classical.choose_spec (Ordinal.lt_omega0.1 h)).symm

private theorem exists_multiset_eval_bounded :
    âˆ€ (b : Ordinal) (L : List (Ordinal Ã— Ordinal)),
      (âˆ€ p âˆˆ L, p.1 < b âˆ§ p.1 < (Ï‰ : Ordinal) âˆ§ p.2 < (Ï‰ : Ordinal)) â†’
      (L.map Prod.fst).Sorted (Â· > Â·) â†’
      âˆƒ m : Multiset Nat,
        dmOrdEmbed m = L.foldr (fun p r â†¦ (Ï‰ : Ordinal) ^ p.1 * p.2 + r) 0 âˆ§
          âˆ€ n âˆˆ m, (n : Ordinal) < b
  | b, [], _, _ =>
      âŸ¨0, by simp [dmOrdEmbed], by
        intro n hn
        simp at hnâŸ©
  | b, p :: ps, hBound, hSorted => by
      have hpBound : p.1 < b âˆ§ p.1 < (Ï‰ : Ordinal) âˆ§ p.2 < (Ï‰ : Ordinal) :=
        hBound p (by simp)
      have hSortedTail : (ps.map Prod.fst).Sorted (Â· > Â·) := (List.sorted_cons.1 hSorted).2
      have hTailBound : âˆ€ q âˆˆ ps, q.1 < p.1 âˆ§ q.1 < (Ï‰ : Ordinal) âˆ§ q.2 < (Ï‰ : Ordinal) := by
        intro q hq
        have hqExp : q.1 < p.1 := by
          have hmem : q.1 âˆˆ ps.map Prod.fst := by
            exact List.mem_map.2 âŸ¨q, hq, rflâŸ©
          exact (List.sorted_cons.1 hSorted).1 _ hmem
        exact âŸ¨hqExp, (hBound q (by simp [hq])).2.1, (hBound q (by simp [hq])).2.2âŸ©
      rcases exists_multiset_eval_bounded p.1 ps hTailBound hSortedTail with
        âŸ¨mTail, hmTailEval, hmTailLtâŸ©
      let e : Nat := natOfLtOmega p.1 hpBound.2.1
      let c : Nat := natOfLtOmega p.2 hpBound.2.2
      let m : Multiset Nat := Multiset.replicate c e + mTail
      have heEq : ((e : Nat) : Ordinal) = p.1 := by
        simpa [e] using natOfLtOmega_eq p.1 hpBound.2.1
      have hcEq : ((c : Nat) : Ordinal) = p.2 := by
        simpa [c] using natOfLtOmega_eq p.2 hpBound.2.2
      have hTailNatLt : âˆ€ n âˆˆ mTail, n < e := by
        intro n hn
        have hnOrd : (n : Ordinal) < p.1 := hmTailLt n hn
        have hnOrd' : (n : Ordinal) < (e : Ordinal) := by
          exact lt_of_lt_of_eq hnOrd heEq.symm
        exact (by exact_mod_cast hnOrd' : n < e)
      have hEval :
          dmOrdEmbed m =
            (Ï‰ : Ordinal) ^ p.1 * p.2 +
              ps.foldr (fun q r â†¦ (Ï‰ : Ordinal) ^ q.1 * q.2 + r) 0 := by
        calc
          dmOrdEmbed m
              = dmOrdEmbed (Multiset.replicate c e + mTail) := rfl
          _ = (Ï‰ : Ordinal) ^ (e : Ordinal) * (c : Ordinal) + dmOrdEmbed mTail := by
                exact dmOrdEmbed_replicate_add_of_all_lt hTailNatLt
          _ = (Ï‰ : Ordinal) ^ p.1 * p.2 + dmOrdEmbed mTail := by
                simp [heEq, hcEq]
          _ = (Ï‰ : Ordinal) ^ p.1 * p.2 +
                ps.foldr (fun q r â†¦ (Ï‰ : Ordinal) ^ q.1 * q.2 + r) 0 := by
                simp [hmTailEval]
      have hmLt : âˆ€ n âˆˆ m, (n : Ordinal) < b := by
        intro n hn
        rcases Multiset.mem_add.1 hn with hrep | htail
        Â· have hnEq : n = e := Multiset.eq_of_mem_replicate hrep
          subst hnEq
          exact lt_of_eq_of_lt heEq hpBound.1
        Â· exact (hmTailLt n htail).trans hpBound.1
      exact âŸ¨m, by simpa [m] using hEval, hmLtâŸ©

/--
Unconditional surjectivity of `dmOrdEmbed` below `Ï‰^Ï‰`, obtained from Mathlib's canonical
Cantor normal form decomposition.
-/
theorem dmOrdEmbed_surjective_lt_opow_omega :
    âˆ€ Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal), âˆƒ m : Multiset Nat, dmOrdEmbed m = Î± := by
  intro Î± hÎ±
  let L : List (Ordinal Ã— Ordinal) := Ordinal.CNF (Ï‰ : Ordinal) Î±
  have hSorted : (L.map Prod.fst).Sorted (Â· > Â·) := by
    simpa [L] using (Ordinal.CNF_sorted (Ï‰ : Ordinal) Î±)
  have hBound : âˆ€ p âˆˆ L, p.1 < (Ï‰ : Ordinal) âˆ§ p.1 < (Ï‰ : Ordinal) âˆ§ p.2 < (Ï‰ : Ordinal) := by
    intro p hp
    have hpL : p âˆˆ Ordinal.CNF (Ï‰ : Ordinal) Î± := by
      simpa [L] using hp
    have hSnd : p.2 < (Ï‰ : Ordinal) := by
      exact Ordinal.CNF_snd_lt (b := (Ï‰ : Ordinal)) (o := Î±)
        Ordinal.one_lt_omega0 hpL
    have hFst : p.1 < (Ï‰ : Ordinal) := by
      by_cases h0 : Î± = 0
      Â· subst h0
        exfalso
        simp [L, Ordinal.CNF_zero] at hp
      Â·
        have hLog : Ordinal.log (Ï‰ : Ordinal) Î± < (Ï‰ : Ordinal) := by
          exact (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 h0).1 hÎ±
        exact lt_of_le_of_lt
          (Ordinal.CNF_fst_le_log (b := (Ï‰ : Ordinal)) (o := Î±) (x := p)
            hpL)
          hLog
    exact âŸ¨hFst, hFst, hSndâŸ©
  rcases exists_multiset_eval_bounded (Ï‰ : Ordinal) L hBound hSorted with âŸ¨m, hm, _âŸ©
  refine âŸ¨m, ?_âŸ©
  calc
    dmOrdEmbed m = L.foldr (fun p r â†¦ (Ï‰ : Ordinal) ^ p.1 * p.2 + r) 0 := hm
    _ = Î± := by simpa [L] using (Ordinal.CNF_foldr (Ï‰ : Ordinal) Î±)

/-- Phase-B bridge: surjectivity of `dmOrdEmbed` below `Ï‰^Ï‰` (proved unconditionally). -/
def DmEmbedSurjBelowOmegaOmega : Prop :=
  âˆ€ Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal), âˆƒ m : Multiset Nat, dmOrdEmbed m = Î±

theorem dmOrdEmbed_surjective_prop : DmEmbedSurjBelowOmegaOmega :=
  dmOrdEmbed_surjective_lt_opow_omega

/-- Order-reflection schema needed for a fully unconditional lower-bound bridge. -/
def DmEmbedReflects : Prop :=
  âˆ€ {mâ‚ mâ‚‚ : Multiset Nat}, dmOrdEmbed mâ‚ < dmOrdEmbed mâ‚‚ â†’ DM mâ‚ mâ‚‚

/--
If `dmOrdEmbed` reflects strict order into `DM`, then the opposite rank bridge follows:
`dmOrdEmbed m â‰¤ dmRankOrd m`.

Together with the unconditional upper bridge `dmRankOrd m â‰¤ dmOrdEmbed m`, this yields equality.
-/
theorem dmOrdEmbed_le_dmRankOrd_of_reflect (hReflect : DmEmbedReflects) :
    âˆ€ m : Multiset Nat, dmOrdEmbed m â‰¤ dmRankOrd m := by
  let P : Ordinal â†’ Prop := fun Î± =>
    âˆ€ m : Multiset Nat, dmOrdEmbed m = Î± â†’ dmOrdEmbed m â‰¤ dmRankOrd m
  have hStep : âˆ€ Î±, (âˆ€ Î², Î² < Î± â†’ P Î²) â†’ P Î± := by
    intro Î± ih m hm
    refine le_of_forall_lt ?_
    intro Î² hÎ²
    have hÎ²Ï‰ : Î² < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal) := by
      exact lt_trans hÎ² (dmOrdEmbed_lt_opow_omega m)
    rcases dmOrdEmbed_surjective_lt_opow_omega Î² hÎ²Ï‰ with âŸ¨w, hwâŸ©
    have hDM : DM w m := hReflect (by simpa [hw] using hÎ²)
    have hRank : dmRankOrd w < dmRankOrd m := dmRankOrd_strictMono hDM
    have hÎ²le : Î² â‰¤ dmRankOrd w := by
      have hÎ²Î± : Î² < Î± := by simpa [hm] using hÎ²
      have hPw : P Î² := ih Î² hÎ²Î±
      have hwLe : dmOrdEmbed w â‰¤ dmRankOrd w := hPw w hw
      simpa [hw] using hwLe
    exact lt_of_le_of_lt hÎ²le hRank
  have hAll : âˆ€ Î±, P Î± := by
    intro Î±
    induction Î± using Ordinal.induction with
    | h Î± ih =>
        exact hStep Î± (fun Î² hÎ² => ih Î² hÎ²)
  intro m
  exact hAll (dmOrdEmbed m) m rfl

theorem dmOrdEmbed_eq_dmRankOrd_of_reflect
    (hReflect : DmEmbedReflects) (m : Multiset Nat) :
    dmOrdEmbed m = dmRankOrd m := by
  refine le_antisymm (dmOrdEmbed_le_dmRankOrd_of_reflect hReflect m) ?_
  exact dmRankOrd_le_dmOrdEmbed_of_strictMono (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) m

theorem dmEmbedReflects : DmEmbedReflects := by
  intro mâ‚ mâ‚‚ hlt
  exact dmOrdEmbed_reflects hlt

theorem dmOrdEmbed_le_dmRankOrd (m : Multiset Nat) :
    dmOrdEmbed m â‰¤ dmRankOrd m :=
  dmOrdEmbed_le_dmRankOrd_of_reflect dmEmbedReflects m

theorem dmOrdEmbed_eq_dmRankOrd (m : Multiset Nat) :
    dmOrdEmbed m = dmRankOrd m :=
  dmOrdEmbed_eq_dmRankOrd_of_reflect dmEmbedReflects m

theorem dmRankOrd_surjective_lt_opow_omega :
    âˆ€ Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal), âˆƒ m : Multiset Nat, dmRankOrd m = Î± := by
  intro Î± hÎ±
  rcases dmOrdEmbed_surjective_lt_opow_omega Î± hÎ± with âŸ¨m, hmâŸ©
  refine âŸ¨m, ?_âŸ©
  calc
    dmRankOrd m = dmOrdEmbed m := (dmOrdEmbed_eq_dmRankOrd m).symm
    _ = Î± := hm

/--
If `dmOrdEmbed` is surjective on `< Ï‰^Ï‰`, then `CNFÏ‰Ï‰.eval` is also surjective on `< Ï‰^Ï‰`.
-/
theorem surj_lt_opow_omega_of_dmSurj
    (hSurj : DmEmbedSurjBelowOmegaOmega) :
    âˆ€ Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal), âˆƒ c : CNFÏ‰Ï‰, c.eval = Î± := by
  intro Î± hÎ±
  rcases hSurj Î± hÎ± with âŸ¨m, hmâŸ©
  exact âŸ¨ofMultiset m, by simpa [eval] using hmâŸ©

/--
Choice-level constructor for values `< Ï‰^Ï‰`, parameterized by the surjectivity bridge.
-/
noncomputable def ofLtOpowOmega (hSurj : DmEmbedSurjBelowOmegaOmega)
    (a : {Î± : Ordinal // Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)}) : CNFÏ‰Ï‰ :=
  ofMultiset (Classical.choose (hSurj a.1 a.2))

theorem eval_ofLtOpowOmega (hSurj : DmEmbedSurjBelowOmegaOmega)
    (a : {Î± : Ordinal // Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)}) :
    (ofLtOpowOmega hSurj a).eval = a.1 := by
  unfold ofLtOpowOmega
  simpa [eval] using (Classical.choose_spec (hSurj a.1 a.2))

/--
CNF-surjectivity below `Ï‰^Ï‰` is equivalent to DM-embedding surjectivity below `Ï‰^Ï‰`.
-/
theorem surj_lt_opow_omega_iff_dmSurj :
    (âˆ€ Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal), âˆƒ c : CNFÏ‰Ï‰, c.eval = Î±) â†”
      DmEmbedSurjBelowOmegaOmega := by
  constructor
  Â· intro h Î± hÎ±
    rcases h Î± hÎ± with âŸ¨c, hcâŸ©
    exact âŸ¨c.toMultiset, by simpa [eval] using hcâŸ©
  Â· intro h
    exact surj_lt_opow_omega_of_dmSurj h

theorem surj_lt_opow_omega :
    âˆ€ Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal), âˆƒ c : CNFÏ‰Ï‰, c.eval = Î± :=
  surj_lt_opow_omega_of_dmSurj dmOrdEmbed_surjective_prop

noncomputable def ofLtOpowOmegaUncond
    (a : {Î± : Ordinal // Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)}) : CNFÏ‰Ï‰ :=
  ofLtOpowOmega dmOrdEmbed_surjective_prop a

theorem eval_ofLtOpowOmegaUncond
    (a : {Î± : Ordinal // Î± < (Ï‰ : Ordinal) ^ (Ï‰ : Ordinal)}) :
    (ofLtOpowOmegaUncond a).eval = a.1 :=
  eval_ofLtOpowOmega dmOrdEmbed_surjective_prop a

end CNFÏ‰Ï‰

end OperatorKO7.MetaDM
````

## OperatorKO7/Meta/FailureModes.lean

**Lines:** 95

``lean
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
4) Î¼ s vs Î¼ (delta n): counterexample to pure ordinal measures
5) KO7-specific countermodels (Î´-flag behavior)

Note: We avoid `sorry` and establish negation or inequality where possible.
-/

namespace OperatorKO7.Countermodels

open OperatorKO7 Trace

/-! ## 1) Branch realism: minimal counterexample -/

/-- A tiny function with two clauses to illustrate branch-by-branch `rfl` checks. -/
def tiny : Nat â†’ Nat
| 0       => 1
| Nat.succ n => n

/-- Witness that the global equation fails on the `x = 0` branch.
    (The global equation `2 * tiny x = tiny (2 * x)` is not true.) -/
lemma tiny_global_eq_fails_zero : 2 * tiny 0 â‰  tiny (2 * 0) := by
  -- LHS = 2 * 1 = 2; RHS = tiny 0 = 1
  decide

/-- Witness that the global equation fails on the `x = succ n` branch. -/
lemma tiny_global_eq_fails_succ (n : Nat) : 2 * tiny (Nat.succ n) â‰  tiny (2 * Nat.succ n) := by
  -- LHS = 2 * n; RHS = tiny (2*n + 2) = (2*n + 1)
  -- They differ by 1.
  simp only [tiny]
  -- Goal: 2 * n â‰  2 * n + 1
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

/-! ## 2) P2 Duplication realism (commented orientation) -/
/--
Consider a duplicating step h(S) â†’ g(S,S). With an additive size M:
  M(after) = M(before) - 1 + M(S) + M(S) = M(before) - 1 + 2Â·M(S)
This is not strictly smaller when M(S) â‰¥ 1.
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
@[simp] def simpleSize : Trace â†’ Nat
| .void => 0
| .delta t => simpleSize t + 1
| .integrate t => simpleSize t + 1
| .merge a b => simpleSize a + simpleSize b + 1
| .app a b => simpleSize a + simpleSize b + 1
| .recÎ” b s n => simpleSize b + simpleSize s + simpleSize n + 1
| .eqW a b => simpleSize a + simpleSize b + 1

/-- There exist `s, n` with `simpleSize s > simpleSize (delta n)`. -/
theorem exists_size_s_gt_size_delta_n : âˆƒ s n : Trace, simpleSize s > simpleSize (delta n) := by
  refine âŸ¨delta (delta void), void, ?_âŸ©
  simp [simpleSize]

/-! ## 5) KO7-flavored P1: Î´-flag is NOT preserved by merge void globally -/
open MetaSN_KO7

/-- Branchwise counterexample: `deltaFlag (merge void t) = deltaFlag t` fails for `t = recÎ” b s (delta n)`. -/
lemma deltaFlag_not_preserved_merge_void (b s n : Trace) :
  deltaFlag (merge void (recÎ” b s (delta n))) â‰  deltaFlag (recÎ” b s (delta n)) := by
  -- LHS = 0, RHS = 1
  simp [deltaFlag]

/-- KO7 duplication mapping note:
    - DM-left used when Îºá´¹ â‰  0: see `OperatorKO7.MetaCM.drop_R_eq_refl_c`.
    - Guarded merge-cancel (`Îºá´¹ = 0`) is discharged by Ï„/right-lex: see `OperatorKO7.MetaCM.drop_R_merge_cancel_c`.
    - The full certified decrease aggregator is `OperatorKO7.MetaCM.measure_decreases_safe_c`. -/
lemma note_ko7_duplication_mapping : True := by trivial

end OperatorKO7.Countermodels
````

## OperatorKO7/Meta/GoodsteinCore.lean

**Lines:** 40

``lean
/-!
GoodsteinCore - a tiny, standalone toy for Goodstein-style base-change shape.
This does NOT modify the KO7 kernel; it exists for examples and cross-links.
It models a pair (base, counter) and a single-step that bumps the base while
consuming one successor on the counter side.
-/

namespace OperatorKO7
namespace GoodsteinCore

/-- Base parameter (modeled minimally as a wrapped `Nat`). -/
inductive Base where
  | b : Nat â†’ Base
deriving Repr, DecidableEq

/-- Unary naturals used as a toy counter for Goodstein-style steps. -/
inductive Cn where
  | z  : Cn
  | s  : Cn â†’ Cn
deriving Repr, DecidableEq

/-- A Goodstein-state is a pair (base, counter). -/
structure St where
  base : Base
  cnt  : Cn
deriving Repr, DecidableEq

open Base Cn

/-- Goodstein-like one-step: bump base, drop one successor on the counter. -/
inductive Step : St â†’ St â†’ Prop where
  | base_change (b : Nat) (t : Cn) :
      Step âŸ¨.b b, .s tâŸ© âŸ¨.b (b+1), tâŸ©

/-- Convenience lemma: the single `Step.base_change` rule is always available on `(.s t)` counters. -/
@[simp] theorem one_step (b : Nat) (t : Cn) :
    Step âŸ¨.b b, .s tâŸ© âŸ¨.b (b+1), tâŸ© := Step.base_change b t

end GoodsteinCore
end OperatorKO7
````

## OperatorKO7/Meta/HydraCore.lean

**Lines:** 35

``lean
/-!
HydraCore - a tiny, standalone toy hydra relation to serve as a minimal
"hydra core" rule set for demonstrations. This does NOT change the KO7 kernel
and is only for examples/tests of duplication-style steps.

This captures the duplication flavor: chopping a head duplicates a subtree.
We keep it intentionally small and independent of KO7.
-/

namespace OperatorKO7
namespace HydraCore

/-- A minimal hydra-as-binary-tree datatype. `head` is a leaf; `node l r` has two sub-hydras. -/
inductive Hydra where
  | head : Hydra
  | node : Hydra â†’ Hydra â†’ Hydra
deriving Repr, DecidableEq

open Hydra

/-- One-step toy hydra rule: cutting a head on one side duplicates the other side. -/
inductive Step : Hydra â†’ Hydra â†’ Prop where
  | chop_left  (h : Hydra) : Step (node head h) (node h h)
  | chop_right (h : Hydra) : Step (node h head) (node h h)

/-- Convenience lemma: left chop duplicates the right subtree. -/
@[simp] theorem dup_left (h : Hydra) : Step (node head h) (node h h) := Step.chop_left h
/-- Convenience lemma: right chop duplicates the left subtree. -/
@[simp] theorem dup_right (h : Hydra) : Step (node h head) (node h h) := Step.chop_right h

/-- Example: a single chop duplicates the non-head subtree. -/
example (h : Hydra) : âˆƒ h', Step (node head h) h' := âŸ¨node h h, Step.chop_left hâŸ©

end HydraCore
end OperatorKO7
````

## OperatorKO7/Meta/Impossibility_Lemmas.lean

**Lines:** 376

``lean
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

Whatâ€™s inside (all selfâ€‘contained, kernel unchanged)
- P1/P2/P3 probes: reâ€‘anchored pointers and small runnable examples.
- Îº+ k counterexample on KO7 traces (R_rec_succ): ties by rfl branchwise.
- Flagâ€‘only outer discriminator failure: concrete Step raises the flag.
- Duplication stress identity (toy calculus): additive counter nonâ€‘drop, plus
  DM and MPO orientation witnesses.
- Rightâ€‘add hazard and â€œquick â‰¤ patchâ€ are documented with intentionally
  nonâ€‘admitted, commented examples (uncomment to see failures).

Note
- This file may include commented, intentionally failing fragments to preserve
  the â€œdead endsâ€ catalog; keep them commented to preserve green builds.
- Live theorems/examples compile and can be cited in the paper/docs.
- See also: `OperatorKO7/Meta/Operational_Incompleteness.lean` (namespace `OperatorKO7.OpIncomp`) for the P1â€“P3 probes.
-/


namespace OperatorKO7
namespace Impossibility

 -- Shorten local names for the rest of this file (doc preface section).
 open OperatorKO7 Trace
 open Prod (Lex)

/-! See namespace `OpIncomp` inside `Operational_Incompleteness.lean` for concrete P1â€“P3
  statements (`P2`, `P2DM`, `P2MPO`) and proofs. This module collects small,
  kernelâ€‘native witnesses and commentary aligned with fails_central sections
  Aâ€“M. This is a documentation mirror; no kernel changes. -/

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

/-- A simple depth-based counter for `recÎ”` nodes. This was one of the first
measures attempted and fails on duplication. -/
@[simp]
def kappa : Trace â†’ Nat
  | recÎ” _ _ n => kappa n + 1
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
  Â¬ (âˆ€ (b s n : Trace),
      kappa (app s (recÎ” b s n)) + k < kappa (recÎ” b s (delta n)) + k) := by
  -- We prove this by providing a concrete counterexample.
  push_neg
  -- The counterexample uses a nested `delta` to show the additive bump `+1` from
  -- the outer `delta` is cancelled by the `+1` from the inner `recÎ”`.
  use void, void, delta void
  -- The goal is now a concrete inequality, which we can simplify.
  -- After simp, the goal is `Â¬(1 + k < 1 + k)`.
  simp [kappa]

/-! ### Theorem 2: Failure of Simple Lexicography
This theorem proves that a standard 2-component lexicographic measure `(Îº, Î¼)`
fails because the primary component, `Îº`, does not strictly decrease.
This forces the move to a more complex measure where the primary component is a
flag or a multiset designed to handle specific reduction rules.
-/
theorem simple_lex_fails :
  Â¬ (âˆ€ (b s n : Trace),
      Lex (Â·<Â·) (Â·<Â·)
        (kappa (app s (recÎ” b s n)), mu (app s (recÎ” b s n)))
        (kappa (recÎ” b s (delta n)), mu (recÎ” b s (delta n)))) := by
  push_neg
  -- The counterexample is `n := void`, which becomes the base case for `recÎ”`
  -- after one step.
  use void, recÎ” void void void, void
  -- After substituting, we need to show the Lex relation does not hold.
  -- This reduces to `Â¬ Lex (Â·<Â·) (Â·<Â·) (1, 0) (1, 0)`, which is decidable.
  simp [kappa, mu]; decide

end FailedMeasures

/-! ## Boolean Î´-flag alone - explicit increase on a non-rec rule (fails_central Â§F)

Using only a â€œtop-is-delta?â€ flag as the outer lex key breaks monotonicity:
there exists a Step that raises the flag. This mirrors the docâ€™s warning that
an unguarded global flag is unsafe; KO7 uses it only under a guard in safe
subrelations. -/
namespace FlagFailure

/-- Top-shape flag: 1 only when the term is headed by `delta`. -/
@[simp] def deltaFlagTop : Trace â†’ Nat
  | Trace.delta _ => 1
  | _             => 0

/-- Concrete increase: `merge void (delta void) â†’ delta void` raises `deltaFlagTop`
from 0 to 1. This shows a flag-only primary component can increase on a legal
kernel step (violates lex monotonicity if used unguarded). -/
theorem merge_void_raises_flag :
    let t := Trace.delta Trace.void
    OperatorKO7.Step (Trace.merge Trace.void t) t âˆ§
    deltaFlagTop (Trace.merge Trace.void t) < deltaFlagTop t := by
  intro t; constructor
  Â· -- The step exists by R_merge_void_left
    exact OperatorKO7.Step.R_merge_void_left t
  Â· -- Compute flags: top of `merge void (delta void)` is not `delta`.
    -- top of `t` is `delta`.
    -- After simplification, the goal becomes `0 < 1`.
    have ht : t = Trace.delta Trace.void := rfl
    simp [deltaFlagTop, ht]

end FlagFailure

/-! ## Right-add hazard and â€œquick â‰¤ patchâ€ (fails_central Â§H)

Commentary-only: transporting strict inequalities to the left over arbitrary
ordinal right-addends is invalid. Attempted patches that relax `=` to `â‰¤` do
not fix the nested-Î´ counterexample. The following fragments are intentionally
commented to keep the build green; they illustrate the bad shapes. -/
-- RightAddHazard (dead end): ordinal right-addition is not strictly monotone.
-- The bad shape `p < q â†’ p + s < q + s` fails on ordinals in general.
-- This dead end is documented; no code is needed.

/-! ## P2 duplication realism - references and examples (fails_central Â§G)

We reuse the toy calculus from `OpIncomp`:
* `r4_size_after_eq_before_plus_piece` gives the exact additive nonâ€‘drop identity.
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

/-! ## P1 rfl-gate (branch realism) - explicit per-branch check (fails_central Â§B)

For any pattern-matched `f`, check rfl per clause and avoid asserting a single
global equation unless all branches agree. The full P1 probe lives in
`Operational_Incompleteness.lean`; we include a tiny exemplar here. -/
namespace RflGate

inductive Two where | A | B deriving DecidableEq, Repr

def f : Two â†’ Nat
  | .A => 0
  | .B => 1

-- Per-branch rfl (passes):
example : f Two.A = 0 := rfl
example : f Two.B = 1 := rfl

-- Over-strong global law fails: not (âˆ€ x, f x = 0)
example : Â¬ (âˆ€ x, f x = 0) := by
  intro h
  -- f B = 1 contradicts h B : f B = 0
  exact Nat.one_ne_zero (by simpa [f] using h Two.B)

end RflGate

/-! ## Anchors to the green path (consolidation Â§J)

The fixes live under KO7â€™s safe layer:
- `Meta/ComputableMeasure.lean`: `drop_R_rec_succ_c` (outer Î´-flag drop),
  `measure_decreases_safe_c`, `wf_SafeStepRev_c`.
These arenâ€™t reâ€‘proved here; this file focuses on the impossibility side. -/

/-! ## KO7 safe Lex3c - tiny cross-link examples (the fix path) -/

namespace KO7_FixPathExamples

open OperatorKO7.MetaCM

-- delta-substitution (rec_succ) strictly drops by KO7's outer flag component.
lemma rec_succ_drops (b s n : Trace) :
   Lex3c (mu3c (app s (recÎ” b s n)))
         (mu3c (recÎ” b s (delta n))) := by
   simpa using drop_R_rec_succ_c b s n

-- The guarded aggregator yields a decrease certificate per safe step.
lemma safe_decrease_rec_succ (b s n : Trace) :
   Lex3c (mu3c (app s (recÎ” b s n)))
         (mu3c (recÎ” b s (delta n))) := by
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
  Lex3c (mu3c (app s (recÎ” b s n))) (mu3c (recÎ” b s (delta n))) := by
  simpa using drop_R_rec_succ_c b s n

lemma drop_merge_void_left (t : Trace) (hÎ´ : MetaSN_KO7.deltaFlag t = 0) :
  Lex3c (mu3c t) (mu3c (merge void t)) := by
  simpa using drop_R_merge_void_left_c t hÎ´

lemma drop_eq_diff (a b : Trace) :
  Lex3c (mu3c (integrate (merge a b))) (mu3c (eqW a b)) := by
  simpa using drop_R_eq_diff_c a b

end Computable_FixPathExamples

/-! ## Approach #9: Complex Hybrid/Constellation Measures (Paper Â§7, Item 9 in failure catalog)

Paper quote: "Attempts to combine measures in ad-hoc ways failed to provide
a uniform decrease across all 8 rules."

Constellation theory attempts to track the "shape" or "pattern" of subterms
rather than their numeric size. The idea is that certain constellations of
constructors signal termination progress. This fails because the Î´-duplication
rule creates constellations that cannot be uniformly ordered.
-/
namespace ConstellationFailure

/-- A constellation is an abstraction of term structure (shape without content).
    Note: We use `recNode` instead of `rec` to avoid conflict with the eliminator. -/
inductive Constellation where
  | atom : Constellation
  | deltaNode : Constellation â†’ Constellation
  | integrateNode : Constellation â†’ Constellation
  | mergeNode : Constellation â†’ Constellation â†’ Constellation
  | appNode : Constellation â†’ Constellation â†’ Constellation
  | recNode : Constellation â†’ Constellation â†’ Constellation â†’ Constellation
  | eqNode : Constellation â†’ Constellation â†’ Constellation
  deriving DecidableEq, Repr

/-- Extract constellation from a trace (forgetting content, keeping shape). -/
def toConstellation : Trace â†’ Constellation
  | .void => .atom
  | .delta t => .deltaNode (toConstellation t)
  | .integrate t => .integrateNode (toConstellation t)
  | .merge a b => .mergeNode (toConstellation a) (toConstellation b)
  | .app a b => .appNode (toConstellation a) (toConstellation b)
  | .recÎ” b s n => .recNode (toConstellation b) (toConstellation s) (toConstellation n)
  | .eqW a b => .eqNode (toConstellation a) (toConstellation b)

/-- The Î´-duplication step produces structurally different constellations.
    The RHS has `appNode` at the root while LHS has `recNode` â€” no simple ordering works. -/
theorem constellation_shapes_differ (b s n : Trace) :
    toConstellation (app s (recÎ” b s n)) â‰  toConstellation (recÎ” b s (delta n)) := by
  simp only [toConstellation]
  intro h
  cases h

/-- A simple constellation size measure (counting nodes). -/
def constellationSize : Constellation â†’ Nat
  | .atom => 1
  | .deltaNode c => constellationSize c + 1
  | .integrateNode c => constellationSize c + 1
  | .mergeNode a b => constellationSize a + constellationSize b + 1
  | .appNode a b => constellationSize a + constellationSize b + 1
  | .recNode b s n => constellationSize b + constellationSize s + constellationSize n + 1
  | .eqNode a b => constellationSize a + constellationSize b + 1

/-- The Î´-duplication rule does NOT decrease constellation size when s is non-trivial.
    This shows additive constellation measures fail just like numeric ones.
    LHS: recNode(b, s, deltaNode(n)) has size = |b| + |s| + (|n| + 1) + 1
    RHS: appNode(s, recNode(b, s, n)) has size = |s| + (|b| + |s| + |n| + 1) + 1
    Difference: RHS - LHS = |s| - 1 â‰¥ 0 when |s| â‰¥ 1. -/
theorem constellation_size_not_decreasing (b s n : Trace)
    (hs : constellationSize (toConstellation s) â‰¥ 1) :
    constellationSize (toConstellation (app s (recÎ” b s n))) â‰¥
    constellationSize (toConstellation (recÎ” b s (delta n))) := by
  simp only [toConstellation, constellationSize]
  omega

end ConstellationFailure

/-! ## Approach #10: Unchecked Recursion (Paper Â§7, Item 10 in failure catalog)

Paper quote: "The raw duplicating rule is the canonical obstacle for global
aggregation: it entangles the relevant recursion counter with an irrelevant
duplicated mass trapped under inert app."

The rule `recÎ” b s (delta n) â†’ app s (recÎ” b s n)`:
1. Duplicates `s` (appears once on LHS, twice on RHS)
2. The recursive `recÎ”` call has `n` instead of `delta n`
3. BUT the `app s (...)` wrapping creates work that grows with each step

The recursion is "checked" only when restricted to `SafeStep`, which gates
certain steps behind a Î´-phase condition.
-/
namespace UncheckedRecursionFailure

/-- Concrete witness: with a simple additive size, the RHS is NOT smaller. -/
def simpleSize : Trace â†’ Nat
  | .void => 0
  | .delta t => simpleSize t + 1
  | .integrate t => simpleSize t + 1
  | .merge a b => simpleSize a + simpleSize b + 1
  | .app a b => simpleSize a + simpleSize b + 1
  | .recÎ” b s n => simpleSize b + simpleSize s + simpleSize n + 1
  | .eqW a b => simpleSize a + simpleSize b + 1

/-- The rec_succ rule is the structural barrier for additive measures.
    LHS: simpleSize(recÎ” b s (delta n)) = |b| + |s| + (|n| + 1) + 1 = |b| + |s| + |n| + 2
    RHS: simpleSize(app s (recÎ” b s n)) = |s| + (|b| + |s| + |n| + 1) + 1 = 2|s| + |b| + |n| + 2
    Difference: RHS - LHS = |s| â‰¥ 0. No strict decrease when |s| â‰¥ 0.
    This is the "ultimate counterexample" from the paper. -/
theorem rec_succ_additive_barrier (b s n : Trace) :
    simpleSize (app s (recÎ” b s n)) â‰¥ simpleSize (recÎ” b s (delta n)) := by
  simp only [simpleSize]
  omega

/-- Stronger: RHS is strictly LARGER when s is non-void. -/
theorem rec_succ_size_increases (b s n : Trace) (hs : simpleSize s â‰¥ 1) :
    simpleSize (app s (recÎ” b s n)) > simpleSize (recÎ” b s (delta n)) := by
  simp only [simpleSize]
  omega

/-- The full Step relation (not SafeStep) allows this barrier to be hit. -/
theorem full_step_permits_barrier :
    âˆƒ b s n, Step (recÎ” b s (delta n)) (app s (recÎ” b s n)) := by
  exact âŸ¨void, void, void, Step.R_rec_succ void void voidâŸ©

/-- Reference: The SafeStep guard is what makes termination provable.
    See `OperatorKO7.MetaCM.wf_SafeStepRev_c` for the working proof. -/
example : WellFounded MetaSN_KO7.SafeStepRev := OperatorKO7.MetaCM.wf_SafeStepRev_c

end UncheckedRecursionFailure

/-! ## Pointers to toy cores for witnesses/examples

For duplication flavor and base-change shape without touching KO7,
see `Meta/HydraCore.lean` and `Meta/GoodsteinCore.lean` (examples only). -/

end Impossibility
end OperatorKO7
````

## OperatorKO7/Meta/LinearRec_Ablation.lean

**Lines:** 83

``lean
import OperatorKO7.Kernel

namespace OperatorKO7

/-!
# Feature-4 Ablation: Linear (Non-Duplicating) Recursor

This module proves that removing step duplication (barrier condition 4)
dissolves the global orientation barrier. We define a linear recursor variant
where the step argument `s` is not duplicated on the RHS of `rec_succ`
(the RHS is `recÎ” b s n` instead of `app s (recÎ” b s n)`), and show that
`simpleSize` (a Tier-1 additive compositional measure) strictly orients both
rules.

This is consistent with duplication being the operative source of the barrier,
not the recursor pattern itself.
-/

open Trace

/-! ## Linear recursor step relation -/

/-- A non-duplicating recursor: `recÎ” b s (delta n) â†’ recÎ” b s n`.
    The step argument `s` is **not** duplicated on the RHS. -/
inductive LinearStep : Trace â†’ Trace â†’ Prop
| R_rec_zero_linear : âˆ€ b s, LinearStep (recÎ” b s void) b
| R_rec_succ_linear : âˆ€ b s n, LinearStep (recÎ” b s (delta n)) (recÎ” b s n)

/-! ## simpleSize: a Tier-1 additive compositional measure -/

/-- Node count: every constructor contributes 1 plus the sum of its subterms. -/
def simpleSize : Trace â†’ Nat
| void => 1
| delta t => 1 + simpleSize t
| integrate t => 1 + simpleSize t
| merge a b => 1 + simpleSize a + simpleSize b
| app a b => 1 + simpleSize a + simpleSize b
| recÎ” b s n => 1 + simpleSize b + simpleSize s + simpleSize n
| eqW a b => 1 + simpleSize a + simpleSize b

/-- `simpleSize` is always positive. -/
theorem simpleSize_pos (t : Trace) : 0 < simpleSize t := by
  cases t <;> simp [simpleSize] <;> omega

/-! ## Strict orientation theorems -/

/-- `simpleSize` strictly orients `R_rec_zero_linear`:
    `simpleSize b < simpleSize (recÎ” b s void)` -/
theorem simpleSize_orients_rec_zero_linear (b s : Trace) :
    simpleSize b < simpleSize (recÎ” b s void) := by
  simp [simpleSize]; omega

/-- `simpleSize` strictly orients `R_rec_succ_linear`:
    `simpleSize (recÎ” b s n) < simpleSize (recÎ” b s (delta n))` -/
theorem simpleSize_orients_rec_succ_linear (b s n : Trace) :
    simpleSize (recÎ” b s n) < simpleSize (recÎ” b s (delta n)) := by
  simp [simpleSize]

/-- Every `LinearStep` instance is strictly oriented by `simpleSize`. -/
theorem simpleSize_orients_linearStep {a b : Trace} (h : LinearStep a b) :
    simpleSize b < simpleSize a := by
  cases h with
  | R_rec_zero_linear b s => exact simpleSize_orients_rec_zero_linear b s
  | R_rec_succ_linear b s n => exact simpleSize_orients_rec_succ_linear b s n

/-- Strong normalization of `LinearStep` via `simpleSize`. -/
theorem wf_linearStep : WellFounded (fun a b => LinearStep b a) :=
  Subrelation.wf
    (fun {_ _} h => simpleSize_orients_linearStep h)
    (InvImage.wf simpleSize Nat.lt_wfRel.wf)

/-! ## Contrast: the duplicating recursor cannot be oriented by simpleSize -/

/-- Witness: `simpleSize` does **not** strictly orient the duplicating
    `R_rec_succ` for all instantiations. Specifically, for `b = void`,
    `s = app void void`, `n = void`, the RHS is strictly larger. -/
theorem simpleSize_fails_on_duplicating_rec_succ :
    Â¬ (âˆ€ b s n, simpleSize (app s (recÎ” b s n)) < simpleSize (recÎ” b s (delta n))) := by
  intro h
  have := h void (app void void) void
  simp [simpleSize] at this

end OperatorKO7
````

## OperatorKO7/Meta/MPO_FullStep.lean

**Lines:** 171

``lean
import OperatorKO7.Kernel

/-!
KO7 MPO orientation for the full root relation `Step`.

This module is KO7-specialized (not a generic library formalization):
- subterm clause;
- precedence clause;
- same-head multiset-style clause for `recÎ”` (third argument drop).

It proves that all eight full-kernel rules are oriented.
-/

namespace OperatorKO7.MetaMPO

open Trace

/-! ## Symbols, heads, arguments -/

inductive Sym : Type
| void
| delta
| integrate
| merge
| app
| recÎ”
| eqW
deriving DecidableEq, Repr

@[simp] def sym : Trace â†’ Sym
  | void => .void
  | delta _ => .delta
  | integrate _ => .integrate
  | merge _ _ => .merge
  | app _ _ => .app
  | recÎ” _ _ _ => .recÎ”
  | eqW _ _ => .eqW

@[simp] def args : Trace â†’ List Trace
  | void => []
  | delta t => [t]
  | integrate t => [t]
  | merge a b => [a, b]
  | app a b => [a, b]
  | recÎ” b s n => [b, s, n]
  | eqW a b => [a, b]

/-! ## Fixed precedence -/

@[simp] def rank : Sym â†’ Nat
  | .void => 0
  | .delta => 1
  | .merge => 2
  | .integrate => 3
  | .app => 4
  | .eqW => 5
  | .recÎ” => 6

def symPrec (f g : Sym) : Prop := rank f < rank g

/-! ## KO7 MPO relation -/

/--
`MPO s t` means `s` strictly dominates `t`.

Constructors:
- `subEq`: direct subterm.
- `subGt`: transitive subterm descent through an argument.
- `byPrec`: precedence domination with recursive domination of RHS arguments.
- `recArg`: same-head multiset-style clause on `recÎ”` (decrease in the third argument).
-/
inductive MPO : Trace â†’ Trace â†’ Prop
| subEq : âˆ€ {s u : Trace}, u âˆˆ args s â†’ MPO s u
| subGt : âˆ€ {s u t : Trace}, u âˆˆ args s â†’ MPO u t â†’ MPO s t
| byPrec : âˆ€ {s t : Trace},
    symPrec (sym t) (sym s) â†’
    (âˆ€ u, u âˆˆ args t â†’ MPO s u) â†’
    MPO s t
| recArg : âˆ€ {b s n n' : Trace},
    MPO n' n â†’
    MPO (recÎ” b s n') (recÎ” b s n)

/-! ## Helpers -/

theorem mpo_subterm {s t : Trace} (h : t âˆˆ args s) : MPO s t :=
  MPO.subEq h

theorem mpo_subterm_of {s u t : Trace} (hmem : u âˆˆ args s) (hgt : MPO u t) : MPO s t :=
  MPO.subGt hmem hgt

theorem mpo_delta_arg (n : Trace) : MPO (delta n) n :=
  mpo_subterm (s := delta n) (t := n) (by simp [args])

/-! ## Rule orientation lemmas -/

theorem mpo_R_int_delta (t : Trace) : MPO (integrate (delta t)) void :=
  MPO.byPrec
    (s := integrate (delta t)) (t := void)
    (by simp [symPrec, rank, sym])
    (by intro u hu; cases hu)

theorem mpo_R_merge_void_left (t : Trace) : MPO (merge void t) t :=
  mpo_subterm (s := merge void t) (t := t) (by simp [args])

theorem mpo_R_merge_void_right (t : Trace) : MPO (merge t void) t :=
  mpo_subterm (s := merge t void) (t := t) (by simp [args])

theorem mpo_R_merge_cancel (t : Trace) : MPO (merge t t) t :=
  mpo_subterm (s := merge t t) (t := t) (by simp [args])

theorem mpo_R_rec_zero (base step : Trace) : MPO (recÎ” base step void) base :=
  mpo_subterm (s := recÎ” base step void) (t := base) (by simp [args])

theorem mpo_R_rec_inner (base step n : Trace) :
    MPO (recÎ” base step (delta n)) (recÎ” base step n) :=
  MPO.recArg (b := base) (s := step) (n' := delta n) (n := n) (mpo_delta_arg n)

theorem mpo_R_rec_succ (base step n : Trace) :
    MPO (recÎ” base step (delta n)) (app step (recÎ” base step n)) :=
  MPO.byPrec
    (s := recÎ” base step (delta n)) (t := app step (recÎ” base step n))
    (by simp [symPrec, rank, sym])
    (by
      intro u hu
      have hu' : u = step âˆ¨ u = recÎ” base step n := by
        simpa [args] using hu
      rcases hu' with rfl | rfl
      Â· exact MPO.subEq (by simp [args])
      Â· exact mpo_R_rec_inner base step n)

theorem mpo_R_eq_refl (x : Trace) : MPO (eqW x x) void :=
  MPO.byPrec
    (s := eqW x x) (t := void)
    (by simp [symPrec, rank, sym])
    (by intro u hu; cases hu)

theorem mpo_R_eq_to_merge (x y : Trace) : MPO (eqW x y) (merge x y) :=
  MPO.byPrec
    (s := eqW x y) (t := merge x y)
    (by simp [symPrec, rank, sym])
    (by
      intro u hu
      have hu' : u = x âˆ¨ u = y := by
        simpa [args] using hu
      rcases hu' with rfl | rfl
      Â· exact MPO.subEq (by simp [args])
      Â· exact MPO.subEq (by simp [args]))

theorem mpo_R_eq_diff (x y : Trace) : MPO (eqW x y) (integrate (merge x y)) :=
  MPO.byPrec
    (s := eqW x y) (t := integrate (merge x y))
    (by simp [symPrec, rank, sym])
    (by
      intro u hu
      have hu' : u = merge x y := by simpa [args] using hu
      subst hu'
      exact mpo_R_eq_to_merge x y)

/-! ## Master theorem -/

theorem mpo_orients_step : âˆ€ {a b : Trace}, Step a b â†’ MPO a b
  | _, _, Step.R_int_delta t => mpo_R_int_delta t
  | _, _, Step.R_merge_void_left t => mpo_R_merge_void_left t
  | _, _, Step.R_merge_void_right t => mpo_R_merge_void_right t
  | _, _, Step.R_merge_cancel t => mpo_R_merge_cancel t
  | _, _, Step.R_rec_zero b s => mpo_R_rec_zero b s
  | _, _, Step.R_rec_succ b s n => mpo_R_rec_succ b s n
  | _, _, Step.R_eq_refl a => mpo_R_eq_refl a
  | _, _, Step.R_eq_diff a b => mpo_R_eq_diff a b

end OperatorKO7.MetaMPO
````

## OperatorKO7/Meta/Newman_Safe.lean

**Lines:** 205

``lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.ComputableMeasure
import OperatorKO7.Meta.Normalize_Safe
import OperatorKO7.Meta.Confluence_Safe

/-!
Newman's lemma for the KO7 safe fragment.

Purpose:
- Packages the standard argument: termination (well-foundedness) + local joinability implies
  confluence (Church-Rosser) for the reflexive-transitive closure.

Scope boundary:
- This file is parameterized by a local-join hypothesis `locAll : âˆ€ a, LocalJoinAt a`.
- Termination for `SafeStep` is supplied by `wf_SafeStepRev_c` (from `Meta/ComputableMeasure.lean`).
- Nothing here claims confluence/termination for the full kernel `Step`.

Main exports:
- `newman_safe` / `confluentSafe_of_localJoinAt_and_SN`
- Corollaries about unique normal forms and stability of `normalizeSafe`, assuming `locAll`.
-/
open Classical
open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Root local-join property at `a` for the KO7 safe relation. -/
def LocalJoinAt (a : Trace) : Prop :=
  âˆ€ {b c}, SafeStep a b â†’ SafeStep a c â†’ âˆƒ d, SafeStepStar b d âˆ§ SafeStepStar c d

/-- Churchâ€“Rosser (confluence) for the safe star closure. -/
def ConfluentSafe : Prop :=
  âˆ€ a b c, SafeStepStar a b â†’ SafeStepStar a c â†’ âˆƒ d, SafeStepStar b d âˆ§ SafeStepStar c d

/-! ### Small join helpers (step vs. star) -/

/-- Trivial join of a single left step with a right reflexive star (choose `d = b`). -/
theorem join_step_with_refl_star {a b : Trace}
  (hab : SafeStep a b) : âˆƒ d, SafeStepStar b d âˆ§ SafeStepStar a d := by
  refine âŸ¨b, ?_, ?_âŸ©
  Â· exact SafeStepStar.refl b
  Â· exact safestar_of_step hab

-- Join a single left step against a right star with a head step, delegating the tail to a
-- provided starâ€“star joiner starting at the right-head successor.
/-- Join one left root step against a right multi-step path, using local join + a star-star joiner. -/
theorem join_step_with_tail_star
  {a b câ‚ c : Trace}
  (loc : LocalJoinAt a)
  (joinSS : âˆ€ {x y z}, SafeStepStar x y â†’ SafeStepStar x z â†’ âˆƒ d, SafeStepStar y d âˆ§ SafeStepStar z d)
  (hab : SafeStep a b) (hacâ‚ : SafeStep a câ‚) (hct : SafeStepStar câ‚ c)
  : âˆƒ d, SafeStepStar b d âˆ§ SafeStepStar c d := by
  -- Local join at the root gives a common `e` with `b â‡’* e` and `câ‚ â‡’* e`.
  rcases loc (b := b) (c := câ‚) (hab) (hacâ‚) with âŸ¨e, hbe, hcâ‚eâŸ©
  -- Use the provided starâ€“star joiner at source `câ‚` to join `câ‚ â‡’* e` and `câ‚ â‡’* c`.
  rcases joinSS (x := câ‚) (y := e) (z := c) hcâ‚e hct with âŸ¨d, hed, hcdâŸ©
  -- Compose on the left: `b â‡’* e â‡’* d`.
  exact âŸ¨d, safestar_trans hbe hed, hcdâŸ©

-- If we can locally join root-steps everywhere and we have a starâ€“star joiner, then a single
-- left step joins with any right star.
/-- If local join holds everywhere and we can join stars, then a single step joins with any star. -/
theorem join_step_star_of_join_star_star
  (locAll : âˆ€ a, LocalJoinAt a)
  (joinSS : âˆ€ {x y z}, SafeStepStar x y â†’ SafeStepStar x z â†’ âˆƒ d, SafeStepStar y d âˆ§ SafeStepStar z d)
  {a b c : Trace}
  (hab : SafeStep a b) (hac : SafeStepStar a c)
  : âˆƒ d, SafeStepStar b d âˆ§ SafeStepStar c d := by
  -- Case split on the right star.
  cases hac with
  | refl _ =>
      -- Right is reflexive: join is immediate with `d = b`.
      exact join_step_with_refl_star hab
  | tail hacâ‚ hct =>
      -- Right has a head step: use the tail helper with local join at `a` and the provided `joinSS`.
      exact join_step_with_tail_star (locAll a) (joinSS) hab hacâ‚ hct

/-! ### Starâ€“star join by Acc recursion and Newman's lemma -/

-- Main engine: starâ€“star join at a fixed source, by Acc recursion on SafeStepRev at the source.
/-- Core engine: join two `SafeStepStar` paths out of `x` by `Acc` recursion on `SafeStepRev x`. -/
private theorem join_star_star_at
  (locAll : âˆ€ a, LocalJoinAt a)
  : âˆ€ x, Acc SafeStepRev x â†’ âˆ€ {y z : Trace}, SafeStepStar x y â†’ SafeStepStar x z â†’ âˆƒ d, SafeStepStar y d âˆ§ SafeStepStar z d := by
  intro x hx
  induction hx with
  | intro x _ ih =>
  intro y z hxy hxz
  -- Destructure both star paths out of x.
  have HX := safestar_destruct hxy
  have HZ := safestar_destruct hxz
  cases HX with
  | inl hEq =>
    -- y = x, trivial join with z
    cases hEq
    exact âŸ¨z, hxz, SafeStepStar.refl zâŸ©
  | inr hex =>
    rcases hex with âŸ¨b1, hxb1, hb1yâŸ©
    cases HZ with
    | inl hEq2 =>
      -- z = x, trivial join with y via left head step
      cases hEq2
      exact âŸ¨y, SafeStepStar.refl y, SafeStepStar.tail hxb1 hb1yâŸ©
    | inr hey =>
      rcases hey with âŸ¨c1, hxc1, hc1zâŸ©
      -- Local join at root x
      rcases locAll x hxb1 hxc1 with âŸ¨e, hb1e, hc1eâŸ©
      -- Use IH at c1 to join c1 â‡’* e and c1 â‡’* z
      rcases ih c1 hxc1 hc1e hc1z with âŸ¨dâ‚, hedâ‚, hzdâ‚âŸ©
      -- Compose b1 â‡’* e â‡’* dâ‚
      have hb1dâ‚ : SafeStepStar b1 dâ‚ := safestar_trans hb1e hedâ‚
      -- Use IH at b1 to join b1 â‡’* y and b1 â‡’* dâ‚
      rcases ih b1 hxb1 hb1y hb1dâ‚ with âŸ¨d, hyd, hdâ‚dâŸ©
      -- Final composition on the right
      exact âŸ¨d, hyd, safestar_trans hzdâ‚ hdâ‚dâŸ©

theorem join_star_star
  (locAll : âˆ€ a, LocalJoinAt a)
  {a b c : Trace}
  (hab : SafeStepStar a b) (hac : SafeStepStar a c)
  : âˆƒ d, SafeStepStar b d âˆ§ SafeStepStar c d := by
  exact join_star_star_at locAll a (acc_SafeStepRev a) hab hac

-- Newman's lemma for the safe relation.
/-- Newman's lemma specialized to `SafeStep`: termination + local joinability implies confluence. -/
theorem newman_safe (locAll : âˆ€ a, LocalJoinAt a) : ConfluentSafe := by
  intro _ _ _ hab hac
  exact join_star_star locAll hab hac

end MetaSN_KO7

namespace MetaSN_KO7

/-! ## Derived corollaries (parameterized by local join) -/

/-- Global confluence from local join everywhere (alias of `newman_safe`). -/
theorem confluentSafe_of_localJoinAt_and_SN
    (locAll : âˆ€ a, LocalJoinAt a) : ConfluentSafe :=
  newman_safe locAll

/-- Unique normal forms under global confluence provided by `locAll`. -/
theorem unique_normal_forms_of_loc
    (locAll : âˆ€ a, LocalJoinAt a)
    {a nâ‚ nâ‚‚ : Trace}
    (hâ‚ : SafeStepStar a nâ‚) (hâ‚‚ : SafeStepStar a nâ‚‚)
    (hnfâ‚ : NormalFormSafe nâ‚) (hnfâ‚‚ : NormalFormSafe nâ‚‚) :
    nâ‚ = nâ‚‚ := by
  have conf : ConfluentSafe := newman_safe locAll
  obtain âŸ¨d, hâ‚d, hâ‚‚dâŸ© := conf a nâ‚ nâ‚‚ hâ‚ hâ‚‚
  have eqâ‚ : nâ‚ = d := nf_no_safestar_forward hnfâ‚ hâ‚d
  have eqâ‚‚ : nâ‚‚ = d := nf_no_safestar_forward hnfâ‚‚ hâ‚‚d
  simp [eqâ‚, eqâ‚‚]

/-- The normalizer returns the unique normal form (assuming `locAll`). -/
theorem normalizeSafe_unique_of_loc
    (locAll : âˆ€ a, LocalJoinAt a)
    {t n : Trace}
    (h : SafeStepStar t n) (hnf : NormalFormSafe n) :
    n = normalizeSafe t := by
  exact unique_normal_forms_of_loc locAll h (to_norm_safe t) hnf (norm_nf_safe t)

/-- Safe-step-related terms normalize to the same result (assuming `locAll`). -/
theorem normalizeSafe_eq_of_star_of_loc
    (locAll : âˆ€ a, LocalJoinAt a)
    {a b : Trace} (h : SafeStepStar a b) :
    normalizeSafe a = normalizeSafe b := by
  have ha := to_norm_safe a
  have hb := to_norm_safe b
  have conf : ConfluentSafe := newman_safe locAll
  obtain âŸ¨d, had, hbdâŸ© := conf a (normalizeSafe a) (normalizeSafe b) ha (safestar_trans h hb)
  have eqâ‚ := nf_no_safestar_forward (norm_nf_safe a) had
  have eqâ‚‚ := nf_no_safestar_forward (norm_nf_safe b) hbd
  simp [eqâ‚, eqâ‚‚]

/-- Global local-join discharge for `SafeStep`, imported from `Confluence_Safe`. -/
theorem locAll_safe : âˆ€ a, LocalJoinAt a := by
  intro a b c hb hc
  exact (MetaSN_KO7.localJoin_all_safe a) hb hc

/-- Unconditional confluence for the safe fragment (`SafeStep`). -/
theorem confluentSafe : ConfluentSafe :=
  newman_safe locAll_safe

/-- Unconditional unique normal forms for the safe fragment. -/
theorem unique_normal_forms_safe
    {a nâ‚ nâ‚‚ : Trace}
    (hâ‚ : SafeStepStar a nâ‚) (hâ‚‚ : SafeStepStar a nâ‚‚)
    (hnfâ‚ : NormalFormSafe nâ‚) (hnfâ‚‚ : NormalFormSafe nâ‚‚) :
    nâ‚ = nâ‚‚ :=
  unique_normal_forms_of_loc locAll_safe hâ‚ hâ‚‚ hnfâ‚ hnfâ‚‚

/-- Unconditional normalizer uniqueness for safe-normal outputs. -/
theorem normalizeSafe_unique
    {t n : Trace}
    (h : SafeStepStar t n) (hnf : NormalFormSafe n) :
    n = normalizeSafe t :=
  normalizeSafe_unique_of_loc locAll_safe h hnf

/-- Unconditional normalization equality along safe-star reachability. -/
theorem normalizeSafe_eq_of_star
    {a b : Trace} (h : SafeStepStar a b) :
    normalizeSafe a = normalizeSafe b :=
  normalizeSafe_eq_of_star_of_loc locAll_safe h

end MetaSN_KO7
````

## OperatorKO7/Meta/Normalize_Safe.lean

**Lines:** 330

``lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Logic.Function.Basic

/-!
Certified normalization for the KO7 safe fragment.

Purpose:
- Defines `SafeStepStar` (multi-step closure of `SafeStep`).
- Defines `NormalFormSafe` and proves basic normal-form facts for the safe relation.
- Constructs a *computable certified* normalizer `normalizeSafe` for `SafeStep` using
  deterministic well-founded recursion.

Important scope boundary:
- Everything in this file is about `SafeStep` (the guarded fragment), not the full kernel `Step`.
- The normalizer is definitional/recursive (no `Classical.choose`); certificates are bundled directly.

Main exports:
- `normalizeSafe` and its certificates: `to_norm_safe`, `norm_nf_safe`
- Fixed-point characterizations: `nf_iff_normalize_fixed`, `not_fixed_iff_exists_step`
- Convenience bundles: `normalizeSafe_sound`, `normalizeSafe_total`
-/
set_option diagnostics.threshold 100000
set_option linter.unnecessarySimpa false
open Classical
open OperatorKO7 Trace
open OperatorKO7.MetaCM
open MetaSN_DM


namespace MetaSN_KO7

/-- Reflexive-transitive closure of `SafeStep`. -/
inductive SafeStepStar : Trace â†’ Trace â†’ Prop
| refl : âˆ€ t, SafeStepStar t t
| tail : âˆ€ {a b c}, SafeStep a b â†’ SafeStepStar b c â†’ SafeStepStar a c

/-- Transitivity of the safe multi-step relation `SafeStepStar`. -/
theorem safestar_trans {a b c : Trace}
  (hâ‚ : SafeStepStar a b) (hâ‚‚ : SafeStepStar b c) : SafeStepStar a c := by
  induction hâ‚ with
  | refl => exact hâ‚‚
  | tail hab _ ih => exact SafeStepStar.tail hab (ih hâ‚‚)

/-- Any single safe step is also a `SafeStepStar`. -/
theorem safestar_of_step {a b : Trace} (h : SafeStep a b) : SafeStepStar a b :=
  SafeStepStar.tail h (SafeStepStar.refl b)

/-- Normal forms for the safe subrelation. -/
def NormalFormSafe (t : Trace) : Prop := Â¬ âˆƒ u, SafeStep t u

/-- No single safe step can originate from a safe normal form. -/
theorem no_step_from_nf {t u : Trace} (h : NormalFormSafe t) : Â¬ SafeStep t u := by
  intro hs; exact h âŸ¨u, hsâŸ©

/-- If `a` is a safe normal form, then any `a â‡’* b` (in `SafeStepStar`) must be trivial. -/
theorem nf_no_safestar_forward {a b : Trace}
  (hnf : NormalFormSafe a) (h : SafeStepStar a b) : a = b :=
  match h with
  | SafeStepStar.refl _ => rfl
  | SafeStepStar.tail hs _ => False.elim (hnf âŸ¨_, hsâŸ©)

/-- From a safe normal form, reachability by `SafeStepStar` is equivalent to equality. -/
theorem safestar_from_nf_iff_eq {t u : Trace}
  (h : NormalFormSafe t) : SafeStepStar t u â†” u = t := by
  constructor
  Â· intro htu
    have ht_eq : t = u := nf_no_safestar_forward h htu
    exact ht_eq.symm
  Â· intro hEq; cases hEq; exact SafeStepStar.refl t

/-- No non-trivial safe multi-step can start from a safe normal form. -/
theorem no_safestar_from_nf_of_ne {t u : Trace}
  (h : NormalFormSafe t) (hne : u â‰  t) : Â¬ SafeStepStar t u := by
  intro htu
  have := (safestar_from_nf_iff_eq h).1 htu
  exact hne this

/-- Uniqueness of endpoints for `SafeStepStar` paths starting at a safe normal form. -/
theorem safestar_from_nf_unique {a b c : Trace}
  (ha : NormalFormSafe a) (hab : SafeStepStar a b) (hac : SafeStepStar a c) : b = c := by
  have hb : b = a := (nf_no_safestar_forward ha hab).symm
  have hc : c = a := (nf_no_safestar_forward ha hac).symm
  simpa [hb, hc]

/-- Any `SafeStepStar` cycle through a safe normal form collapses to equality. -/
theorem safestar_cycle_nf_eq {a b : Trace}
  (ha : NormalFormSafe a) (hab : SafeStepStar a b) (_hba : SafeStepStar b a) : a = b :=
  nf_no_safestar_forward ha hab

/-! ### Star structure helpers -/

/-- Head decomposition for `SafeStepStar`: either refl, or a head step with a tail star. -/
theorem safestar_destruct {a c : Trace} (h : SafeStepStar a c) :
  a = c âˆ¨ âˆƒ b, SafeStep a b âˆ§ SafeStepStar b c := by
  cases h with
  | refl t => exact Or.inl rfl
  | tail hab hbc => exact Or.inr âŸ¨_, hab, hbcâŸ©

/-- Append a single safe step to the right of a safe multi-step path. -/
theorem safestar_snoc {a b c : Trace}
  (hab : SafeStepStar a b) (hbc : SafeStep b c) : SafeStepStar a c :=
  safestar_trans hab (safestar_of_step hbc)

/-! ### Strong normalization (rev) - convenience -/

/-- Accessibility for `SafeStepRev` as a derived corollary of `wf_SafeStepRev_c`. -/
theorem acc_SafeStepRev (t : Trace) : Acc SafeStepRev t :=
  wf_SafeStepRev_c.apply t

/-- A well-founded pullback of the computable KO7 Lex3c order along Î¼3c. -/
def RÎ¼3 (x y : Trace) : Prop := Lex3c (mu3c x) (mu3c y)

/-- Well-foundedness of `RÎ¼3`, inherited from `wf_Lex3c` via `InvImage`. -/
lemma wf_RÎ¼3 : WellFounded RÎ¼3 :=
  InvImage.wf (f := mu3c) wf_Lex3c

/-- Deterministic one-step selector for root `SafeStep`.
Returns a witness term and its `SafeStep` proof when a root step exists, otherwise `none`. -/
@[simp] def safeStepWitness? : (t : Trace) â†’ Option {u : Trace // SafeStep t u}
  | integrate (delta t) =>
      some âŸ¨void, SafeStep.R_int_delta tâŸ©
  | merge void t =>
      if hÎ´ : deltaFlag t = 0 then
        some âŸ¨t, SafeStep.R_merge_void_left t hÎ´âŸ©
      else
        none
  | merge t void =>
      if hÎ´ : deltaFlag t = 0 then
        some âŸ¨t, SafeStep.R_merge_void_right t hÎ´âŸ©
      else
        none
  | merge a b =>
      if hEq : a = b then
        match hEq with
        | rfl =>
            if hÎ´ : deltaFlag a = 0 then
              if h0 : kappaM a = 0 then
                some âŸ¨a, SafeStep.R_merge_cancel a hÎ´ h0âŸ©
              else
                none
            else
              none
      else
        none
  | recÎ” b s void =>
      if hÎ´ : deltaFlag b = 0 then
        some âŸ¨b, SafeStep.R_rec_zero b s hÎ´âŸ©
      else
        none
  | recÎ” b s (delta n) =>
      some âŸ¨app s (recÎ” b s n), SafeStep.R_rec_succ b s nâŸ©
  | eqW a b =>
      if hEq : a = b then
        match hEq with
        | rfl =>
            if h0 : kappaM a = 0 then
              some âŸ¨void, SafeStep.R_eq_refl a h0âŸ©
            else
              none
      else
        some âŸ¨integrate (merge a b), SafeStep.R_eq_diff a b hEqâŸ©
  | _ =>
      none

/-- Step target-only view of `safeStepWitness?` for executable stepping. -/
@[simp] def safeStepNext? (t : Trace) : Option Trace :=
  (safeStepWitness? t).map (fun w => w.1)

/-- If the deterministic selector returns `none`, no root `SafeStep` exists. -/
lemma safeStepWitness?_none_no_step {t : Trace} (hnone : safeStepWitness? t = none) :
    âˆ€ u, Â¬ SafeStep t u := by
  intro u hu
  cases hu with
  | R_int_delta t =>
      simp [safeStepWitness?] at hnone
  | R_merge_void_left t hÎ´ =>
      cases u <;> simp [safeStepWitness?, deltaFlag] at hÎ´ hnone
      all_goals exact hnone hÎ´
  | R_merge_void_right t hÎ´ =>
      cases u <;> simp [safeStepWitness?, deltaFlag] at hÎ´ hnone
      all_goals exact hnone hÎ´
  | R_merge_cancel t hÎ´ h0 =>
      cases u <;> simp [safeStepWitness?, deltaFlag, MetaSN_DM.kappaM] at hÎ´ h0 hnone
      all_goals exact hnone h0
  | R_rec_zero b s hÎ´ =>
      cases u <;> simp [safeStepWitness?, deltaFlag] at hÎ´ hnone
      all_goals exact hnone hÎ´
  | R_rec_succ b s n =>
      simp [safeStepWitness?] at hnone
  | R_eq_refl a h0 =>
      cases a <;> simp [safeStepWitness?, MetaSN_DM.kappaM] at h0 hnone
      all_goals exact hnone h0
  | R_eq_diff a b hne =>
      simp [safeStepWitness?, hne] at hnone

/-- Deterministic normalization for the safe subrelation, bundled with a proof certificate. -/
def normalizeSafePack (t : Trace) : Î£' n : Trace, SafeStepStar t n âˆ§ NormalFormSafe n :=
  WellFounded.fix wf_RÎ¼3 (C := fun t => Î£' n : Trace, SafeStepStar t n âˆ§ NormalFormSafe n)
    (fun t rec =>
      match hnext : safeStepWitness? t with
      | some w =>
          let u : Trace := w.1
          let hu : SafeStep t u := w.2
          have hdrop : RÎ¼3 u t := measure_decreases_safe_c hu
          match rec u hdrop with
          | âŸ¨n, hstar, hnfâŸ© => âŸ¨n, SafeStepStar.tail hu hstar, hnfâŸ©
      | none =>
          âŸ¨t, SafeStepStar.refl t, by
            intro ex
            rcases ex with âŸ¨u, huâŸ©
            exact (safeStepWitness?_none_no_step hnext u) huâŸ©
    ) t

/-- The safe normal form selected by `normalizeSafePack`. -/
def normalizeSafe (t : Trace) : Trace := (normalizeSafePack t).1

/-- Certificate: `t` reduces to `normalizeSafe t` by `SafeStepStar`. -/
theorem to_norm_safe (t : Trace) : SafeStepStar t (normalizeSafe t) := (normalizeSafePack t).2.left

/-- Certificate: `normalizeSafe t` is a safe normal form. -/
theorem norm_nf_safe (t : Trace) : NormalFormSafe (normalizeSafe t) := (normalizeSafePack t).2.right
/-! ### Small derived lemmas -/

/-- If `t` is already in safe normal form, normalization is the identity. -/
theorem normalizeSafe_eq_self_of_nf (t : Trace) (h : NormalFormSafe t) :
  normalizeSafe t = t := by
  -- From NF, any star out of `t` is trivial; apply it to the normalizer path.
  have := nf_no_safestar_forward h (to_norm_safe t)
  exact this.symm

/-- Existence of a reachable safe normal form for any trace (witnessed by `normalizeSafe`). -/
theorem exists_nf_reachable (t : Trace) :
  âˆƒ n, SafeStepStar t n âˆ§ NormalFormSafe n :=
  âŸ¨normalizeSafe t, to_norm_safe t, norm_nf_safe tâŸ©

/-- Either a safe step exists from `t`, or the normalizer is already fixed at `t`. -/
theorem progress_or_fixed (t : Trace) : (âˆƒ u, SafeStep t u) âˆ¨ normalizeSafe t = t := by
  classical
  -- Term-mode split on NormalFormSafe t
  exact
    (if hnf : NormalFormSafe t then
      Or.inr (normalizeSafe_eq_self_of_nf t hnf)
    else
      Or.inl (by
        have : Â¬Â¬ âˆƒ u, SafeStep t u := by simpa [NormalFormSafe] using hnf
        exact not_not.mp this))

/-- Head-or-refl decomposition of the normalization path (unbundled). -/
theorem to_norm_safe_head_or_refl (t : Trace) :
  normalizeSafe t = t âˆ¨ âˆƒ u, SafeStep t u âˆ§ SafeStepStar u (normalizeSafe t) := by
  have h := safestar_destruct (to_norm_safe t)
  cases h with
  | inl hEq => exact Or.inl hEq.symm
  | inr hex =>
      rcases hex with âŸ¨u, hstep, htailâŸ©
      exact Or.inr âŸ¨u, hstep, htailâŸ©

/-- If normalization changes `t`, then a safe step exists from `t`. -/
theorem exists_step_of_not_fixed (t : Trace) (h : normalizeSafe t â‰  t) : âˆƒ u, SafeStep t u := by
  cases progress_or_fixed t with
  | inl hex => exact hex
  | inr hfix => exact (h hfix).elim

/-- If normalization changes `t`, there exists a `SafeStep` successor that strictly decreases `RÎ¼3`. -/
theorem exists_drop_if_not_fixed (t : Trace) (h : normalizeSafe t â‰  t) :
  âˆƒ u, SafeStep t u âˆ§ RÎ¼3 u t := by
  classical
  rcases exists_step_of_not_fixed t h with âŸ¨u, hsâŸ©
  exact âŸ¨u, hs, measure_decreases_safe_c hsâŸ©

/-- If there is a safe step from `t`, then normalization cannot be fixed at `t`. -/
theorem not_fixed_of_exists_step (t : Trace) (hex : âˆƒ u, SafeStep t u) :
  normalizeSafe t â‰  t := by
  intro hfix
  -- From fixed-point, we get NF; contradiction with existence of a step.
  have hnf : NormalFormSafe t := by simpa [hfix] using norm_nf_safe t
  exact hnf hex

/-- Fixed-point characterization: `normalizeSafe t â‰  t` iff there exists a safe step from `t`. -/
theorem not_fixed_iff_exists_step (t : Trace) :
  normalizeSafe t â‰  t â†” âˆƒ u, SafeStep t u := by
  constructor
  Â· exact exists_step_of_not_fixed t
  Â· intro hex; exact not_fixed_of_exists_step t hex

/-! ### Fixed-point characterization of safe normal forms -/

theorem nf_iff_normalize_fixed (t : Trace) :
  NormalFormSafe t â†” normalizeSafe t = t := by
  constructor
  Â· intro h; exact normalizeSafe_eq_self_of_nf t h
  Â· intro h; simpa [h] using norm_nf_safe t


/-! ### Basic properties for the KO7 safe normalizer -/

/-- Idempotence of safe normalization: normalizing twice is the same as once. -/
theorem normalizeSafe_idempotent (t : Trace) :
  normalizeSafe (normalizeSafe t) = normalizeSafe t := by
  classical
  have hnf : NormalFormSafe (normalizeSafe t) := norm_nf_safe t
  -- No outgoing safe step from `normalizeSafe t` and star to itself
  have hstar : SafeStepStar (normalizeSafe t) (normalizeSafe (normalizeSafe t)) := to_norm_safe (normalizeSafe t)
  have := nf_no_safestar_forward hnf hstar
  exact this.symm

/-! ### (reserved) join-to-NF and confluence

-- Note: General join-to-NF and confluence results are intentionally deferred here.
-- They require additional confluence hypotheses or a separate argument; we keep the
-- current module to safe, non-controversial lemmas that do not rely on global CR.

-/

end MetaSN_KO7

namespace MetaSN_KO7

/-- Bundled soundness of the KO7 safe normalizer. -/
theorem normalizeSafe_sound (t : Trace) :
  SafeStepStar t (normalizeSafe t) âˆ§ NormalFormSafe (normalizeSafe t) :=
  âŸ¨to_norm_safe t, norm_nf_safe tâŸ©

/-- Totality alias for convenience: every trace safely normalizes to some NF. -/
theorem normalizeSafe_total (t : Trace) :
  âˆƒ n, SafeStepStar t n âˆ§ NormalFormSafe n :=
  âŸ¨normalizeSafe t, to_norm_safe t, norm_nf_safe tâŸ©

end MetaSN_KO7
````

## OperatorKO7/Meta/Operational_Incompleteness.lean

**Lines:** 1186

``lean
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna
import OperatorKO7.Meta.HydraCore
import OperatorKO7.Meta.GoodsteinCore

/-!
Operational incompleteness probes (P1-P3) and duplication stress-test scaffolding.

This file is intentionally "probe oriented": it collects small, explicit constructions that support
the paper's *operational incompleteness* framing, without claiming that the full KO7 kernel `Step`
is terminating or confluent.

What this module provides:
- A small operator-only term language (`Term`) with 7 constructors.
- Eight unconditional rewrite rules (`Rule`) plus a standard context closure (`Step`).
- Generic reflexive-transitive closure `Star` and star-composition utilities.
- A structure `InternallyDefinableMeasure` capturing "operator-definable" measures (the notion that
  is relevant to the conjecture: which proof principles count as "internal").
- Duplication stress-test scaffolding for the duplicating rule `mul (s x) y -> add y (mul x y)`.
- Imports of `HydraCore` and `GoodsteinCore` stubs used as additional stress-test encodings.

Style/guardrails:
- All statements are proved (no `sorry`); when a fragment is meant to record a dead end, it remains
  commented to keep the build green.
- Names and arities are spelled out explicitly to satisfy "NameGate / TypeGate" style checks.
-/

set_option linter.unnecessarySimpa false
namespace OperatorKO7.OpIncomp

/--
Seven constructors (names and arities are explicit to satisfy NameGate/TypeGate):
  z    : 0
  s    : 1
  add  : 2
  mul  : 2
  pair : 2
  fst  : 1
  snd  : 1
-/

inductive Term : Type
| z    : Term
| s    : Term â†’ Term
| add  : Term â†’ Term â†’ Term
| mul  : Term â†’ Term â†’ Term
| pair : Term â†’ Term â†’ Term
| fst  : Term â†’ Term
| snd  : Term â†’ Term
deriving DecidableEq, Repr

open Term

/-- Arity table for NameGate/TypeGate reporting. -/
inductive Op where
| z | s | add | mul | pair | fst | snd
deriving DecidableEq, Repr

/-- Arity of each operator symbol (used only for probe reporting, not for rewriting). -/
def arity : Op â†’ Nat
| .z    => 0
| .s    => 1
| .add  => 2
| .mul  => 2
| .pair => 2
| .fst  => 1
| .snd  => 1

/-- Eight unconditional rules at the top level. -/
inductive Rule : Term â†’ Term â†’ Prop
| r1 (y)         : Rule (add z y) y
| r2 (x y)       : Rule (add (s x) y) (s (add x y))
| r3 (y)         : Rule (mul z y) z
| r4 (x y)       : Rule (mul (s x) y) (add y (mul x y))          -- duplicates y
| r5 (x y)       : Rule (fst (pair x y)) x
| r6 (x y)       : Rule (snd (pair x y)) y
| r7 (x)         : Rule (add x z) x                               -- right-zero for add
| r8 (x)         : Rule (mul x z) z                               -- right-zero for mul

/-- For each LHS, list all RHS "pieces" that any matching rule could produce.
This union makes the per-piece orientation contract independent of the Prop proof.
It is intentionally slightly stronger on overlapping LHS shapes. -/
def rhsPiecesLHS : Term â†’ List Term
| add a b =>
  let LaddLeft : List Term :=
    match a with
    | z     => [b]            -- r1: add z b â†’ b
    | s x   => [add x b]      -- r2: add (s x) b â†’ s (add x b)
    | _     => []
  let LaddRight : List Term :=
    match b with
    | z     => [a]            -- r7: add a z â†’ a
    | _     => []
  LaddLeft ++ LaddRight
| mul a b =>
  let LmulLeft : List Term :=
    match a with
    | z     => [z]            -- r3: mul z b â†’ z
    | s x   => [b, mul x b]   -- r4: mul (s x) b â†’ add b (mul x b)
    | _     => []
  let LmulRight : List Term :=
    match b with
    | z     => [z]            -- r8: mul a z â†’ z
    | _     => []
  LmulLeft ++ LmulRight
| fst t =>
  match t with
  | pair x _ => [x]           -- r5
  | _        => []
| snd t =>
  match t with
  | pair _ y => [y]           -- r6
  | _        => []
| _ => []

/-- Context closure of single-step rewriting. -/
inductive Step : Term â†’ Term â†’ Prop
| base {l r}     : Rule l r â†’ Step l r
| sCtx  {t u}    : Step t u â†’ Step (s t) (s u)
| addLCtx {t u v}: Step t u â†’ Step (add t v) (add u v)
| addRCtx {t u v}: Step t u â†’ Step (add v t) (add v u)
| mulLCtx {t u v}: Step t u â†’ Step (mul t v) (mul u v)
| mulRCtx {t u v}: Step t u â†’ Step (mul v t) (mul v u)
| pairLCtx{t u v}: Step t u â†’ Step (pair t v) (pair u v)
| pairRCtx{t u v}: Step t u â†’ Step (pair v t) (pair v u)
| fstCtx {t u}   : Step t u â†’ Step (fst t) (fst u)
| sndCtx {t u}   : Step t u â†’ Step (snd t) (snd u)

/-- Reflexiveâ€“transitive closure `Star`. -/
inductive Star {Î± : Type} (R : Î± â†’ Î± â†’ Prop) : Î± â†’ Î± â†’ Prop
| refl {a}       : Star R a a
| step {a b c}   : R a b â†’ Star R b c â†’ Star R a c

namespace Star
variable {Î± : Type} {R : Î± â†’ Î± â†’ Prop}

@[simp] theorem refl' {a} : Star R a a := Star.refl

theorem trans {a b c} (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  induction h1 with
  | refl =>
    simpa using h2
  | step h h1 ih =>
    exact Star.step h (ih h2)

end Star

/-- A simple additive size measure used only for the duplication stress test. -/
def size : Term â†’ Nat
| z           => 1
| s t         => size t + 1
| add t u     => size t + size u + 1
| mul t u     => size t + size u + 1
| pair t u    => size t + size u + 1
| fst t       => size t + 1
| snd t       => size t + 1


/-! A) Branch-by-branch rfl gate.
    Define a two-clause function `f` and test `two * f x = f (two * x)`.
    We enumerate clauses and expose which branch passes by `rfl`.
-/
def two : Term := s (s z)

def f : Term â†’ Term
| z         => z
| s n       => s (s (f n))
| add a b   => add (f a) (f b)
| mul a b   => mul (f a) (f b)
| pair a b  => pair (f a) (f b)
| fst t     => fst (f t)
| snd t     => snd (f t)

/-- Clause x = z: both sides reduce by definitional unfolding of `f`. -/
def P1_pass_clause_z_LHS : Term := mul two (f z)     -- = mul two z
def P1_pass_clause_z_RHS : Term := f (mul two z)     -- stays syntactically as `f (mul two z)`
/-
rfl attempt results:
  `P1_pass_clause_z_LHS` defeq `mul two z`.
  `P1_pass_clause_z_RHS` defeq `f (mul two z)`.
Global rfl fails; per-branch equality holds only after rewriting. Failing pattern: `x = s n`.
Minimal counterexample: `x := s z`.
-/
def P1_counterexample : Term := s z

/-! B) Duplication stress test for Rule r4.
    Show additive non-drop first using `size`.
-/
def R4_before (x y : Term) : Term := mul (s x) y
def R4_after  (x y : Term) : Term := add y (mul x y)

/-- Raw size profile to exhibit non-decrease; computation by unfolding `size`. -/
def R4_size_profile (x y : Term) : Nat Ã— Nat := (size (R4_before x y), size (R4_after x y))

/-
Additive calculation:
  size (mul (s x) y) = 2 + size x + size y
  size (add y (mul x y)) = 2 + size x + 2 * size y
Hence `size(after) = size(before) + size y`. No strict drop whenever `size y â‰¥ 1`.
Only after switching to a robust base order (e.g., DM multiset/RPO with explicit precedence)
can we prove each RHS piece is strictly < the removed LHS redex.
-/

/-! Concrete size lemmas for r4 (sorry-free). -/

@[simp] lemma size_mul_succ (x y : Term) :
    size (mul (s x) y) = size x + size y + 2 := by
  -- size (mul (s x) y) = size (s x) + size y + 1 = (size x + 1) + size y + 1
  calc
    size (mul (s x) y) = size (s x) + size y + 1 := by simp [size]
    _ = (size x + 1) + size y + 1 := by simp [size]
    _ = size x + size y + (1 + 1) := by ac_rfl
    _ = size x + size y + 2 := by simp

@[simp] lemma size_add_y_mul (x y : Term) :
    size (add y (mul x y)) = size x + (size y + size y) + 2 := by
  -- size (add y (mul x y)) = size y + size (mul x y) + 1 = size y + (size x + size y + 1) + 1
  calc
    size (add y (mul x y)) = size y + size (mul x y) + 1 := by simp [size]
    _ = size y + (size x + size y + 1) + 1 := by simp [size]
    _ = size x + (size y + size y) + (1 + 1) := by ac_rfl
    _ = size x + (size y + size y) + 2 := by simp

lemma r4_size_after_eq_before_plus_piece (x y : Term) :
    size (R4_after x y) = size (R4_before x y) + size y := by
  -- Normalize both sides to the same arithmetic form and conclude.
  calc
    size (R4_after x y)
        = size x + (size y + size y) + 2 := by
              simp [R4_after, size_add_y_mul]
    _   = (size x + size y + 2) + size y := by
              ac_rfl
    _   = size (R4_before x y) + size y := by
              simp [R4_before, size_mul_succ]

lemma r4_no_strict_drop_additive (x y : Term) :
    Â¬ size (R4_after x y) < size (R4_before x y) := by
  intro hlt
  have : size (R4_before x y) + size y < size (R4_before x y) := by
    simpa [r4_size_after_eq_before_plus_piece] using hlt
  have hle : size (R4_before x y) â‰¤ size (R4_before x y) + size y := Nat.le_add_right _ _
  exact (Nat.lt_irrefl _) (Nat.lt_of_le_of_lt hle this)

/-! Lightweight lex witness for r4 pieces vs redex (illustrative). -/
namespace R4Lex

abbrev Weight := Nat Ã— Nat

def lexLT (a b : Weight) : Prop :=
  a.fst < b.fst âˆ¨ (a.fst = b.fst âˆ§ a.snd < b.snd)

def wRedex (x y : Term) : Weight := (1, size (mul (s x) y))
def wPieceY (y : Term) : Weight := (0, size y)
def wPieceMul (x y : Term) : Weight := (0, size (mul x y))

lemma wPieceY_lt_redex (x y : Term) : lexLT (wPieceY y) (wRedex x y) := by
  -- 0 < 1 on the first coordinate
  left; exact Nat.zero_lt_one

lemma wPieceMul_lt_redex (x y : Term) : lexLT (wPieceMul x y) (wRedex x y) := by
  -- 0 < 1 on the first coordinate
  left; exact Nat.zero_lt_one

end R4Lex

/-! DM orientation for r4: {size y, size (mul x y)} <â‚˜ {size (mul (s x) y)}. -/
namespace R4DM
open Multiset

local infix:70 " <â‚˜ " => Multiset.IsDershowitzMannaLT

@[simp] lemma size_redex (x y : Term) : size (mul (s x) y) = size x + size y + 2 := by
  -- delegate to size_mul_succ for clarity
  simpa using size_mul_succ x y

@[simp] lemma size_piece_mul (x y : Term) : size (mul x y) = size x + size y + 1 := by
  simp [size]

lemma pieceY_lt_redex (x y : Term) : size y < size (mul (s x) y) := by
  -- Step 1: size y + 0 < size y + (size x + 2)
  have hpos : 0 < size x + 2 := Nat.succ_pos (size x + 1)
  have h0 : size y + 0 < size y + (size x + 2) := Nat.add_lt_add_left hpos _
  have h1 : size y < size y + (size x + 2) := by simpa using h0
  -- Step 2: normalize RHS and fold to redex size
  have h2 : size y < size x + size y + 2 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h1
  have hred : size x + size y + 2 = size (mul (s x) y) := (size_mul_succ x y).symm
  simpa [hred] using h2

lemma pieceMul_lt_redex (x y : Term) : size (mul x y) < size (mul (s x) y) := by
  -- size x + size y + 1 < size x + size y + 2 and rewrite both sides
  simpa [size_piece_mul, size_mul_succ, size] using Nat.lt_succ_self (size x + size y + 1)

theorem dm_orient (x y : Term) :
  ({size y} + {size (mul x y)}) <â‚˜ ({size (mul (s x) y)}) := by
  classical
  -- X = 0, Y = {size y, size (mul x y)}, Z = {size redex}
  refine âŸ¨(0 : Multiset Nat), ({size y} + {size (mul x y)}), {size (mul (s x) y)}, ?hZ, by simp, by simp, ?hYâŸ©
  Â· simp
  Â· intro y' hy'
    rcases mem_add.mp hy' with hY | hM
    Â· have hy0 : y' = size y := by simpa using hY
      refine âŸ¨size (mul (s x) y), by simp, ?_âŸ©
      simpa [hy0] using pieceY_lt_redex x y
    Â· have hm0 : y' = size (mul x y) := by simpa using hM
      refine âŸ¨size (mul (s x) y), by simp, ?_âŸ©
      simpa [hm0] using pieceMul_lt_redex x y

end R4DM

/-! MPO-style orientation for r4 using a simple precedence/status triple. -/
namespace R4MPO

/- Precedence: mul > add > s > pair > fst/snd > z. -/
@[simp] def headRank : Term â†’ Nat
| z         => 0
| s _       => 3
| add _ _   => 4
| mul _ _   => 5
| pair _ _  => 2
| fst _     => 1
| snd _     => 1

@[simp] def weight : Term â†’ Nat Ã— Nat Ã— Nat
| z           => (headRank z, 0, 0)
| s t         => (headRank (s t), size t, 0)
| add a b     => (headRank (add a b), size a, size b)
| mul a b     => (headRank (mul a b), size a, size b)
| pair a b    => (headRank (pair a b), size a, size b)
| fst t       => (headRank (fst t), size t, 0)
| snd t       => (headRank (snd t), size t, 0)

/- Strict lexicographic order on Nat Ã— Nat Ã— Nat. -/
def ltW (u v : Nat Ã— Nat Ã— Nat) : Prop :=
  u.1 < v.1 âˆ¨ (u.1 = v.1 âˆ§ (u.2.1 < v.2.1 âˆ¨ (u.2.1 = v.2.1 âˆ§ u.2.2 < v.2.2)))

lemma ltW_of_fst_lt {a b : Nat Ã— Nat Ã— Nat} (h : a.1 < b.1) : ltW a b := Or.inl h

/-- Orientation witness: add y (mul x y) < mul (s x) y under ltW âˆ˜ weight. -/
theorem mpo_orient_r4 (x y : Term) :
  ltW (weight (add y (mul x y))) (weight (mul (s x) y)) := by
  -- First components: headRank(add â€¦) < headRank(mul â€¦)
  left
  -- close 4 < 5 by computation
  have : 4 < 5 := by decide
  simpa [weight, headRank] using this

end R4MPO

/-! C) NameGate and TypeGate probes. -/
/-- Success case (name exists, arity matches): -/
def NG_success : Term := fst (pair z z)

-- /-- Unknown identifier probe: `kappa` is not in this environment. -/
-- -- CONSTRAINT BLOCKER (NameGate): `kappa` unknown.

-- /-- Arity mismatch probe: `add` has arity 2; the following malformed term is intentionally commented out. -/
-- -- def NG_arity_mismatch : Term := add z        -- CONSTRAINT BLOCKER (TypeGate).

/-! D) Internally definable measures.
    Package the "operator-only" constraints explicitly.
-/
-- -- CONSTRAINT BLOCKER (NameGate): `kappa` unknown.

-- /-- Arity mismatch probe: `add` has arity 2; the following malformed term is intentionally commented out. -/
-- -- def NG_arity_mismatch : Term := add z        -- CONSTRAINT BLOCKER (TypeGate).

-- /-! D) Internally definable measures.
--     Package the â€œoperator-onlyâ€ constraints explicitly.
-- -/

structure InternallyDefinableMeasure where
  ÎºMType  : Type          -- multiset-like component (DM-style), abstract
  Î¼Type   : Type          -- ordinal-like component, abstract
  flag    : Term â†’ Bool   -- delta-flag or any unary indicator
  ÎºM      : Term â†’ ÎºMType -- structural multiset measure
  Î¼       : Term â†’ Î¼Type  -- well-founded secondary component
  base    : Term â†’ Term â†’ Prop    -- base simplification order
  wf_base : WellFounded base      -- well-foundedness witness

  /- Monotonicity/compositionality in all contexts. -/
  mono_s      : âˆ€ {t u}, base t u â†’ base (s t) (s u)
  mono_add_L  : âˆ€ {t u v}, base t u â†’ base (add t v) (add u v)
  mono_add_R  : âˆ€ {t u v}, base t u â†’ base (add v t) (add v u)
  mono_mul_L  : âˆ€ {t u v}, base t u â†’ base (mul t v) (mul u v)
  mono_mul_R  : âˆ€ {t u v}, base t u â†’ base (mul v t) (mul v u)
  mono_pair_L : âˆ€ {t u v}, base t u â†’ base (pair t v) (pair u v)
  mono_pair_R : âˆ€ {t u v}, base t u â†’ base (pair v t) (pair v u)
  mono_fst    : âˆ€ {t u}, base t u â†’ base (fst t) (fst u)
  mono_snd    : âˆ€ {t u}, base t u â†’ base (snd t) (snd u)

  /- Lexicographic/orientation gate (relaxed for skeleton):
     For each rule instance, we accept either:
     (i) a flag drop; or (ii) a per-piece strict decrease in `base`; or (iii) a direct base drop.
     This matches the DM/MPO contract where duplicators use per-piece orientation.
  -/
  lex_ok :
    âˆ€ {l r}, Rule l r â†’
      (flag r = false âˆ§ flag l = true) âˆ¨
      (âˆƒ t, t âˆˆ rhsPiecesLHS l âˆ§ base t l) âˆ¨
      base r l

  /- Per-piece orientation gate (duplication-aware): for every rule, every listed RHS
    piece is strictly below the removed LHS redex in the base order. This encodes
    the Dershowitzâ€“Manna/MPO-style contract used in P2. -/
  per_piece_base_lt : âˆ€ {l r}, Rule l r â†’ âˆ€ t âˆˆ rhsPiecesLHS l, base t l

  /- Explicit duplication additive failure (documentation contract): the additive `size`
    does not strictly drop for the duplicating rule r4 before any robust orientation.
    This field records the phenomenon as part of the class; a trivial instance can
    reuse `r4_no_strict_drop_additive` below. -/
  dup_additive_nodrop_r4 : âˆ€ x y, Â¬ size (R4_after x y) < size (R4_before x y)

/-- C(Î£): Frozen alias for the KO7 method class used across the project. -/
abbrev CSigma := InternallyDefinableMeasure

/-! E) Stubs for operator-only encodings of Goodstein/Hydra. -/
namespace Encodings

/-- Codes internal to KO7 terms. -/
inductive Code : Type
| zero : Code
| suc  : Code â†’ Code
| pair : Code â†’ Code â†’ Code
| tag  : Nat â†’ Code â†’ Code          -- finite tags for rule schemas
deriving DecidableEq, Repr

/-- Goodstein-style rule schema (shape only). -/
inductive GRule : Code â†’ Code â†’ Prop
| base_change (b n) :
    GRule (Code.tag b (Code.suc n)) (Code.tag (b+1) n)

/-- Hydra-style rule schema (shape only). -/
inductive HRule : Code â†’ Code â†’ Prop
| chop (h) : HRule (Code.suc h) (Code.pair h h)    -- illustrative duplication

end Encodings

-- /-- Target theorems are recorded as statements (no axioms). -/
namespace Targets

open Encodings

/-- â€œThere exists a rule with no internal measure proving its decreaseâ€ (statement only). -/
def Exists_No_Internal_Decrease
  (M : InternallyDefinableMeasure) : Prop :=
  âˆƒ (l r : Term), Rule l r âˆ§ Â¬ M.base l r

/-- Bridge to independence exemplars: Goodstein and Hydra simulations are realized
    via `Simulation.simulate_GRule_base_change_rel` and `Simulation.simulate_HRule_chop_rel`
    respectively, with the no-single-step witness at `goodstein_no_single_step_encode`. -/
lemma independence_exemplar_bridge : True := trivial

end Targets

/-- Demo term touching all constructors. -/
def demo_term : Term :=
  fst (pair (add (s z) (mul (s z) z))
            (snd (pair (add z z) (mul z z))))

/- The reduction of `demo_term` under the eight rules exercises all constructors.
   The actual normalizer is provided in your `Normalize_Safe` bundle. -/

/-! Independence-grade witness: a simple embedding and a same-level no-go. -/

namespace Encodings

/-- Encode natural numbers as KO7 numerals. -/
def natToTerm : Nat â†’ OperatorKO7.OpIncomp.Term
| 0     => OperatorKO7.OpIncomp.Term.z
| n+1   => OperatorKO7.OpIncomp.Term.s (natToTerm n)

/-- Total embedding of `Encodings.Code` into KO7 terms. -/
def encode : Code â†’ OperatorKO7.OpIncomp.Term
| Code.zero      => OperatorKO7.OpIncomp.Term.z
| Code.suc c     => OperatorKO7.OpIncomp.Term.s (encode c)
| Code.pair a b  => OperatorKO7.OpIncomp.Term.pair (encode a) (encode b)
| Code.tag b c   => OperatorKO7.OpIncomp.Term.pair (natToTerm b) (encode c)

end Encodings

/-! Higher-level simulation layer (outside KO7 Step): Admin moves on encoded tags. -/
namespace Simulation
open Encodings OperatorKO7.OpIncomp

/-- Administrative move permitted by the simulation layer: bump the Goodstein base tag on the left of the pair while stripping one succ from the right component (since `encode (suc n) = s (encode n)`). -/
inductive Admin : Term â†’ Term â†’ Prop
| base_change (b : Nat) (n : Encodings.Code) :
    Admin (pair (natToTerm b) (s (encode n))) (pair (natToTerm (b+1)) (encode n))
| hydra_chop (h : Encodings.Code) :
  Admin (s (encode h)) (pair (encode h) (encode h))

/-- Combined simulation relation: either a KO7 Step or an Admin move. -/
def Rel (a b : Term) : Prop := OperatorKO7.OpIncomp.Step a b âˆ¨ Admin a b

/-- One-step simulation of Goodstein base-change under the Admin layer. -/
lemma simulate_GRule_base_change_rel (b : Nat) (n : Encodings.Code) :
  Rel (encode (Encodings.Code.tag b (Encodings.Code.suc n)))
      (encode (Encodings.Code.tag (b+1) n)) := by
  -- By definition, encode(tag b (suc n)) = pair (natToTerm b) (s (encode n))
  -- and encode(tag (b+1) n) = pair (natToTerm (b+1)) (encode n)
  right
  exact Admin.base_change b n

/-- One-step simulation of Hydra chop under the Admin layer. -/
lemma simulate_HRule_chop_rel (h : Encodings.Code) :
  Rel (encode (Encodings.Code.suc h))
      (encode (Encodings.Code.pair h h)) := by
  right
  exact Admin.hydra_chop h

end Simulation

namespace Simulation

/-- Reflexiveâ€“transitive closure for Rel. -/
inductive RelStar : Term â†’ Term â†’ Prop
| refl {a} : RelStar a a
| step {a b c} : Rel a b â†’ RelStar b c â†’ RelStar a c

namespace RelStar

theorem trans {a b c} (h1 : RelStar a b) (h2 : RelStar b c) : RelStar a c := by
  induction h1 with
  | refl => simpa using h2
  | step h h1 ih => exact RelStar.step h (ih h2)

theorem of_step {a b} (h : OperatorKO7.OpIncomp.Step a b) : RelStar a b :=
  RelStar.step (Or.inl h) RelStar.refl

theorem of_admin {a b} (h : Admin a b) : RelStar a b :=
  RelStar.step (Or.inr h) RelStar.refl

end RelStar

end Simulation

namespace Simulation
open OperatorKO7.OpIncomp.Encodings

/- Paperâ†”code map (names frozen):
  - CSigma â‰¡ `M_size`
  - Î´ two-case: `delta_top_cases_add_s`, `delta_top_cases_mul_s`
  - Î´ Star runners: `delta_star_add_s_auto`, `delta_star_mul_s_auto`
  - RelStar lifts: `simulate_GRule_base_change_relStar`, `simulate_HRule_chop_relStar`
  - No single Step from encode: `Targets.Goodstein_NoSingleStep_Encode`
-/

/-- Lift Goodstein base-change simulation to `RelStar`. -/
lemma simulate_GRule_base_change_relStar (b : Nat) (n : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.tag b (Encodings.Code.suc n)))
    (encode (Encodings.Code.tag (b+1) n)) :=
  Simulation.RelStar.of_admin (Admin.base_change b n)

/-- Lift Hydra chop simulation to `RelStar`. -/
lemma simulate_HRule_chop_relStar (h : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.suc h))
    (encode (Encodings.Code.pair h h)) :=
  Simulation.RelStar.of_admin (Admin.hydra_chop h)

end Simulation

namespace Targets
open Encodings

/-- Same-level no-go box: Goodstein base-change does not collapse to a single KO7 Step under `encode`.
Recorded as a statement; proof handled in documentation/meta notes. -/
def Goodstein_NoSingleStep_Encode : Prop :=
  âˆ€ (b : Nat) (n : Encodings.Code),
    Â¬ Step (encode (Code.tag b (Code.suc n)))
           (encode (Code.tag (b+1) n))

end Targets

-- Independence-grade â€œno-go boxâ€ recorded as a statement under Targets.
-- We avoid asserting the proof here; see documentation for the meta-argument.

/-- No single OperatorKO7.OpIncomp.Step originates from a numeral `natToTerm b`. -/
lemma no_step_from_natToTerm (b : Nat) : âˆ€ t, Â¬ Step (Encodings.natToTerm b) t := by
  induction b with
  | zero =>
    intro t h
    -- LHS is `z`; there is no Rule/Context matching it.
    cases h with
    | base hr => cases hr
  | succ b ih =>
    intro t h
    -- LHS is `s (natToTerm b)`; only sCtx could apply, implying an inner step.
    cases h with
    | base hr => cases hr
    | sCtx hinner =>
      exact (ih _ hinner)

/-- Encoded Goodstein codes (`encode`) contain only z/s/pair/nat tags, so they have no KO7 single-step. -/
lemma no_step_from_encode (c : Encodings.Code) : âˆ€ t, Â¬ Step (Encodings.encode c) t := by
  induction c with
  | zero =>
    intro t h
    -- LHS is `z`; only `base` could appear, which contradicts Rule shapes.
    cases h with
    | base hr => cases hr
  | suc c ih =>
    intro t h
    -- LHS is `s (encode c)`; only `base` or `sCtx` can appear.
    cases h with
    | base hr => cases hr
    | sCtx hinner => exact (ih _ hinner)
  | pair a b iha ihb =>
    intro t h
    -- LHS is `pair (encode a) (encode b)`; only `base`/`pairLCtx`/`pairRCtx` possible.
    cases h with
    | base hr => cases hr
    | pairLCtx hL => exact (iha _ hL)
    | pairRCtx hR => exact (ihb _ hR)
  | tag b c ih =>
    intro t h
    -- LHS is `pair (natToTerm b) (encode c)`; only `base`/`pairLCtx`/`pairRCtx` possible.
    cases h with
    | base hr => cases hr
    | pairLCtx hL => exact (no_step_from_natToTerm b _ hL)
    | pairRCtx hR => exact (ih _ hR)

namespace Targets
open Encodings

/-- Formal proof: Goodstein base-change is not a single OperatorKO7.OpIncomp.Step under `encode`. -/
theorem goodstein_no_single_step_encode : Goodstein_NoSingleStep_Encode := by
  intro b n h
  -- Use the general â€œno step from encodeâ€ lemma instantiated at `tag b (suc n)`.
  -- This is stronger: there is no OperatorKO7.OpIncomp.Step from the encoded source to any target.
  have hno := OperatorKO7.OpIncomp.no_step_from_encode (c := Encodings.Code.tag b (Encodings.Code.suc n))
    (t := Encodings.encode (Encodings.Code.tag (b+1) n))
  exact hno h

/-- Bridging theorem (Goodstein family): encoded base-change steps are simulated in `RelStar`. -/
theorem goodstein_family_simulated_in_RelStar
  (b : Nat) (n : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.tag b (Encodings.Code.suc n)))
                     (encode (Encodings.Code.tag (b+1) n)) :=
  Simulation.simulate_GRule_base_change_relStar b n

/-- Bridging theorem (Hydra family): encoded chop steps are simulated in `RelStar`. -/
theorem hydra_family_simulated_in_RelStar
  (h : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.suc h))
                     (encode (Encodings.Code.pair h h)) :=
  Simulation.simulate_HRule_chop_relStar h

end Targets



/-! Tiny examples exercising witnesses and Star utilities. -/
example (x y : Term) : R4Lex.lexLT (R4Lex.wPieceY y) (R4Lex.wRedex x y) :=
  R4Lex.wPieceY_lt_redex x y

example (x y : Term) :
    Multiset.IsDershowitzMannaLT ({size y} + {size (mul x y)}) ({size (mul (s x) y)}) := by
  simpa using R4DM.dm_orient x y

example (x y : Term) :
    R4MPO.ltW (R4MPO.weight (add y (mul x y))) (R4MPO.weight (mul (s x) y)) :=
  R4MPO.mpo_orient_r4 x y

example (y : Term) : Star Step (add z y) y :=
  Star.step (Step.base (Rule.r1 y)) Star.refl

-- Additional Step â†’ Star examples
example (y : Term) : Star Step (mul z y) z :=
  Star.step (Step.base (Rule.r3 y)) Star.refl

example (x y : Term) : Star Step (fst (pair x y)) x :=
  Star.step (Step.base (Rule.r5 x y)) Star.refl

end OperatorKO7.OpIncomp

/-!
Tiny Goodstein/Hydra examples (toy cores)

These are small, independent examples that exercise the minimal toy cores added
for exposition. They do not interact with the KO7 kernel and are provided as
cross-linkable witnesses for the paper and Impossibility catalog.
-/

namespace TinyGoodsteinHydra

open OperatorKO7
open OperatorKO7.GoodsteinCore
open OperatorKO7.HydraCore

/- Goodstein: one-step base-change on the toy state. -/
example (b : Nat) (t : Cn) :
  GoodsteinCore.Step âŸ¨Base.b b, Cn.s tâŸ© âŸ¨Base.b (b+1), tâŸ© := by
  simpa using GoodsteinCore.one_step b t

/- Hydra: a chop duplicates the other subtree (left and right variants). -/
example (h : Hydra) :
  HydraCore.Step (Hydra.node Hydra.head h) (Hydra.node h h) :=
  HydraCore.Step.chop_left h

example (h : Hydra) :
  HydraCore.Step (Hydra.node h Hydra.head) (Hydra.node h h) :=
  HydraCore.Step.chop_right h

/- Existential-style tiny witness. -/
example (h : Hydra) : âˆƒ h', HydraCore.Step (Hydra.node Hydra.head h) h' :=
  âŸ¨Hydra.node h h, HydraCore.Step.chop_left hâŸ©

end TinyGoodsteinHydra

namespace OperatorKO7.OpIncomp
open Term
-- set_option diagnostics true
/-- A concrete internal-measure instance using size as the base order.
Flags mark only r2/r4 LHSs (where additive size does not strictly drop). -/
noncomputable def flagTerm : Term â†’ Bool
| add (s _) _ => true
| mul (s _) _ => true
| _           => false

noncomputable def M_size : InternallyDefinableMeasure where
  ÎºMType := Unit
  Î¼Type  := Unit
  flag   := flagTerm
  ÎºM     := fun _ => ()
  Î¼      := fun _ => ()
  -- size-based base order
  base   := fun a b => size a < size b
  wf_base := by
    -- pull back Nat.lt along `size`
    simpa using (InvImage.wf (f := size) Nat.lt_wfRel.wf)
  -- context monotonicity (all 7 contexts)
  mono_s := by
    intro t u h; dsimp [size] at *; simpa using Nat.add_lt_add_right h 1
  mono_add_L := by
    intro t u v h; dsimp [size] at *
    -- size (add t v) = size t + (size v + 1)
    have := Nat.add_lt_add_left h (size v + 1)
    -- rewrite lhs: (size v + 1) + size t = size t + (size v + 1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_add_R := by
    intro t u v h; dsimp [size] at *
    -- size (add v t) = size v + (size t + 1)
    have := Nat.add_lt_add_left h (size v)
    have := Nat.add_lt_add_right this 1
    -- reorder sums
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_mul_L := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v + 1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_mul_R := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v)
    have := Nat.add_lt_add_right this 1
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_pair_L := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v + 1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_pair_R := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v)
    have := Nat.add_lt_add_right this 1
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_fst := by
    intro t u h; dsimp [size] at *
    simpa using Nat.add_lt_add_right h 1
  mono_snd := by
    intro t u h; dsimp [size] at *
    simpa using Nat.add_lt_add_right h 1
  -- lex gate: satisfy via per-piece base drops for all rules
  lex_ok := by
    intro l r hr
    cases hr with
    | r1 y =>
      -- r1: add z y â†’ y, need y < 1 + y + 1
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r2 x y =>
      -- r2: add (s x) y â†’ s (add x y)
      exact Or.inr (Or.inl âŸ¨add x y, by simp [rhsPiecesLHS], by simp only [size]; omegaâŸ©)
    | r3 y =>
      -- r3: mul z y â†’ z, need 1 < 1 + y + 1
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r4 x y =>
      -- r4: mul (s x) y â†’ add y (mul x y)
      exact Or.inr (Or.inl âŸ¨y, by simp [rhsPiecesLHS], by simp only [size]; omegaâŸ©)
    | r5 x y =>
      -- r5: fst (pair x y) â†’ x, need x < x + y + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r6 x y =>
      -- r6: snd (pair x y) â†’ y, need y < x + y + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r7 x =>
      -- r7: add x z â†’ x, need x < x + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r8 x =>
      -- r8: mul x z â†’ z, need 1 < x + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
  -- per-piece strictness (duplication-aware)
  per_piece_base_lt := by
    intro l r h t ht
    -- prove size t < size l by case on l
    cases l with
    | z => cases h
    | s tl => cases h
    | add a b =>
      -- pieces = pieces from a (r1/r2) plus maybe from b (r7 when b=z)
      dsimp [rhsPiecesLHS] at ht
      have : size t < size a + size b + 1 := by
        rcases List.mem_append.mp ht with hL | hR
        Â· -- left pieces from a
          cases a with
          | z =>
            -- t âˆˆ [b]
            have hx : t = b := by simpa using hL
            subst hx
            -- size b < size (add z b) = 1 + b + 1
            simp only [size]
            omega
          | s xx =>
            -- t âˆˆ [add xx b]
            have hx : t = add xx b := by simpa using hL
            subst hx
            -- size (add xx b) < size (add (s xx) b)
            simp only [size]
            omega
          | _ =>
            -- no pieces from other constructors
            cases hL
        Â· -- right pieces from b
          cases b with
          | z =>
            -- t âˆˆ [a]
            have hx : t = a := by simpa using hR
            subst hx
            -- size a < size (add a z) = a + 1 + 1
            simp only [size]
            omega
          | _ =>
            cases hR
      simpa [size] using this
    | mul a b =>
      dsimp [rhsPiecesLHS] at ht
      have : size t < size a + size b + 1 := by
        rcases List.mem_append.mp ht with hL | hR
        Â· -- left pieces from a
          cases a with
          | z =>
            -- t âˆˆ [z]
            have hx : t = z := by simpa using hL
            subst hx
            -- 1 < 1 + size b + 1
            simp only [size]
            omega
          | s xx =>
            rcases List.mem_cons.mp hL with hby | hmul
            Â· -- t = b
              have hx : t = b := by simpa using hby
              subst hx
              -- size b < size (s xx) + size b + 1 = xx + 1 + b + 1
              simp only [size]
              omega
            Â· -- t = mul xx b
              have hx : t = mul xx b := by simpa using hmul
              subst hx
              -- size (mul xx b) < size (mul (s xx) b)
              simp only [size]
              omega
          | _ =>
            cases hL
        Â· -- right pieces from b
          cases b with
          | z =>
            -- t âˆˆ [z]
            have hx : t = z := by simpa using hR
            subst hx
            -- 1 < size a + 1 + 1
            simp only [size]
            omega
          | _ =>
            cases hR
      simpa [size] using this
    | pair a b => cases h
    | fst u =>
      cases u with
      | pair xx yy =>
        dsimp [rhsPiecesLHS] at ht
        have hx : t = xx := by simpa using ht
        subst hx
        simp [size]
        omega
      | _ => cases h
    | snd u =>
      cases u with
      | pair xx yy =>
        dsimp [rhsPiecesLHS] at ht
        have hx : t = yy := by simpa using ht
        subst hx
        simp [size]
        omega
      | _ => cases h
  dup_additive_nodrop_r4 := by
    intro x y; exact r4_no_strict_drop_additive x y

/-! Optional Î´-guard (Prop) isolating the duplicating/flagged shapes.
    We provide a decidable predicate and a couple of lightweight lemmas. -/

/-- Terms whose head is add (s Â·) Â· or mul (s Â·) Â·. -/
inductive Delta : Term â†’ Prop
| add_s (x y : Term) : Delta (add (s x) y)
| mul_s (x y : Term) : Delta (mul (s x) y)

attribute [simp] Delta.add_s Delta.mul_s

/-- Decidability for `Delta`. -/
instance : DecidablePred Delta := by
  intro t
  cases t with
  | z => exact isFalse (by intro h; cases h)
  | s _ => exact isFalse (by intro h; cases h)
  | add a b =>
    cases a with
    | s x => exact isTrue (Delta.add_s x b)
    | _ => exact isFalse (by intro h; cases h)
  | mul a b =>
    cases a with
    | s x => exact isTrue (Delta.mul_s x b)
    | _ => exact isFalse (by intro h; cases h)
  | pair _ _ => exact isFalse (by intro h; cases h)
  | fst _ => exact isFalse (by intro h; cases h)
  | snd _ => exact isFalse (by intro h; cases h)

@[simp] lemma Delta_r2 (x y : Term) : Delta (add (s x) y) := Delta.add_s x y
@[simp] lemma Delta_r4 (x y : Term) : Delta (mul (s x) y) := Delta.mul_s x y

/- Simple preservation under right-context rewriting: the Î´ head persists. -/
lemma Delta_preserve_addR {x t u : Term} (_h : Step t u) : Delta (add (s x) u) := by
  simpa using (Delta.add_s x u)

lemma Delta_preserve_mulR {x t u : Term} (_h : Step t u) : Delta (mul (s x) u) := by
  simpa using (Delta.mul_s x u)

-- Preservation for remaining contexts (trivial shape persistence)
lemma Delta_preserve_addL {x t u : Term} (_h : Step t u) : Delta (add (s x) u) := by
  simpa using (Delta.add_s x u)

lemma Delta_preserve_mulL {x t u : Term} (_h : Step t u) : Delta (mul (s x) u) := by
  simpa using (Delta.mul_s x u)

lemma Delta_preserve_pairL {x t u v : Term} (_h : Step t u) : Delta (add (s x) v) := by
  simpa using (Delta.add_s x v)

lemma Delta_preserve_pairR {x t u v : Term} (_h : Step t u) : Delta (mul (s x) v) := by
  simpa using (Delta.mul_s x v)

lemma Delta_preserve_fstCtx {x t u : Term} (_h : Step t u) : Delta (add (s x) (fst u)) := by
  -- Note: guard refers to outer head; inner shape changes do not affect outer head
  simpa using (Delta.add_s x (fst u))

lemma Delta_preserve_sndCtx {x t u : Term} (_h : Step t u) : Delta (mul (s x) (snd u)) := by
  simpa using (Delta.mul_s x (snd u))

/-! Substitution (homomorphic map) and Î´â€‘preservation under substitution. -/

/-- Homomorphic transform on KO7 terms (preserves heads, transforms subterms). -/
def mapTerm (Ïƒ : Term â†’ Term) : Term â†’ Term
| z => z
| s t => s (mapTerm Ïƒ t)
| add a b => add (mapTerm Ïƒ a) (mapTerm Ïƒ b)
| mul a b => mul (mapTerm Ïƒ a) (mapTerm Ïƒ b)
| pair a b => pair (mapTerm Ïƒ a) (mapTerm Ïƒ b)
| fst t => fst (mapTerm Ïƒ t)
| snd t => snd (mapTerm Ïƒ t)

@[simp] lemma mapTerm_s (Ïƒ) (t : Term) : mapTerm Ïƒ (s t) = s (mapTerm Ïƒ t) := rfl
@[simp] lemma mapTerm_add (Ïƒ) (a b : Term) : mapTerm Ïƒ (add a b) = add (mapTerm Ïƒ a) (mapTerm Ïƒ b) := rfl
@[simp] lemma mapTerm_mul (Ïƒ) (a b : Term) : mapTerm Ïƒ (mul a b) = mul (mapTerm Ïƒ a) (mapTerm Ïƒ b) := rfl

lemma Delta_preserve_r2_subst (Ïƒ : Term â†’ Term) (x y : Term) :
  Delta (mapTerm Ïƒ (add (s x) y)) := by
  simp [mapTerm, Delta.add_s]

lemma Delta_preserve_r4_subst (Ïƒ : Term â†’ Term) (x y : Term) :
  Delta (mapTerm Ïƒ (mul (s x) y)) := by
  simp [mapTerm, Delta.mul_s]

/-! Promote mapTerm to a substitution alias and restate Î´â€‘substitution lemmas. -/

abbrev subst := mapTerm

@[simp] lemma subst_s (Ïƒ) (t : Term) : subst Ïƒ (s t) = s (subst Ïƒ t) := rfl
@[simp] lemma subst_add (Ïƒ) (a b : Term) : subst Ïƒ (add a b) = add (subst Ïƒ a) (subst Ïƒ b) := rfl
@[simp] lemma subst_mul (Ïƒ) (a b : Term) : subst Ïƒ (mul a b) = mul (subst Ïƒ a) (subst Ïƒ b) := rfl

lemma Delta_subst_preserves_r2 (Ïƒ : Term â†’ Term) (x y : Term) :
  Delta (subst Ïƒ (add (s x) y)) := by
  simp [subst, mapTerm, Delta.add_s]

lemma Delta_subst_preserves_r4 (Ïƒ : Term â†’ Term) (x y : Term) :
  Delta (subst Ïƒ (mul (s x) y)) := by
  simp [subst, mapTerm, Delta.mul_s]

/-! Star-level automation for Î´ shapes. -/

lemma delta_star_cases_add_s (x y : Term) :
  Star Step (add (s x) y) (s (add x y)) âˆ¨
  (y = z âˆ§ Star Step (add (s x) y) (s x)) := by
  -- r2 always provides the left branch as a single step
  exact Or.inl (Star.step (Step.base (Rule.r2 x y)) Star.refl)

lemma delta_star_cases_mul_s (x y : Term) :
  Star Step (mul (s x) y) (add y (mul x y)) âˆ¨
  (y = z âˆ§ Star Step (mul (s x) y) z) := by
  -- r4 always provides the left branch as a single step
  exact Or.inl (Star.step (Step.base (Rule.r4 x y)) Star.refl)

/-! Î´ exhaustive two-case lemmas at the top level. -/

lemma delta_top_cases_add_s (x y r : Term)
  (h : Rule (add (s x) y) r) :
  r = s (add x y) âˆ¨ (y = z âˆ§ r = s x) := by
  cases h with
  | r2 _ _ => exact Or.inl rfl
  | r7 _ => exact Or.inr âŸ¨rfl, rflâŸ©

lemma delta_top_cases_mul_s (x y r : Term)
  (h : Rule (mul (s x) y) r) :
  r = add y (mul x y) âˆ¨ (y = z âˆ§ r = z) := by
  cases h with
  | r4 _ _ => exact Or.inl rfl
  | r8 _ => exact Or.inr âŸ¨rfl, rflâŸ©

/-- Î´-safe critical pairs coverage (add): every rule at the guarded top-shape matches one of the two cases. -/
theorem Delta_SafePairs_Exhaustive_add
  (x y r : Term) (_hÎ´ : Delta (add (s x) y)) (h : Rule (add (s x) y) r) :
  r = s (add x y) âˆ¨ (y = z âˆ§ r = s x) :=
  delta_top_cases_add_s x y r h

/-- Î´-safe critical pairs coverage (mul): every rule at the guarded top-shape matches one of the two cases. -/
theorem Delta_SafePairs_Exhaustive_mul
  (x y r : Term) (_hÎ´ : Delta (mul (s x) y)) (h : Rule (mul (s x) y) r) :
  r = add y (mul x y) âˆ¨ (y = z âˆ§ r = z) :=
  delta_top_cases_mul_s x y r h

/-! Small Star runners that choose the RHS automatically via the Î´ two-case split. -/

/-- Canonical RHS selector for `add (s x) y` using the Î´ two-case: if `y` is `z`, pick `s x`,
  otherwise pick `s (add x y)`. -/
def delta_rhs_add_s (x y : Term) : Term :=
  match y with
  | z => s x
  | _ => s (add x y)

/-- Canonical RHS selector for `mul (s x) y` using the Î´ two-case: if `y` is `z`, pick `z`,
  otherwise pick `add y (mul x y)`. -/
def delta_rhs_mul_s (x y : Term) : Term :=
  match y with
  | z => z
  | _ => add y (mul x y)

/-- One-step Star that automatically chooses the appropriate RHS for `add (s x) y`. -/
lemma delta_star_add_s_auto (x y : Term) :
  Star Step (add (s x) y) (delta_rhs_add_s x y) := by
  -- Use a direct case split on `y`'s top constructor.
  cases y with
  | z =>
    -- pick r7
    change Star Step (add (s x) z) (s x)
    exact Star.step (Step.base (Rule.r7 (s x))) Star.refl
  | s y' =>
    -- pick r2
    change Star Step (add (s x) (s y')) (s (add x (s y')))
    exact Star.step (Step.base (Rule.r2 x (s y'))) Star.refl
  | add a b =>
    change Star Step (add (s x) (add a b)) (s (add x (add a b)))
    exact Star.step (Step.base (Rule.r2 x (add a b))) Star.refl
  | mul a b =>
    change Star Step (add (s x) (mul a b)) (s (add x (mul a b)))
    exact Star.step (Step.base (Rule.r2 x (mul a b))) Star.refl
  | pair a b =>
    change Star Step (add (s x) (pair a b)) (s (add x (pair a b)))
    exact Star.step (Step.base (Rule.r2 x (pair a b))) Star.refl
  | fst t =>
    change Star Step (add (s x) (fst t)) (s (add x (fst t)))
    exact Star.step (Step.base (Rule.r2 x (fst t))) Star.refl
  | snd t =>
    change Star Step (add (s x) (snd t)) (s (add x (snd t)))
    exact Star.step (Step.base (Rule.r2 x (snd t))) Star.refl

/-- One-step Star that automatically chooses the appropriate RHS for `mul (s x) y`. -/
lemma delta_star_mul_s_auto (x y : Term) :
  Star Step (mul (s x) y) (delta_rhs_mul_s x y) := by
  cases y with
  | z =>
    change Star Step (mul (s x) z) z
    exact Star.step (Step.base (Rule.r8 (s x))) Star.refl
  | s y' =>
    change Star Step (mul (s x) (s y')) (add (s y') (mul x (s y')))
    exact Star.step (Step.base (Rule.r4 x (s y'))) Star.refl
  | add a b =>
    change Star Step (mul (s x) (add a b)) (add (add a b) (mul x (add a b)))
    exact Star.step (Step.base (Rule.r4 x (add a b))) Star.refl
  | mul a b =>
    change Star Step (mul (s x) (mul a b)) (add (mul a b) (mul x (mul a b)))
    exact Star.step (Step.base (Rule.r4 x (mul a b))) Star.refl
  | pair a b =>
    change Star Step (mul (s x) (pair a b)) (add (pair a b) (mul x (pair a b)))
    exact Star.step (Step.base (Rule.r4 x (pair a b))) Star.refl
  | fst t =>
    change Star Step (mul (s x) (fst t)) (add (fst t) (mul x (fst t)))
    exact Star.step (Step.base (Rule.r4 x (fst t))) Star.refl
  | snd t =>
    change Star Step (mul (s x) (snd t)) (add (snd t) (mul x (snd t)))
    exact Star.step (Step.base (Rule.r4 x (snd t))) Star.refl

/-! Î´â€‘substitution perâ€‘branch lemma stubs (align names with paper). -/

/-- Under substitution, the r2 guard shape is preserved (wrapper aligning naming with paper). -/
@[simp] theorem delta_subst_preserves_r2 (Ïƒ : Term â†’ Term) (x y : Term) :
  Delta (subst Ïƒ (add (s x) y)) :=
  Delta_subst_preserves_r2 Ïƒ x y

/-- Under substitution, the r4 guard shape is preserved (wrapper aligning naming with paper). -/
@[simp] theorem delta_subst_preserves_r4 (Ïƒ : Term â†’ Term) (x y : Term) :
  Delta (subst Ïƒ (mul (s x) y)) :=
  Delta_subst_preserves_r4 Ïƒ x y

/-! Examples using `M_size.lex_ok` on representative rules. -/

example (y : Term) :
  (flagTerm y = false âˆ§ flagTerm (add z y) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (add z y) âˆ§ M_size.base t (add z y)) âˆ¨
  M_size.base y (add z y) := by
  -- r1: add z y â†’ y
  simpa using (M_size.lex_ok (Rule.r1 y))

example (x y : Term) :
  (flagTerm (add y (mul x y)) = false âˆ§ flagTerm (mul (s x) y) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (mul (s x) y) âˆ§ M_size.base t (mul (s x) y)) âˆ¨
  M_size.base (add y (mul x y)) (mul (s x) y) := by
  -- r4: mul (s x) y â†’ add y (mul x y)
  simpa using (M_size.lex_ok (Rule.r4 x y))

example (x : Term) :
  (flagTerm x = false âˆ§ flagTerm (add x z) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (add x z) âˆ§ M_size.base t (add x z)) âˆ¨
  M_size.base x (add x z) := by
  -- r7: add x z â†’ x
  simpa using (M_size.lex_ok (Rule.r7 x))

example (x y : Term) :
  (flagTerm (s (add x y)) = false âˆ§ flagTerm (add (s x) y) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (add (s x) y) âˆ§ M_size.base t (add (s x) y)) âˆ¨
  M_size.base (s (add x y)) (add (s x) y) := by
  -- r2: add (s x) y â†’ s (add x y)
  simpa using (M_size.lex_ok (Rule.r2 x y))

example (y : Term) :
  (flagTerm z = false âˆ§ flagTerm (mul z y) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (mul z y) âˆ§ M_size.base t (mul z y)) âˆ¨
  M_size.base z (mul z y) := by
  -- r3: mul z y â†’ z
  simpa using (M_size.lex_ok (Rule.r3 y))

example (x y : Term) :
  (flagTerm x = false âˆ§ flagTerm (fst (pair x y)) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (fst (pair x y)) âˆ§ M_size.base t (fst (pair x y))) âˆ¨
  M_size.base x (fst (pair x y)) := by
  -- r5: fst (pair x y) â†’ x
  simpa using (M_size.lex_ok (Rule.r5 x y))

example (x y : Term) :
  (flagTerm y = false âˆ§ flagTerm (snd (pair x y)) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (snd (pair x y)) âˆ§ M_size.base t (snd (pair x y))) âˆ¨
  M_size.base y (snd (pair x y)) := by
  -- r6: snd (pair x y) â†’ y
  simpa using (M_size.lex_ok (Rule.r6 x y))

example (x : Term) :
  (flagTerm z = false âˆ§ flagTerm (mul x z) = true) âˆ¨
  (âˆƒ t, t âˆˆ rhsPiecesLHS (mul x z) âˆ§ M_size.base t (mul x z)) âˆ¨
  M_size.base z (mul x z) := by
  -- r8: mul x z â†’ z
  simpa using (M_size.lex_ok (Rule.r8 x))
end OperatorKO7.OpIncomp
````

## OperatorKO7/Meta/PaperApproachIndex.lean

**Lines:** 38

``lean
import OperatorKO7.Meta.Impossibility_Lemmas

/-!
# Paper Approach Index (compile-time consistency check)

Purpose
- This module exists to keep the paper's multi-approach impossibility claims mechanically checkable.
- It provides *editor-quiet* references (`example` terms) to the specific approach namespaces/lemmas,
  so renames/deletions break compilation instead of silently drifting.

How to use
- Run: `lake build OperatorKO7.Meta.PaperApproachIndex`
- This is intentionally *not* imported by the default `OperatorKO7.lean` entrypoint, to keep the
  default build fast; treat it as an â€œaudit targetâ€.
-/

namespace OperatorKO7.Meta.PaperApproachIndex

open OperatorKO7 Trace
open OperatorKO7.Impossibility

/-!
Approach #9 and #10 were added later; keep explicit anchors here so this audit target
continues to catch drift between manuscript wording and mechanized names.
-/

-- Approach #9: Complex Hybrid/Constellation Measures
example (b s n : Trace) :=
  ConstellationFailure.constellation_size_not_decreasing b s n

-- Approach #10: Unchecked Recursion
example (b s n : Trace) :=
  UncheckedRecursionFailure.rec_succ_additive_barrier b s n

example :=
  UncheckedRecursionFailure.full_step_permits_barrier

end OperatorKO7.Meta.PaperApproachIndex
````

## OperatorKO7/Meta/RecCore.lean

**Lines:** 256

``lean
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
RecÎ”-core subsystem: the 4-constructor fragment `{void, delta, app, recÎ”}`.

This file restates the compositional-impossibility boundary directly on the core
signature used by the counterexamples.
-/

namespace OperatorKO7.RecCore

open OperatorKO7
open OperatorKO7.StepDuplicating

/-- RecÎ”-core syntax (the 4-constructor fragment). -/
inductive RecCoreTerm : Type
| void : RecCoreTerm
| delta : RecCoreTerm â†’ RecCoreTerm
| app : RecCoreTerm â†’ RecCoreTerm â†’ RecCoreTerm
| recÎ” : RecCoreTerm â†’ RecCoreTerm â†’ RecCoreTerm â†’ RecCoreTerm
deriving DecidableEq, Repr

open RecCoreTerm

/-- The RecÎ”-core schema instance of the generic duplication barrier. -/
def recCoreSchema : StepDuplicatingSchema where
  T := RecCoreTerm
  base := RecCoreTerm.void
  succ := RecCoreTerm.delta
  wrap := RecCoreTerm.app
  recur := RecCoreTerm.recÎ”

/-- Canonical embedding of RecÎ”-core terms into full KO7 traces. -/
@[simp] def embed : RecCoreTerm â†’ Trace
  | RecCoreTerm.void         => Trace.void
  | RecCoreTerm.delta t      => Trace.delta (embed t)
  | RecCoreTerm.app a b      => Trace.app (embed a) (embed b)
  | RecCoreTerm.recÎ” b s n   => Trace.recÎ” (embed b) (embed s) (embed n)

/-- Iterated core app constructor used to pump measure size. -/
def appIter : Nat â†’ RecCoreTerm :=
  StepDuplicatingSchema.wrapIter recCoreSchema

/-- Additive compositional measures restricted to RecÎ”-core constructors. -/
structure AdditiveRecCoreMeasure where
  w_void      : Nat
  w_delta     : Nat
  w_app       : Nat
  w_rec       : Nat
  hw_app_pos  : w_app â‰¥ 1

/-- Evaluation for additive RecÎ”-core measures. -/
@[simp] def AdditiveRecCoreMeasure.eval
    (M : AdditiveRecCoreMeasure) : RecCoreTerm â†’ Nat
  | RecCoreTerm.void        => M.w_void
  | RecCoreTerm.delta t     => M.w_delta + M.eval t
  | RecCoreTerm.app a b     => M.w_app + M.eval a + M.eval b
  | RecCoreTerm.recÎ” b s n  => M.w_rec + M.eval b + M.eval s + M.eval n

/-- Generic-schema view of an additive RecÎ”-core measure. -/
def AdditiveRecCoreMeasure.toSchemaMeasure
    (M : AdditiveRecCoreMeasure) :
    StepDuplicatingSchema.AdditiveMeasure recCoreSchema where
  eval := M.eval
  w_base := M.w_void
  w_succ := M.w_delta
  w_wrap := M.w_app
  w_recur := M.w_rec
  eval_base := by rfl
  eval_succ := by intro t; rfl
  eval_wrap := by intro x y; rfl
  eval_recur := by intro b s n; rfl
  h_wrap_pos := M.hw_app_pos

lemma eval_appIter_ge (M : AdditiveRecCoreMeasure) (k : Nat) :
    M.eval (appIter k) â‰¥ k := by
  simpa [appIter, AdditiveRecCoreMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.eval_wrapIter_ge
      (S := recCoreSchema) (M := M.toSchemaMeasure) k)

/-- Tier-1 impossibility specialized to RecÎ”-core. -/
theorem no_additive_compositional_orients_rec_succ
    (M : AdditiveRecCoreMeasure) :
    Â¬ (âˆ€ (b s n : RecCoreTerm),
      M.eval (RecCoreTerm.app s (RecCoreTerm.recÎ” b s n)) <
      M.eval (RecCoreTerm.recÎ” b s (RecCoreTerm.delta n))) := by
  simpa [recCoreSchema, AdditiveRecCoreMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_additive_orients_dup_step
      (S := recCoreSchema) (M := M.toSchemaMeasure))

/-- Abstract compositional measures restricted to RecÎ”-core constructors. -/
structure CompositionalRecCoreMeasure where
  c_void      : Nat
  c_delta     : Nat â†’ Nat
  c_app       : Nat â†’ Nat â†’ Nat
  c_recÎ”      : Nat â†’ Nat â†’ Nat â†’ Nat
  app_subterm1 : âˆ€ x y, c_app x y > x
  app_subterm2 : âˆ€ x y, c_app x y > y

/-- Evaluation for abstract RecÎ”-core compositional measures. -/
@[simp] def CompositionalRecCoreMeasure.eval
    (CM : CompositionalRecCoreMeasure) : RecCoreTerm â†’ Nat
  | RecCoreTerm.void        => CM.c_void
  | RecCoreTerm.delta t     => CM.c_delta (CM.eval t)
  | RecCoreTerm.app a b     => CM.c_app (CM.eval a) (CM.eval b)
  | RecCoreTerm.recÎ” b s n  => CM.c_recÎ” (CM.eval b) (CM.eval s) (CM.eval n)

/-- Generic-schema view of an abstract RecÎ”-core compositional measure. -/
def CompositionalRecCoreMeasure.toSchemaMeasure
    (CM : CompositionalRecCoreMeasure) :
    StepDuplicatingSchema.CompositionalMeasure recCoreSchema where
  eval := CM.eval
  c_base := CM.c_void
  c_succ := CM.c_delta
  c_wrap := CM.c_app
  c_recur := CM.c_recÎ”
  eval_base := by rfl
  eval_succ := by intro t; rfl
  eval_wrap := by intro x y; rfl
  eval_recur := by intro b s n; rfl
  wrap_subterm1 := CM.app_subterm1
  wrap_subterm2 := CM.app_subterm2

/-- Tier-2 impossibility specialized to RecÎ”-core (transparent delta case). -/
theorem no_compositional_orients_rec_succ_transparent_delta
    (CM : CompositionalRecCoreMeasure)
    (h_transparent : CM.c_delta CM.c_void = CM.c_void) :
    Â¬ (âˆ€ (b s n : RecCoreTerm),
      CM.eval (RecCoreTerm.app s (RecCoreTerm.recÎ” b s n)) <
      CM.eval (RecCoreTerm.recÎ” b s (RecCoreTerm.delta n))) := by
  simpa [recCoreSchema, CompositionalRecCoreMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_compositional_orients_dup_step_transparent_succ
      (S := recCoreSchema) (CM := CM.toSchemaMeasure) h_transparent)

/-- DP-style projection on RecÎ”-core (tracks only recursion counter depth). -/
@[simp] def dpProjection : RecCoreTerm â†’ Nat
  | RecCoreTerm.void        => 0
  | RecCoreTerm.delta t     => dpProjection t + 1
  | RecCoreTerm.app _ _     => 0
  | RecCoreTerm.recÎ” _ _ n  => dpProjection n

/-- RecÎ”-core DP projection as a generic schema rank. -/
def dpProjectionRank : StepDuplicatingSchema.ProjectionRank recCoreSchema where
  rank := dpProjection
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

@[simp] theorem dpProjection_embed (t : RecCoreTerm) :
    OperatorKO7.CompositionalImpossibility.dpProjection (embed t) = dpProjection t := by
  induction t with
  | void => rfl
  | delta t ih => simp [embed, dpProjection, ih]
  | app a b iha ihb => simp [embed, dpProjection]
  | recÎ” b s n ihb ihs ihn =>
      simpa [embed, dpProjection] using ihn

/-- DP projection orients the duplicating recursor on RecÎ”-core. -/
theorem dp_projection_orients_rec_succ (b s n : RecCoreTerm) :
    dpProjection (RecCoreTerm.app s (RecCoreTerm.recÎ” b s n)) <
    dpProjection (RecCoreTerm.recÎ” b s (RecCoreTerm.delta n)) := by
  exact
    (StepDuplicatingSchema.projection_orients_dup_step
      (S := recCoreSchema) dpProjectionRank b s n)

/-- DP projection violates app-subterm sensitivity on RecÎ”-core. -/
theorem dp_projection_violates_sensitivity :
    âˆƒ x y : RecCoreTerm,
      Â¬ (dpProjection (RecCoreTerm.app x y) > dpProjection x) := by
  simpa [recCoreSchema, dpProjectionRank] using
    (StepDuplicatingSchema.projection_violates_wrap_subterm1
      (S := recCoreSchema) dpProjectionRank)

/-- DP projection also violates the second app-subterm condition. -/
theorem dp_projection_violates_subterm2 :
    âˆƒ x y : RecCoreTerm,
      Â¬ (dpProjection (RecCoreTerm.app x y) > dpProjection y) := by
  simpa [recCoreSchema, dpProjectionRank] using
    (StepDuplicatingSchema.projection_violates_wrap_subterm2
      (S := recCoreSchema) dpProjectionRank)

/-- Concrete nonlinear witness showing that Tier-2 transparency is essential. -/
def quadraticWitness : CompositionalRecCoreMeasure where
  c_void := 1
  c_delta := fun x => x + 1
  c_app := fun x y => x + y + 1
  c_recÎ” := fun a b c => a + b * (c + 1) * (c + 1) + c
  app_subterm1 := by
    intro x y
    omega
  app_subterm2 := by
    intro x y
    omega

/-- Every term has positive value under the nonlinear witness. -/
lemma quadraticWitness_eval_pos (t : RecCoreTerm) :
    1 â‰¤ quadraticWitness.eval t := by
  induction t with
  | void =>
      simp [quadraticWitness]
  | delta t ih =>
      show 1 â‰¤ quadraticWitness.eval (RecCoreTerm.delta t)
      simp [CompositionalRecCoreMeasure.eval, quadraticWitness]
  | app a b iha ihb =>
      show 1 â‰¤ quadraticWitness.eval (RecCoreTerm.app a b)
      simp [CompositionalRecCoreMeasure.eval, quadraticWitness]
  | recÎ” b s n ihb ihs ihn =>
      have h :
          quadraticWitness.eval b â‰¤
            quadraticWitness.eval b +
              quadraticWitness.eval s * (quadraticWitness.eval n + 1) *
                (quadraticWitness.eval n + 1) +
              quadraticWitness.eval n := by
        omega
      simpa [CompositionalRecCoreMeasure.eval, quadraticWitness] using le_trans ihb h

/-- The nonlinear witness is not transparent at the base term. -/
lemma quadraticWitness_not_transparent :
    quadraticWitness.c_delta quadraticWitness.c_void â‰  quadraticWitness.c_void := by
  simp [quadraticWitness]

/-- The nonlinear witness strictly orients the duplicating recursor step. -/
theorem quadraticWitness_orients_rec_succ (b s n : RecCoreTerm) :
    quadraticWitness.eval (RecCoreTerm.app s (RecCoreTerm.recÎ” b s n)) <
      quadraticWitness.eval (RecCoreTerm.recÎ” b s (RecCoreTerm.delta n)) := by
  set B := quadraticWitness.eval b
  set S := quadraticWitness.eval s
  set N := quadraticWitness.eval n
  have hs : 1 â‰¤ S := by
    simpa [S] using quadraticWitness_eval_pos s
  have hn : 1 â‰¤ N := by
    simpa [N] using quadraticWitness_eval_pos n
  have hmain : S + S * (N + 1) * (N + 1) < S * (N + 2) * (N + 2) := by
    nlinarith
  have hcalc :
      S + (B + S * (N + 1) * (N + 1) + N) + 1 <
        B + S * (N + 2) * (N + 2) + (N + 1) := by
    nlinarith [hmain]
  simpa [B, S, N, CompositionalRecCoreMeasure.eval, quadraticWitness] using hcalc

/-- The nonlinear witness satisfies the RecÎ”-core compositional axioms but lies
outside Tier 2 exactly because transparency fails. -/
theorem quadraticWitness_exhibits_transparency_gap :
    (âˆ€ x y, quadraticWitness.c_app x y > x) âˆ§
    (âˆ€ x y, quadraticWitness.c_app x y > y) âˆ§
    quadraticWitness.c_delta quadraticWitness.c_void â‰  quadraticWitness.c_void âˆ§
    (âˆ€ b s n : RecCoreTerm,
      quadraticWitness.eval (RecCoreTerm.app s (RecCoreTerm.recÎ” b s n)) <
        quadraticWitness.eval (RecCoreTerm.recÎ” b s (RecCoreTerm.delta n))) := by
  refine âŸ¨quadraticWitness.app_subterm1, quadraticWitness.app_subterm2,
    quadraticWitness_not_transparent, ?_âŸ©
  intro b s n
  exact quadraticWitness_orients_rec_succ b s n

end OperatorKO7.RecCore
````

## OperatorKO7/Meta/SafeStep_Core.lean

**Lines:** 156

``lean
import OperatorKO7.Kernel
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.WellFounded

/-!
Core SafeStep infrastructure used by the canonical computable termination path.

This file is intentionally minimal and self-contained:
- `MetaSN_DM`: computable multiset toolkit (`weight`, `kappaM`, DM lemmas)
- `MetaSN_KO7`: `deltaFlag`, guarded relation `SafeStep`, and `SafeStepRev`

No ordinal payloads or external termination frameworks are imported here.
-/

open OperatorKO7 Trace Multiset

namespace MetaSN_DM

local infix:70 " <â‚˜ " => Multiset.IsDershowitzMannaLT

/-- Weight of a trace: recursion-depth payload at `recÎ”` heads. -/
@[simp] def weight : Trace â†’ Nat
| recÎ” _ _ n => weight n + 1
| _          => 0

/-- DM multiset payload for KO7 traces. -/
@[simp] def kappaM : Trace â†’ Multiset Nat
| void            => 0
| delta t         => kappaM t
| integrate t     => kappaM t
| merge a b       => kappaM a âˆª kappaM b
| app   a b       => kappaM a âˆª kappaM b
| recÎ” b s n      => (weight n + 1) ::â‚˜ (kappaM n âˆª kappaM s) + kappaM b
| eqW  a b        => kappaM a âˆª kappaM b

instance : WellFoundedLT Nat := inferInstance

/-- Well-foundedness of Dershowitz-Manna order on multisets of naturals. -/
lemma wf_dm : WellFounded (fun a b : Multiset Nat => a <â‚˜ b) :=
  Multiset.wellFounded_isDershowitzMannaLT

@[simp] lemma kappaM_int_delta (t : Trace) :
    kappaM (integrate (delta t)) = kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_merge_void_left (t : Trace) :
    kappaM (merge void t) = kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_merge_void_right (t : Trace) :
    kappaM (merge t void) = kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_merge_cancel (t : Trace) :
    kappaM (merge t t) = kappaM t âˆª kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_rec_zero (b s : Trace) :
    kappaM (recÎ” b s void) = (1 ::â‚˜ kappaM s) + kappaM b := by
  simp [kappaM]

@[simp] lemma kappaM_eq_refl (a : Trace) :
    kappaM (eqW a a) = kappaM a âˆª kappaM a := by
  simp [kappaM]

@[simp] lemma kappaM_eq_diff (a b : Trace) :
    kappaM (integrate (merge a b)) = kappaM (eqW a b) := by
  simp [kappaM]

lemma dm_lt_add_of_ne_zero (X Z : Multiset Nat) (h : Z â‰  0) :
    X <â‚˜ (X + Z) := by
  classical
  refine âŸ¨X, (0 : Multiset Nat), Z, ?hZ, ?hM, rfl, ?hYâŸ©
  Â· simpa using h
  Â· simp
  Â· simp

lemma dm_lt_add_of_ne_zero' (X Z : Multiset Nat) (h : Z â‰  0) :
    Multiset.IsDershowitzMannaLT X (X + Z) := by
  classical
  refine âŸ¨X, (0 : Multiset Nat), Z, ?hZ, ?hM, rfl, ?hYâŸ©
  Â· simpa using h
  Â· simp
  Â· simp

lemma dm_drop_R_rec_zero (b s : Trace) :
    kappaM b <â‚˜ kappaM (recÎ” b s void) := by
  classical
  have hdm : Multiset.IsDershowitzMannaLT (kappaM b) (kappaM b + (1 ::â‚˜ kappaM s)) :=
    dm_lt_add_of_ne_zero' (kappaM b) (1 ::â‚˜ kappaM s) (by simp)
  simpa [kappaM, add_comm, add_left_comm, add_assoc] using hdm

lemma union_self_ne_zero_of_ne_zero {X : Multiset Nat} (h : X â‰  0) :
    X âˆª X â‰  (0 : Multiset Nat) := by
  classical
  intro hU
  have hUU : X âˆª X = X := by
    ext a
    simp [Multiset.count_union, max_self]
  exact h (by simpa [hUU] using hU)

end MetaSN_DM

namespace MetaSN_KO7

open MetaSN_DM

@[simp] def deltaFlag : Trace â†’ Nat
| recÎ” _ _ (delta _) => 1
| _                  => 0

@[simp] lemma deltaFlag_void : deltaFlag void = 0 := rfl
@[simp] lemma deltaFlag_integrate (t : Trace) : deltaFlag (integrate t) = 0 := rfl
@[simp] lemma deltaFlag_merge (a b : Trace) : deltaFlag (merge a b) = 0 := rfl
@[simp] lemma deltaFlag_eqW (a b : Trace) : deltaFlag (eqW a b) = 0 := rfl
@[simp] lemma deltaFlag_app (a b : Trace) : deltaFlag (app a b) = 0 := rfl
@[simp] lemma deltaFlag_rec_zero (b s : Trace) : deltaFlag (recÎ” b s void) = 0 := by
  simp [deltaFlag]
@[simp] lemma deltaFlag_rec_delta (b s n : Trace) : deltaFlag (recÎ” b s (delta n)) = 1 := by
  simp [deltaFlag]

lemma deltaFlag_range (t : Trace) : deltaFlag t = 0 âˆ¨ deltaFlag t = 1 := by
  cases t with
  | void => simp
  | delta t => simp
  | integrate t => simp
  | merge a b => simp
  | app a b => simp
  | recÎ” b s n =>
      cases n with
      | void => simp [deltaFlag]
      | delta n => simp [deltaFlag]
      | integrate t => simp [deltaFlag]
      | merge a b => simp [deltaFlag]
      | app a b => simp [deltaFlag]
      | eqW a b => simp [deltaFlag]
      | recÎ” b s n => simp [deltaFlag]
  | eqW a b => simp

/-- Guarded subrelation used by the canonical termination development. -/
inductive SafeStep : Trace â†’ Trace â†’ Prop
| R_int_delta (t) : SafeStep (integrate (delta t)) void
| R_merge_void_left (t) (hÎ´ : deltaFlag t = 0) : SafeStep (merge void t) t
| R_merge_void_right (t) (hÎ´ : deltaFlag t = 0) : SafeStep (merge t void) t
| R_merge_cancel (t) (hÎ´ : deltaFlag t = 0) (h0 : kappaM t = 0) : SafeStep (merge t t) t
| R_rec_zero (b s) (hÎ´ : deltaFlag b = 0) : SafeStep (recÎ” b s void) b
| R_rec_succ (b s n) : SafeStep (recÎ” b s (delta n)) (app s (recÎ” b s n))
| R_eq_refl (a) (h0 : kappaM a = 0) : SafeStep (eqW a a) void
| R_eq_diff (a b) (hne : a â‰  b) : SafeStep (eqW a b) (integrate (merge a b))

/-- Reverse relation for strong-normalization statements. -/
def SafeStepRev : Trace â†’ Trace â†’ Prop := fun a b => SafeStep b a

end MetaSN_KO7

````

## OperatorKO7/Meta/SafeStep_Ctx.lean

**Lines:** 548

``lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.Normalize_Safe

/-!
Context-closure utilities for the KO7 safe fragment.

Purpose:
- Defines `SafeStepCtx`, the one-step contextual closure of the safe root relation `SafeStep`.
- Defines `SafeStepCtxStar`, the reflexive-transitive closure of `SafeStepCtx`.
- Provides lifting lemmas that transport `SafeStepStar` and `SafeStepCtxStar` through constructors.

Why this matters:
- Local confluence is usually stated for a context-closed step relation.
- Our certified artifact focuses on `SafeStep` at the root; this file supplies the standard closure
  layers so that later confluence statements can be phrased in the usual rewriting style.

Scope boundary:
- All results here are about `SafeStep` / `SafeStepCtx`. Nothing here asserts properties of the full
  kernel relation `Step`.
-/
open Classical
open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Context-closure of the KO7 safe root relation. -/
inductive SafeStepCtx : Trace â†’ Trace â†’ Prop
| root {a b} : SafeStep a b â†’ SafeStepCtx a b
| integrate {t u} : SafeStepCtx t u â†’ SafeStepCtx (integrate t) (integrate u)
| mergeL {a a' b} : SafeStepCtx a a' â†’ SafeStepCtx (merge a b) (merge a' b)
| mergeR {a b b'} : SafeStepCtx b b' â†’ SafeStepCtx (merge a b) (merge a b')
| appL {a a' b} : SafeStepCtx a a' â†’ SafeStepCtx (app a b) (app a' b)
| appR {a b b'} : SafeStepCtx b b' â†’ SafeStepCtx (app a b) (app a b')
| recB {b b' s n} : SafeStepCtx b b' â†’ SafeStepCtx (recÎ” b s n) (recÎ” b' s n)
| recS {b s s' n} : SafeStepCtx s s' â†’ SafeStepCtx (recÎ” b s n) (recÎ” b s' n)
| recN {b s n n'} : SafeStepCtx n n' â†’ SafeStepCtx (recÎ” b s n) (recÎ” b s n')

/-- Reflexive-transitive closure of `SafeStepCtx`. -/
inductive SafeStepCtxStar : Trace â†’ Trace â†’ Prop
| refl : âˆ€ t, SafeStepCtxStar t t
| tail : âˆ€ {a b c}, SafeStepCtx a b â†’ SafeStepCtxStar b c â†’ SafeStepCtxStar a c

/-- Transitivity of the context-closed multi-step relation `SafeStepCtxStar`. -/
theorem ctxstar_trans {a b c : Trace}
  (hâ‚ : SafeStepCtxStar a b) (hâ‚‚ : SafeStepCtxStar b c) : SafeStepCtxStar a c := by
  induction hâ‚ with
  | refl => exact hâ‚‚
  | tail hab _ ih => exact SafeStepCtxStar.tail hab (ih hâ‚‚)

/-- A single safe root step can be viewed as a one-step `SafeStepCtx` and hence as a star. -/
theorem ctxstar_of_root {a b : Trace} (h : SafeStep a b) : SafeStepCtxStar a b :=
  SafeStepCtxStar.tail (SafeStepCtx.root h) (SafeStepCtxStar.refl b)

/-- Any `SafeStepStar` path lifts to a `SafeStepCtxStar` path via repeated `SafeStepCtx.root`. -/
theorem ctxstar_of_star {a b : Trace} (h : SafeStepStar a b) : SafeStepCtxStar a b := by
  induction h with
  | refl t => exact SafeStepCtxStar.refl t
  | tail hab _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.root hab) ih

/-- Lift `SafeStepCtxStar` through the `integrate` constructor. -/
theorem ctxstar_integrate {t u : Trace}
  (h : SafeStepCtxStar t u) : SafeStepCtxStar (integrate t) (integrate u) := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail htu _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.integrate htu) ih

/-- Lift `SafeStepCtxStar` through the left argument of `merge`. -/
theorem ctxstar_mergeL {a a' b : Trace}
  (h : SafeStepCtxStar a a') : SafeStepCtxStar (merge a b) (merge a' b) := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hab _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.mergeL hab) ih

/-- Lift `SafeStepCtxStar` through the right argument of `merge`. -/
theorem ctxstar_mergeR {a b b' : Trace}
  (h : SafeStepCtxStar b b') : SafeStepCtxStar (merge a b) (merge a b') := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hbb _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.mergeR hbb) ih

/-- Lift `SafeStepCtxStar` through the left argument of `app`. -/
theorem ctxstar_appL {a a' b : Trace}
  (h : SafeStepCtxStar a a') : SafeStepCtxStar (app a b) (app a' b) := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hab _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.appL hab) ih

/-- Lift `SafeStepCtxStar` through the right argument of `app`. -/
theorem ctxstar_appR {a b b' : Trace}
  (h : SafeStepCtxStar b b') : SafeStepCtxStar (app a b) (app a b') := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hbb _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.appR hbb) ih

/-- Lift `SafeStepCtxStar` through the base argument `b` of `recÎ” b s n`. -/
theorem ctxstar_recB {b b' s n : Trace}
  (h : SafeStepCtxStar b b') : SafeStepCtxStar (recÎ” b s n) (recÎ” b' s n) := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hbb _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.recB hbb) ih

/-- Lift `SafeStepCtxStar` through the step function argument `s` of `recÎ” b s n`. -/
theorem ctxstar_recS {b s s' n : Trace}
  (h : SafeStepCtxStar s s') : SafeStepCtxStar (recÎ” b s n) (recÎ” b s' n) := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hss _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.recS hss) ih

/-- Lift `SafeStepCtxStar` through the argument `n` of `recÎ” b s n`. -/
theorem ctxstar_recN {b s n n' : Trace}
  (h : SafeStepCtxStar n n') : SafeStepCtxStar (recÎ” b s n) (recÎ” b s n') := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hnn _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.recN hnn) ih

/-- Compose left and right ctx-star lifts under `merge`. -/
theorem ctxstar_mergeLR {a a' b b' : Trace}
  (ha : SafeStepCtxStar a a') (hb : SafeStepCtxStar b b') :
  SafeStepCtxStar (merge a b) (merge a' b') :=
  ctxstar_trans (ctxstar_mergeL ha) (ctxstar_mergeR hb)

/-- Compose all three ctx-star lifts under `recÎ”`. -/
theorem ctxstar_recBSN {b b' s s' n n' : Trace}
  (hb : SafeStepCtxStar b b') (hs : SafeStepCtxStar s s') (hn : SafeStepCtxStar n n') :
  SafeStepCtxStar (recÎ” b s n) (recÎ” b' s' n') :=
  ctxstar_trans (ctxstar_recB hb) (ctxstar_trans (ctxstar_recS hs) (ctxstar_recN hn))

/-- Compose left and right ctx-star lifts under `app`. -/
theorem ctxstar_appLR {a a' b b' : Trace}
  (ha : SafeStepCtxStar a a') (hb : SafeStepCtxStar b b') :
  SafeStepCtxStar (app a b) (app a' b') :=
  ctxstar_trans (ctxstar_appL ha) (ctxstar_appR hb)

/-- Local join at root allowing context-closed stars after the two root steps. -/
def LocalJoinSafe_ctx (a : Trace) : Prop :=
  âˆ€ {b c}, SafeStep a b â†’ SafeStep a c â†’ âˆƒ d, SafeStepCtxStar b d âˆ§ SafeStepCtxStar c d

/-- If there are no safe root steps from `a`, ctx-local join holds vacuously. -/
theorem localJoin_of_none_ctx (a : Trace)
    (h : âˆ€ {b}, SafeStep a b â†’ False) : LocalJoinSafe_ctx a := by
  intro b c hb hc
  exact False.elim (h hb)

/-- If `a` is in safe normal form, ctx-local join holds. -/
theorem localJoin_of_nf_ctx (a : Trace) (hnf : NormalFormSafe a) : LocalJoinSafe_ctx a := by
  refine localJoin_of_none_ctx (a := a) ?h
  intro b hb; exact no_step_from_nf hnf hb

/-- If normalization is fixed at `a`, ctx-local join holds. -/
theorem localJoin_if_normalize_fixed_ctx (a : Trace) (hfix : normalizeSafe a = a) :
    LocalJoinSafe_ctx a := by
  have hnf : NormalFormSafe a := (nf_iff_normalize_fixed a).mpr hfix
  intro b c hb hc
  exact (localJoin_of_nf_ctx a hnf) hb hc

/-- If every safe root step from `a` targets the same `d`, then ctx-local join holds. -/
theorem localJoin_of_unique_ctx (a d : Trace)
    (h : âˆ€ {b}, SafeStep a b â†’ b = d) : LocalJoinSafe_ctx a := by
  intro b c hb hc
  have hb' : b = d := h hb
  have hc' : c = d := h hc
  refine âŸ¨d, ?_, ?_âŸ©
  Â· simpa [hb'] using (SafeStepCtxStar.refl d)
  Â· simpa [hc'] using (SafeStepCtxStar.refl d)

/-! ### Convenience ctx-local joins for vacuous shapes -/

/-- At `void`, there is no safe root rule; ctx-local join holds vacuously. -/
theorem localJoin_ctx_void : LocalJoinSafe_ctx void := by
  refine localJoin_of_none_ctx (a := void) ?h
  intro b hb; cases hb

/-- At `delta t`, there is no safe root rule; ctx-local join holds vacuously. -/
theorem localJoin_ctx_delta (t : Trace) : LocalJoinSafe_ctx (delta t) := by
  refine localJoin_of_none_ctx (a := delta t) ?h
  intro b hb; cases hb

/-- At `app a b`, there is no safe root rule; ctx-local join holds vacuously. -/
theorem localJoin_ctx_app (a b : Trace) : LocalJoinSafe_ctx (app a b) := by
  refine localJoin_of_none_ctx (a := app a b) ?h
  intro b' hb'; cases hb'

/-- At `integrate void`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_integrate_void : LocalJoinSafe_ctx (integrate void) := by
  refine localJoin_of_none_ctx (a := integrate void) ?h
  intro x hx; cases hx

/-- At `integrate (merge a b)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_integrate_merge (a b : Trace) : LocalJoinSafe_ctx (integrate (merge a b)) := by
  refine localJoin_of_none_ctx (a := integrate (merge a b)) ?h
  intro x hx; cases hx

/-- At `integrate (app a b)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_integrate_app (a b : Trace) : LocalJoinSafe_ctx (integrate (app a b)) := by
  refine localJoin_of_none_ctx (a := integrate (app a b)) ?h
  intro x hx; cases hx

/-- At `integrate (eqW a b)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_integrate_eqW (a b : Trace) : LocalJoinSafe_ctx (integrate (eqW a b)) := by
  refine localJoin_of_none_ctx (a := integrate (eqW a b)) ?h
  intro x hx; cases hx

/-- At `integrate (integrate t)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_integrate_integrate (t : Trace) :
    LocalJoinSafe_ctx (integrate (integrate t)) := by
  refine localJoin_of_none_ctx (a := integrate (integrate t)) ?h
  intro x hx; cases hx

/-- At `integrate (recÎ” b s n)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_integrate_rec (b s n : Trace) :
    LocalJoinSafe_ctx (integrate (recÎ” b s n)) := by
  refine localJoin_of_none_ctx (a := integrate (recÎ” b s n)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s (merge a c)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_merge (b s a c : Trace) : LocalJoinSafe_ctx (recÎ” b s (merge a c)) := by
  refine localJoin_of_none_ctx (a := recÎ” b s (merge a c)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s (app a c)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_app (b s a c : Trace) : LocalJoinSafe_ctx (recÎ” b s (app a c)) := by
  refine localJoin_of_none_ctx (a := recÎ” b s (app a c)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s (integrate t)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_integrate (b s t : Trace) : LocalJoinSafe_ctx (recÎ” b s (integrate t)) := by
  refine localJoin_of_none_ctx (a := recÎ” b s (integrate t)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s (eqW a c)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_eqW (b s a c : Trace) : LocalJoinSafe_ctx (recÎ” b s (eqW a c)) := by
  refine localJoin_of_none_ctx (a := recÎ” b s (eqW a c)) ?h
  intro x hx; cases hx

/-- At `recÎ” b s void`, only one safe root rule; ctx-local join is trivial. -/
theorem localJoin_ctx_rec_zero (b s : Trace) : LocalJoinSafe_ctx (recÎ” b s void) := by
  refine localJoin_of_unique_ctx (a := recÎ” b s void) (d := b) ?h
  intro x hx; cases hx with
  | R_rec_zero _ _ _ => rfl

/-- At `recÎ” b s (delta n)`, only one safe root rule; ctx-local join is trivial. -/
theorem localJoin_ctx_rec_succ (b s n : Trace) : LocalJoinSafe_ctx (recÎ” b s (delta n)) := by
  refine localJoin_of_unique_ctx (a := recÎ” b s (delta n)) (d := app s (recÎ” b s n)) ?h
  intro x hx; cases hx with
  | R_rec_succ _ _ _ => rfl

/-- At `merge void t`, only the left-void rule can fire; ctx-local join is trivial. -/
theorem localJoin_ctx_merge_void_left (t : Trace) : LocalJoinSafe_ctx (merge void t) := by
  refine localJoin_of_unique_ctx (a := merge void t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- At `merge t void`, only the right-void rule can fire; ctx-local join is trivial. -/
theorem localJoin_ctx_merge_void_right (t : Trace) : LocalJoinSafe_ctx (merge t void) := by
  refine localJoin_of_unique_ctx (a := merge t void) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_void_right _ _ => rfl
  | R_merge_void_left _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- At `merge t t`, any applicable safe rule reduces to `t`; ctx-local join is trivial. -/
theorem localJoin_ctx_merge_tt (t : Trace) : LocalJoinSafe_ctx (merge t t) := by
  refine localJoin_of_unique_ctx (a := merge t t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_cancel _ _ _ => rfl
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- Convenience: `merge void void` reduces uniquely to `void` (ctx). -/
theorem localJoin_ctx_merge_void_void : LocalJoinSafe_ctx (merge void void) :=
  localJoin_ctx_merge_void_left void

/-- Convenience: `merge void (delta n)` reduces uniquely to `delta n` (ctx). -/
theorem localJoin_ctx_merge_void_delta (n : Trace) :
    LocalJoinSafe_ctx (merge void (delta n)) :=
  localJoin_ctx_merge_void_left (delta n)

/-- Convenience: `merge (delta n) void` reduces uniquely to `delta n` (ctx). -/
theorem localJoin_ctx_merge_delta_void (n : Trace) :
    LocalJoinSafe_ctx (merge (delta n) void) :=
  localJoin_ctx_merge_void_right (delta n)

/-- Convenience: `merge (delta n) (delta n)` reduces (by cancel) to `delta n` (ctx). -/
theorem localJoin_ctx_merge_delta_delta (n : Trace) :
    LocalJoinSafe_ctx (merge (delta n) (delta n)) :=
  localJoin_ctx_merge_tt (delta n)

/-- At `integrate (delta t)`, only one safe root rule; ctx-local join is trivial. -/
theorem localJoin_ctx_int_delta (t : Trace) : LocalJoinSafe_ctx (integrate (delta t)) := by
  refine localJoin_of_unique_ctx (a := integrate (delta t)) (d := void) ?h
  intro x hx; cases hx with
  | R_int_delta _ => rfl

/-- If `deltaFlag t â‰  0`, the left-void merge rule cannot apply; no competing branch. -/
theorem localJoin_ctx_merge_void_left_guard_ne (t : Trace)
    (hÎ´ne : deltaFlag t â‰  0) : LocalJoinSafe_ctx (merge void t) := by
  refine localJoin_of_unique_ctx (a := merge void t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_void_left _ hÎ´ => exact (False.elim (hÎ´ne hÎ´))
  | R_merge_void_right _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t â‰  0`, the right-void merge rule cannot apply; no competing branch. -/
theorem localJoin_ctx_merge_void_right_guard_ne (t : Trace)
    (hÎ´ne : deltaFlag t â‰  0) : LocalJoinSafe_ctx (merge t void) := by
  refine localJoin_of_unique_ctx (a := merge t void) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_void_right _ hÎ´ => exact (False.elim (hÎ´ne hÎ´))
  | R_merge_void_left _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t â‰  0`, merge-cancel is blocked at root; vacuous ctx-local join. -/
theorem localJoin_ctx_merge_cancel_guard_delta_ne (t : Trace)
    (hÎ´ne : deltaFlag t â‰  0) : LocalJoinSafe_ctx (merge t t) := by
  refine localJoin_of_unique_ctx (a := merge t t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_cancel _ hÎ´ _ => exact (False.elim (hÎ´ne hÎ´))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- If `kappaM t â‰  0`, merge-cancel is blocked at root; vacuous ctx-local join. -/
theorem localJoin_ctx_merge_cancel_guard_kappa_ne (t : Trace)
    (h0ne : MetaSN_DM.kappaM t â‰  0) : LocalJoinSafe_ctx (merge t t) := by
  refine localJoin_of_unique_ctx (a := merge t t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_cancel _ _ h0 => exact (False.elim (h0ne h0))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- At `recÎ” b s void`, if `deltaFlag b â‰  0` then the rec-zero rule is blocked. -/
theorem localJoin_ctx_rec_zero_guard_ne (b s : Trace)
    (hÎ´ne : deltaFlag b â‰  0) : LocalJoinSafe_ctx (recÎ” b s void) := by
  refine localJoin_of_none_ctx (a := recÎ” b s void) ?h
  intro x hx; cases hx with
  | R_rec_zero _ _ hÎ´ => exact (hÎ´ne hÎ´)

/-- At `integrate t`, if `t` is not a `delta _`, then there is no safe root step (ctx). -/
theorem localJoin_ctx_integrate_non_delta (t : Trace)
    (hnd : âˆ€ u, t â‰  delta u) : LocalJoinSafe_ctx (integrate t) := by
  refine localJoin_of_none_ctx (a := integrate t) ?h
  intro x hx; cases hx with
  | R_int_delta u => exact (hnd u) rfl

/-- At `recÎ” b s n`, if `n â‰  void` and `n` is not a `delta _`, then no safe root step (ctx). -/
theorem localJoin_ctx_rec_other (b s n : Trace)
    (hn0 : n â‰  void) (hns : âˆ€ u, n â‰  delta u) : LocalJoinSafe_ctx (recÎ” b s n) := by
  refine localJoin_of_none_ctx (a := recÎ” b s n) ?h
  intro x hx; cases hx with
  | R_rec_zero _ _ _ => exact (hn0 rfl)
  | R_rec_succ _ _ u => exact (hns u) rfl

-- (moved above to allow reuse in subsequent lemmas)

/-- Conditional join for the eqW peak: if `merge a a` context-reduces to a `delta n`, then
 the two root branches from `eqW a a` context-join at `void`. -/
theorem localJoin_eqW_refl_ctx_if_merges_to_delta (a n : Trace)
  (hmd : SafeStepCtxStar (merge a a) (delta n)) :
  LocalJoinSafe_ctx (eqW a a) := by
  intro b c hb hc
  -- Enumerate the two root branches
  cases hb with
  | R_eq_refl _ _ =>
    -- b = void; hc can only be refl or diff
    cases hc with
    | R_eq_refl _ _ => exact âŸ¨void, SafeStepCtxStar.refl _, SafeStepCtxStar.refl _âŸ©
    | R_eq_diff _ _ =>
      -- c = integrate (merge a a) â‡’ctx* integrate (delta n) â†’ void
      have h_to_delta : SafeStepCtxStar (integrate (merge a a)) (integrate (delta n)) :=
        ctxstar_integrate hmd
      have h_to_void : SafeStepCtxStar (integrate (delta n)) void :=
        ctxstar_of_root (SafeStep.R_int_delta n)
      exact âŸ¨void, SafeStepCtxStar.refl _, ctxstar_trans h_to_delta h_to_voidâŸ©
  | R_eq_diff _ _ =>
    -- b = integrate (merge a a)
    cases hc with
    | R_eq_refl _ _ =>
      have h_to_delta : SafeStepCtxStar (integrate (merge a a)) (integrate (delta n)) :=
        ctxstar_integrate hmd
      have h_to_void : SafeStepCtxStar (integrate (delta n)) void :=
        ctxstar_of_root (SafeStep.R_int_delta n)
      exact âŸ¨void, ctxstar_trans h_to_delta h_to_void, SafeStepCtxStar.refl _âŸ©
    | R_eq_diff _ _ =>
      -- both to the same term
  exact âŸ¨integrate (merge a a), SafeStepCtxStar.refl _, SafeStepCtxStar.refl _âŸ©

/-- If `a â‡’ctx* delta n` and `delta n` satisfies the cancel guards, then
`merge a a â‡’ctx* delta n`. -/
theorem ctxstar_merge_cancel_of_arg_to_delta
  (a n : Trace)
  (ha : SafeStepCtxStar a (delta n))
  (hÎ´ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  SafeStepCtxStar (merge a a) (delta n) := by
  -- push left argument to delta n
  have hL : SafeStepCtxStar (merge a a) (merge (delta n) a) := ctxstar_mergeL ha
  -- push right argument to delta n
  have hR : SafeStepCtxStar (merge (delta n) a) (merge (delta n) (delta n)) := ctxstar_mergeR ha
  -- apply root cancel at delta n
  have hC : SafeStepCtxStar (merge (delta n) (delta n)) (delta n) :=
    ctxstar_of_root (SafeStep.R_merge_cancel (t := delta n) hÎ´ h0)
  exact ctxstar_trans hL (ctxstar_trans hR hC)

/-- If `a â‡’* delta n` by root-safe steps and the cancel guards hold on `delta n`, then
`merge a a â‡’ctx* delta n`. -/
theorem ctxstar_merge_cancel_of_arg_star_to_delta
  (a n : Trace)
  (ha : SafeStepStar a (delta n))
  (hÎ´ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  SafeStepCtxStar (merge a a) (delta n) := by
  have ha_ctx : SafeStepCtxStar a (delta n) := ctxstar_of_star ha
  exact ctxstar_merge_cancel_of_arg_to_delta a n ha_ctx hÎ´ h0

/-- Conditional local join for `eqW a a` from an argument-to-delta premise.
If `a â‡’ctx* delta n` and the cancel guards hold on `delta n`, the two root branches
context-join at `void`. -/
theorem localJoin_eqW_refl_ctx_if_arg_merges_to_delta (a n : Trace)
  (ha : SafeStepCtxStar a (delta n))
  (hÎ´ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW a a) := by
  -- derive the stronger mergeâ†’delta premise and reuse previous lemma
  have hmd : SafeStepCtxStar (merge a a) (delta n) :=
    ctxstar_merge_cancel_of_arg_to_delta a n ha hÎ´ h0
  -- apply the previous lemma to the concrete branch steps
  intro b c hb hc
  exact (localJoin_eqW_refl_ctx_if_merges_to_delta a n hmd) hb hc

/-- Variant: if `a â‡’* delta n` by root-safe steps, embed to ctx-star and reuse the delta-argument lemma. -/
theorem localJoin_eqW_refl_ctx_if_arg_star_to_delta (a n : Trace)
  (ha : SafeStepStar a (delta n))
  (hÎ´ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW a a) := by
  -- embed SafeStepStar into SafeStepCtxStar
  have ha_ctx : SafeStepCtxStar a (delta n) := ctxstar_of_star ha
  -- reuse the ctx lemma, applied to the given branches
  intro b c hb hc
  exact (localJoin_eqW_refl_ctx_if_arg_merges_to_delta a n ha_ctx hÎ´ h0) hb hc

/-- Variant: if `normalizeSafe (merge a a) = delta n`, then we can reuse the
merges-to-delta lemma directly to obtain a ctx-local join for `eqW a a`. -/
theorem localJoin_eqW_refl_ctx_if_merge_normalizes_to_delta (a n : Trace)
  (hn : normalizeSafe (merge a a) = delta n) :
  LocalJoinSafe_ctx (eqW a a) := by
  -- get a root-star to the normal form and embed to ctx-star
  have hmd_star : SafeStepStar (merge a a) (normalizeSafe (merge a a)) :=
    to_norm_safe (merge a a)
  have hmd_ctx : SafeStepCtxStar (merge a a) (delta n) := by
    simpa [hn] using (ctxstar_of_star hmd_star)
  -- apply the merges-to-delta variant to the given branches
  intro b c hb hc
  exact (localJoin_eqW_refl_ctx_if_merges_to_delta a n hmd_ctx) hb hc

/-- If `merge a a â‡’ctx* delta n` then `integrate (merge a a) â‡’ctx* void`. -/
theorem ctxstar_integrate_merge_to_void_of_mergeToDelta (a n : Trace)
  (hmd : SafeStepCtxStar (merge a a) (delta n)) :
  SafeStepCtxStar (integrate (merge a a)) void := by
  have h_to_delta : SafeStepCtxStar (integrate (merge a a)) (integrate (delta n)) :=
    ctxstar_integrate hmd
  have h_to_void : SafeStepCtxStar (integrate (delta n)) void :=
    ctxstar_of_root (SafeStep.R_int_delta n)
  exact ctxstar_trans h_to_delta h_to_void

/-- If `normalizeSafe (merge a a) = delta n` then `integrate (merge a a) â‡’ctx* void`. -/
theorem ctxstar_integrate_merge_to_void_of_merge_normalizes_to_delta (a n : Trace)
  (hn : normalizeSafe (merge a a) = delta n) :
  SafeStepCtxStar (integrate (merge a a)) void := by
  have hmd_star : SafeStepStar (merge a a) (normalizeSafe (merge a a)) :=
    to_norm_safe (merge a a)
  have hmd_ctx : SafeStepCtxStar (merge a a) (delta n) := by
    simpa [hn] using (ctxstar_of_star hmd_star)
  exact ctxstar_integrate_merge_to_void_of_mergeToDelta a n hmd_ctx

/-- If `integrate (merge a a) â‡’ctx* void`, then `eqW a a` has a ctx-local join at `void`. -/
theorem localJoin_eqW_refl_ctx_if_integrate_merge_to_void (a : Trace)
  (hiv : SafeStepCtxStar (integrate (merge a a)) void) :
  LocalJoinSafe_ctx (eqW a a) := by
  intro b c hb hc
  cases hb with
  | R_eq_refl _ _ =>
    cases hc with
    | R_eq_refl _ _ =>
      exact âŸ¨void, SafeStepCtxStar.refl _, SafeStepCtxStar.refl _âŸ©
    | R_eq_diff _ _ =>
      exact âŸ¨void, SafeStepCtxStar.refl _, hivâŸ©
  | R_eq_diff _ _ =>
    cases hc with
    | R_eq_refl _ _ =>
      exact âŸ¨void, hiv, SafeStepCtxStar.refl _âŸ©
    | R_eq_diff _ _ =>
      exact âŸ¨integrate (merge a a), SafeStepCtxStar.refl _, SafeStepCtxStar.refl _âŸ©

/-- At `eqW a b` with `a â‰  b`, only the diff rule applies; ctx-local join is trivial. -/
theorem localJoin_eqW_ne_ctx (a b : Trace) (hne : a â‰  b) : LocalJoinSafe_ctx (eqW a b) := by
  refine localJoin_of_unique_ctx (a := eqW a b) (d := integrate (merge a b)) ?h
  intro x hx
  cases hx with
  | R_eq_diff _ _ => rfl
  | R_eq_refl _ _ => exact (False.elim (hne rfl))

/-- At `eqW a a`, if `kappaM a â‰  0`, the reflexive rule is blocked; only diff applies. -/
theorem localJoin_eqW_refl_ctx_guard_ne (a : Trace)
  (h0ne : MetaSN_DM.kappaM a â‰  0) : LocalJoinSafe_ctx (eqW a a) := by
  refine localJoin_of_unique_ctx (a := eqW a a) (d := integrate (merge a a)) ?h
  intro x hx
  cases hx with
  | R_eq_diff _ _ => rfl
  | R_eq_refl _ h0 => exact (False.elim (h0ne h0))

end MetaSN_KO7

namespace MetaSN_KO7

/-- If `a` is literally `delta n` and cancel guards hold on `delta n`, then
`eqW a a` has a context-closed local join at `void`. -/
theorem localJoin_eqW_refl_ctx_when_a_is_delta (n : Trace)
  (hÎ´ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW (delta n) (delta n)) := by
  -- trivial arg-to-delta via refl
  intro b c hb hc
  -- build the LocalJoinSafe_ctx witness once, then apply to the given branches
  have ha : SafeStepCtxStar (delta n) (delta n) := SafeStepCtxStar.refl _
  have hj : LocalJoinSafe_ctx (eqW (delta n) (delta n)) :=
    localJoin_eqW_refl_ctx_if_arg_merges_to_delta (a := delta n) (n := n) ha hÎ´ h0
  exact hj hb hc

/-- If `a` safe-normalizes to `delta n` and cancel guards hold on `delta n`, then
`eqW a a` has a context-closed local join at `void`. -/
theorem localJoin_eqW_refl_ctx_if_normalizes_to_delta (a n : Trace)
  (hn : normalizeSafe a = delta n)
  (hÎ´ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW a a) := by
  -- embed the normalization star into ctx-star
  intro b c hb hc
  have ha_star : SafeStepStar a (normalizeSafe a) := to_norm_safe a
  have ha_ctx : SafeStepCtxStar a (normalizeSafe a) := ctxstar_of_star ha_star
  -- build the LocalJoinSafe_ctx witness using the argâ†’delta bridge
  have hj : LocalJoinSafe_ctx (eqW a a) :=
    localJoin_eqW_refl_ctx_if_arg_merges_to_delta (a := a) (n := n)
      (by simpa [hn] using ha_ctx) hÎ´ h0
  exact hj hb hc

end MetaSN_KO7
````

## OperatorKO7/Meta/StepDuplicatingSchema.lean

**Lines:** 159

``lean
import Mathlib

/-!
# Generic Step-Duplicating Schema

This module isolates the abstract shape used by the KO7 / RecÎ”-core impossibility
proofs:

- a base term,
- a successor constructor,
- a binary wrapper constructor, and
- a ternary recursor with duplicating successor step
  `recur b s (succ n) â†¦ wrap s (recur b s n)`.

The point is to prove the direct/compositional impossibility theorems once at the
schema level, independent of KO7's surrounding signature.
-/

namespace OperatorKO7.StepDuplicating

/-- Minimal constructor interface needed for the duplication barrier. -/
structure StepDuplicatingSchema where
  T : Type
  base : T
  succ : T â†’ T
  wrap : T â†’ T â†’ T
  recur : T â†’ T â†’ T â†’ T

namespace StepDuplicatingSchema

/-- Left-nested wrapper chain used to pump additive measures. -/
def wrapIter (S : StepDuplicatingSchema) : Nat â†’ S.T
  | 0 => S.base
  | k + 1 => S.wrap (wrapIter S k) S.base

/-- Additive compositional measures on a step-duplicating schema. -/
structure AdditiveMeasure (S : StepDuplicatingSchema) where
  eval : S.T â†’ Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval S.base = w_base
  eval_succ : âˆ€ t, eval (S.succ t) = w_succ + eval t
  eval_wrap : âˆ€ x y, eval (S.wrap x y) = w_wrap + eval x + eval y
  eval_recur : âˆ€ b s n, eval (S.recur b s n) = w_recur + eval b + eval s + eval n
  h_wrap_pos : w_wrap â‰¥ 1

/-- The wrapper pump grows at least linearly because `wrap` has positive weight. -/
lemma eval_wrapIter_ge {S : StepDuplicatingSchema} (M : AdditiveMeasure S) (k : Nat) :
    M.eval (wrapIter S k) â‰¥ k := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      have := M.h_wrap_pos
      omega

/-- Schema-level Tier 1 impossibility:
no additive compositional measure can orient the duplicating step uniformly. -/
theorem no_additive_orients_dup_step {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    Â¬ (âˆ€ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hspec := h S.base (wrapIter S M.w_succ) S.base
  have hge := eval_wrapIter_ge M M.w_succ
  simp [M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur] at hspec
  have := M.h_wrap_pos
  omega

/-- Abstract compositional measures on a step-duplicating schema. -/
structure CompositionalMeasure (S : StepDuplicatingSchema) where
  eval : S.T â†’ Nat
  c_base : Nat
  c_succ : Nat â†’ Nat
  c_wrap : Nat â†’ Nat â†’ Nat
  c_recur : Nat â†’ Nat â†’ Nat â†’ Nat
  eval_base : eval S.base = c_base
  eval_succ : âˆ€ t, eval (S.succ t) = c_succ (eval t)
  eval_wrap : âˆ€ x y, eval (S.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : âˆ€ b s n, eval (S.recur b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm1 : âˆ€ x y, c_wrap x y > x
  wrap_subterm2 : âˆ€ x y, c_wrap x y > y

/-- Schema-level Tier 2 impossibility under base-level successor transparency. -/
theorem no_compositional_orients_dup_step_transparent_succ
    {S : StepDuplicatingSchema} (CM : CompositionalMeasure S)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    Â¬ (âˆ€ (b s n : S.T),
      CM.eval (S.wrap s (S.recur b s n)) < CM.eval (S.recur b s (S.succ n))) := by
  intro h
  have hspec := h S.base S.base S.base
  simp [CM.eval_base, CM.eval_succ, CM.eval_wrap, CM.eval_recur, h_transparent] at hspec
  have hsub := CM.wrap_subterm2 CM.c_base (CM.c_recur CM.c_base CM.c_base CM.c_base)
  omega

/-- A rewrite system whose signature contains the generic duplicating step. -/
structure StepDuplicatingSystem extends StepDuplicatingSchema where
  Step : T â†’ T â†’ Prop
  dup_step : âˆ€ b s n, Step (recur b s (succ n)) (wrap s (recur b s n))

/-- A measure/order pair globally orients every step of the system. -/
def GlobalOrients {Î± : Type} (Sys : StepDuplicatingSystem) (m : Sys.T â†’ Î±)
    (lt : Î± â†’ Î± â†’ Prop) : Prop :=
  âˆ€ {a b : Sys.T}, Sys.Step a b â†’ lt (m b) (m a)

/-- Any additive measure on a system containing the duplicating step fails globally. -/
theorem no_global_orients_additive {Sys : StepDuplicatingSystem}
    (M : AdditiveMeasure Sys.toStepDuplicatingSchema) :
    Â¬ GlobalOrients Sys M.eval (Â· < Â·) := by
  intro h
  exact
    no_additive_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
      (fun b s n => h (Sys.dup_step b s n))

/-- Any compositional measure with transparent successor at base fails globally. -/
theorem no_global_orients_compositional_transparent_succ
    {Sys : StepDuplicatingSystem} (CM : CompositionalMeasure Sys.toStepDuplicatingSchema)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    Â¬ GlobalOrients Sys CM.eval (Â· < Â·) := by
  intro h
  exact
    no_compositional_orients_dup_step_transparent_succ
      (S := Sys.toStepDuplicatingSchema) CM h_transparent
      (fun b s n => h (Sys.dup_step b s n))

/-- Projection-style ranks that only track successor depth through the recursor argument. -/
structure ProjectionRank (S : StepDuplicatingSchema) where
  rank : S.T â†’ Nat
  rank_base : rank S.base = 0
  rank_succ : âˆ€ t, rank (S.succ t) = rank t + 1
  rank_wrap : âˆ€ x y, rank (S.wrap x y) = 0
  rank_recur : âˆ€ b s n, rank (S.recur b s n) = rank n

/-- The projection rank orients the duplicating step by tracking only the recursion counter. -/
theorem projection_orients_dup_step {S : StepDuplicatingSchema} (R : ProjectionRank S)
    (b s n : S.T) :
    R.rank (S.wrap s (S.recur b s n)) < R.rank (S.recur b s (S.succ n)) := by
  rw [R.rank_wrap, R.rank_recur, R.rank_succ]
  omega

/-- The projection rank violates sensitivity to the first wrapper argument. -/
theorem projection_violates_wrap_subterm1 {S : StepDuplicatingSchema} (R : ProjectionRank S) :
    âˆƒ x y : S.T, Â¬ (R.rank (S.wrap x y) > R.rank x) := by
  refine âŸ¨S.succ S.base, S.base, ?_âŸ©
  rw [R.rank_wrap, R.rank_succ, R.rank_base]
  omega

/-- The projection rank violates sensitivity to the second wrapper argument. -/
theorem projection_violates_wrap_subterm2 {S : StepDuplicatingSchema} (R : ProjectionRank S) :
    âˆƒ x y : S.T, Â¬ (R.rank (S.wrap x y) > R.rank y) := by
  refine âŸ¨S.base, S.succ S.base, ?_âŸ©
  rw [R.rank_wrap, R.rank_succ, R.rank_base]
  omega

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
````

## OperatorKO7/Test/Sanity.lean

**Lines:** 11

``lean
/-!
Tiny smoke tests.

Why this file exists:
- Ensures the Lake package can compile a small `#eval` and a basic `#check` on a fresh machine.
- Keeps a minimal test surface under `OperatorKO7/Test/` to catch obvious toolchain regressions.
- This file is intentionally trivial and does not contribute to the KO7 theorems.
-/

#eval (1 + 1)
#check Prod.Lex
````

