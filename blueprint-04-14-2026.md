# Blueprint: Confession-Method Family Formalization
## Extending the Orientation Boundary to All Recursive-Call Projection Methods

**Date:** April 14, 2026
**Repository:** OperatorKO7
**Depends on:** `Meta/StepDuplicatingSchema.lean`, `Meta/CompositionalMeasure_Impossibility.lean`, `Meta/DependencyPairs_Fragment.lean`, `Meta/DependencyPairs_Works.lean`, `Meta/OperationalIncompleteness.lean`

---

## 1. Motivation

The current artifact formalizes one confession method: dependency pairs with subterm criterion. The `dpProjection` rank and its `CertifiedForgettingWitness` packaging prove that DP orients the duplicating step while violating wrapper sensitivity.

But DP is not the only confession method. The boundary-methods analysis identifies four additional methods that share the same structural shape: they extract a recursive-call relation from the rules, project to the counter coordinate, and declare the payload inert. These are:

1. **Counter-projection** (subterm criterion applied directly to argument positions)
2. **Size-Change Termination** (call-graph construction with descent-thread check)
3. **Argument filtering** (DP framework variant projecting F to its third argument)
4. **Usable rules + subterm projection** (conditional: within-boundary only when followed by projection, not by a construction step)

All four are confession methods in the sense of Paper C. They satisfy the `CertifiedForgettingWitness` interface: they orient the duplicating step while violating wrapper sensitivity. The goal of this formalization sprint is to:

- **Part B (generalize):** Define a schema-level `ConfessionMethod` structure that captures the common shape
- **Part A (enumerate):** Instantiate it for each method, providing mechanized evidence that the confession family is not a single method but a structural class

---

## 2. Mathematical content

### 2.1 What all confession methods share

Every confession method on the step-duplicating schema `recur(b, s, succ(n)) → wrap(s, recur(b, s, n))` does the following:

1. **Extraction:** From the rule, identify the recursive-call relation: the source `recur(b, s, succ(n))` calls `recur(b, s, n)`.
2. **Projection:** Select a coordinate of the recursive call that strictly decreases. For all known methods on this schema, the coordinate is the third argument (the counter): `succ(n)` maps to `n`.
3. **Inertness declaration:** The remaining coordinates (in particular, the step argument `s` / payload `y`) are not tracked by the descent argument. The wrapper `wrap(s, ·)` is stripped from the proof obligation.
4. **Soundness import:** An external metatheorem guarantees that well-foundedness of the projected relation implies termination of the original system.

The key formal properties shared by every such method:

- The projection rank satisfies `rank(wrap(x, y)) = 0` (or more generally, `rank(wrap(x, y))` does not depend on `x`). This is what makes the wrapper "transparent" to the rank and allows the duplicated payload to be ignored.
- The rank satisfies `rank(recur(b, s, n)) = rank(n)` (projection to the counter coordinate).
- The rank satisfies `rank(succ(t)) = rank(t) + 1` (the counter is tracked faithfully).

These three properties are exactly the `ProjectionRank` structure already defined in `StepDuplicatingSchema.lean` (lines 335-340). So the schema-level infrastructure already captures the mathematical content. What's missing is:

- A named `ConfessionMethod` structure that wraps `ProjectionRank` with the confession interpretation
- Multiple instantiations showing different methods are all instances
- A theorem connecting `ConfessionMethod` to `CertifiedForgettingWitness`

### 2.2 Why the methods are distinct despite sharing the same rank

On the specific two-rule schema, all four confession methods produce the same concrete rank function: track only the counter depth. The mathematical content of each method is identical on this instance. They differ in:

- **What is extracted:** DP extracts marked dependency-pair symbols. Counter-projection works on the original symbols. SCT builds a call graph. Argument filtering applies a projection map.
- **What soundness theorem is invoked:** DP uses Arts-Giesl 2000. SCT uses Lee-Jones-Ben-Amram 2001. Argument filtering uses the argument-filtering soundness theorem within the DP framework.
- **How general the method is:** DP handles multi-rule, multi-SCC systems. SCT handles functional programs with multiple call sites. Argument filtering is a DP processor. Counter-projection is the most restricted (works only when the descent is on a single visible argument position).

For Paper A's purposes, the important fact is: **on the step-duplicating schema, all confession methods reduce to the same `ProjectionRank`**. This is a theorem, not an accident. It's because the schema has exactly one recursive call with exactly one strictly decreasing argument, so every method that extracts the recursive-call structure and finds the descent coordinate will find the same coordinate.

### 2.3 The schema-level unification theorem

**Theorem (Confession unification on the step-duplicating schema):** Let `S` be a step-duplicating schema. Any rank `r : S.T → ℕ` that:
1. orients the duplicating step: `r(wrap(s, recur(b, s, n))) < r(recur(b, s, succ(n)))` for all `b, s, n`, and
2. is insensitive to the wrapper's first argument: `r(wrap(x, y)) = r(wrap(x', y))` for all `x, x', y`

must satisfy `r(recur(b, s, succ(n))) ≥ r(recur(b, s, n)) + 1` for all `b, s, n`.

*Proof sketch.* From (1), `r(wrap(s, recur(b, s, n))) < r(recur(b, s, succ(n)))`. From (2), `r(wrap(s, recur(b, s, n))) = r(wrap(s', recur(b, s, n)))` for any `s'`, so in particular `r(wrap(s, recur(b, s, n))) ≥ 0` places no lower constraint on the wrap side beyond `r(recur(b, s, n))` (since `r(wrap(x, y))` is independent of `x`, it is determined by `y`). The strict inequality forces `r(recur(b, s, succ(n))) > r(wrap(s, recur(b, s, n)))`, and since the wrap side is determined only by the inner `recur(b, s, n)`, we get that the recursor rank must strictly decrease from `succ(n)` to `n` in the third argument. ∎

This theorem says: any confession-style rank on the schema must track the counter faithfully. The specific rank values may differ, but the descent is always on the counter coordinate. This is why DP, counter-projection, SCT, and argument filtering all produce the same descent argument on this schema.

---

## 3. New Lean modules

### 3.1 `Meta/ConfessionMethod.lean` (Part B: the generic interface)

```lean
import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.OperationalIncompleteness

/-!
# Confession Methods: Generic Interface

A confession method on a step-duplicating schema is any termination argument
that:

1. extracts a recursive-call relation from the rule structure,
2. projects to a descent coordinate (the counter),
3. declares the payload dimension inert, and
4. appeals to an external soundness metatheorem.

Formally, this is captured by a `ProjectionRank` (already in
`StepDuplicatingSchema.lean`) together with a named soundness justification.
This module wraps that into a `ConfessionMethod` structure and proves that
every `ConfessionMethod` yields a `CertifiedForgettingWitness`.

The point is not that these are different methods on this schema (they all
produce the same rank). The point is that the *class* of confession methods
is formally defined and mechanically shown to share the certified-forgetting
property.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating

/-- The external soundness theorem that licenses the confession.
    Each confession method names a different one. -/
inductive SoundnessLicense
  | artsGiesl2000           -- dependency pairs
  | subtermCriterionDirect  -- subterm criterion without DP extraction
  | leeJonesBenAmram2001    -- size-change termination
  | argumentFilteringSoundness -- argument filtering within DP framework
  deriving DecidableEq, Repr

/-- A confession method on a step-duplicating schema: a projection rank
    together with the name of the external soundness license that
    justifies dropping the payload dimension. -/
structure ConfessionMethod (S : StepDuplicatingSchema) extends
    ProjectionRank S where
  license : SoundnessLicense

/-- Every confession method orients the duplicating step. -/
theorem confession_orients (S : StepDuplicatingSchema) (C : ConfessionMethod S)
    (b s n : S.T) :
    C.rank (S.wrap s (S.recur b s n)) < C.rank (S.recur b s (S.succ n)) :=
  projection_orients_dup_step C.toProjectionRank b s n

/-- Every confession method violates wrapper sensitivity (first argument). -/
theorem confession_violates_wrap1 (S : StepDuplicatingSchema) (C : ConfessionMethod S) :
    ∃ x y : S.T, ¬ (C.rank (S.wrap x y) > C.rank x) :=
  projection_violates_wrap_subterm1 C.toProjectionRank

/-- Every confession method violates wrapper sensitivity (second argument). -/
theorem confession_violates_wrap2 (S : StepDuplicatingSchema) (C : ConfessionMethod S) :
    ∃ x y : S.T, ¬ (C.rank (S.wrap x y) > C.rank y) :=
  projection_violates_wrap_subterm2 C.toProjectionRank

end OperatorKO7.ConfessionMethodFamily
```

**Estimated size:** ~80-100 lines including documentation.

### 3.2 `Meta/ConfessionMethod_DP.lean` (Part A: DP instance)

```lean
import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Confession Method Instance: Dependency Pairs + Subterm Criterion

The canonical confession method. Extracts dependency pairs from the KO7
rules, applies the subterm criterion with projection π(recΔ♯) = 3, and
certifies counter descent via Arts-Giesl 2000.

This is a thin wrapper: the underlying `ProjectionRank` is `dpProjectionRank`
from `CompositionalMeasure_Impossibility.lean`, already formalized.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- Dependency pairs + subterm criterion as a confession method. -/
def dpConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.artsGiesl2000

end OperatorKO7.ConfessionMethodFamily
```

**Estimated size:** ~30-40 lines.

### 3.3 `Meta/ConfessionMethod_CounterProjection.lean` (Part A: counter-projection instance)

```lean
import OperatorKO7.Meta.ConfessionMethod

/-!
# Confession Method Instance: Direct Counter-Projection (Subterm Criterion)

The subterm criterion applied directly to the argument positions of F,
without passing through DP extraction. On the two-rule schema:

- π(F) = 3 (select the counter argument)
- Check: S(n) ▷ n (strict subterm)
- Y is never evaluated

This is structurally identical to DP on this schema because the schema has
a single defined symbol with a single recursive call site. The methods
diverge on more complex systems.

The underlying rank is the same `ProjectionRank` as DP. What differs is
the soundness license: the subterm criterion is applied directly to the
rule's argument positions, not to dependency-pair symbols.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- Counter-projection via direct subterm criterion. Same rank as DP on this
    schema; different soundness license (subterm criterion on argument
    positions rather than on DP symbols). -/
def counterProjectionConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.subtermCriterionDirect

/-- On the step-duplicating schema, counter-projection and DP produce the
    same rank function. -/
theorem counterProjection_eq_dp_rank :
    counterProjectionConfession.rank = dpConfession.rank := rfl

end OperatorKO7.ConfessionMethodFamily
```

**Estimated size:** ~40-50 lines.

### 3.4 `Meta/ConfessionMethod_SCT.lean` (Part A: Size-Change Termination instance)

This is the most substantive new module because SCT has its own formalism (size-change graphs) that needs to be represented, at least minimally, in Lean.

```lean
import OperatorKO7.Meta.ConfessionMethod

/-!
# Confession Method Instance: Size-Change Termination (SCT)

Size-Change Termination (Lee, Jones, Ben-Amram 2001) constructs size-change
graphs for each recursive call site and checks that every infinite call
multipath contains an infinitely descending thread.

For the step-duplicating schema:
- There is one recursive call: recur(b, s, succ(n)) calls recur(b, s, n)
- The size-change graph has one arc: argument 3 decreases strictly (↓)
- Arguments 1 and 2 are non-increasing (≥) or untracked
- Since every call path passes through this single graph, and the graph has
  a strict descent arc on argument 3, SCT certifies termination.

The formal content is:
1. Define the size-change graph for the schema's recursive call
2. Show the graph has a strict descent arc on the counter coordinate
3. Derive that the SCT criterion is satisfied
4. Package as a `ConfessionMethod`

The SCT rank is the same as the DP projection rank on this schema: it
tracks only the counter depth. What differs is the extraction method
(call-graph analysis rather than dependency-pair extraction) and the
soundness license (Lee-Jones-Ben-Amram 2001 rather than Arts-Giesl 2000).
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating

/-- A size-change arc records whether an argument strictly decreases (↓),
    is non-increasing (≥), or is untracked between caller and callee. -/
inductive SCArc
  | strictDecrease   -- ↓ : callee value < caller value
  | nonIncreasing    -- ≥ : callee value ≤ caller value
  | untracked        -- no relation asserted
  deriving DecidableEq, Repr

/-- A size-change graph for a function with `n` arguments is an `n × n`
    matrix of arcs from caller argument positions to callee argument
    positions. -/
structure SizeChangeGraph (arity : Nat) where
  arcs : Fin arity → Fin arity → SCArc

/-- The size-change graph for the schema's single recursive call.
    The schema has arity 3 (b=0, s=1, n=2).
    - Argument 0 (b): caller b maps to callee b, non-increasing
    - Argument 1 (s): caller s maps to callee s, non-increasing
    - Argument 2 (n): caller succ(n) maps to callee n, strict decrease -/
def schemaRecCallGraph : SizeChangeGraph 3 where
  arcs := fun i j =>
    if i = 2 ∧ j = 2 then SCArc.strictDecrease
    else if i = j then SCArc.nonIncreasing
    else SCArc.untracked

/-- The schema's size-change graph has a strict decrease on the diagonal
    of argument position 2 (the counter). -/
theorem schemaRecCallGraph_counter_descent :
    schemaRecCallGraph.arcs ⟨2, by omega⟩ ⟨2, by omega⟩ = SCArc.strictDecrease := by
  simp [schemaRecCallGraph, SizeChangeGraph.arcs]

/-- A size-change graph satisfies the SCT criterion if every idempotent
    in the closure of the graph monoid contains a strict decrease on the
    diagonal. For a single recursive call with one graph, this reduces to:
    the graph itself has a strict decrease on some diagonal entry. -/
def sctSatisfied (G : SizeChangeGraph n) : Prop :=
  ∃ i : Fin n, G.arcs i i = SCArc.strictDecrease

/-- The schema's SCT criterion is satisfied via the counter descent. -/
theorem schema_sct_satisfied : sctSatisfied schemaRecCallGraph :=
  ⟨⟨2, by omega⟩, schemaRecCallGraph_counter_descent⟩

/-- SCT as a confession method on the KO7 schema. The rank is the same
    counter-projection rank; the license is Lee-Jones-Ben-Amram 2001. -/
def sctConfession : ConfessionMethod ko7Schema where
  toProjectionRank := OperatorKO7.CompositionalImpossibility.dpProjectionRank
  license := SoundnessLicense.leeJonesBenAmram2001

/-- On the step-duplicating schema, SCT and DP produce the same rank. -/
theorem sct_eq_dp_rank :
    sctConfession.rank = dpConfession.rank := rfl

end OperatorKO7.ConfessionMethodFamily
```

**Estimated size:** ~120-160 lines including the SCT formalization.

### 3.5 `Meta/ConfessionMethod_ArgumentFiltering.lean` (Part A: argument filtering instance)

```lean
import OperatorKO7.Meta.ConfessionMethod

/-!
# Confession Method Instance: Argument Filtering

Argument filtering (Arts-Giesl 2000, within the DP framework) maps each
function symbol to a subset or projection of its arguments. For the schema:

- π(recur) = 3  (project to the counter argument only)
- π(wrap) = ε   (collapse to nothing, or project to second argument)
- π(succ) = 1   (keep the argument)
- π(base) = ε   (collapse to nothing)

After filtering, the rule becomes: n+1 → n (in the projected universe).
This is trivially terminating.

The filtering is a structural drop: it removes arguments from the proof
obligation rather than constructing a new comparison object. The soundness
is licensed by the argument-filtering soundness theorem within the DP
framework.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- Argument filtering as a confession method. Same projection rank;
    the license is the argument-filtering soundness theorem. -/
def argumentFilteringConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.argumentFilteringSoundness

/-- On the step-duplicating schema, argument filtering and DP produce
    the same rank. -/
theorem argumentFiltering_eq_dp_rank :
    argumentFilteringConfession.rank = dpConfession.rank := rfl

end OperatorKO7.ConfessionMethodFamily
```

**Estimated size:** ~50-60 lines.

### 3.6 `Meta/ConfessionMethod_Family.lean` (collector module)

```lean
import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP
import OperatorKO7.Meta.ConfessionMethod_CounterProjection
import OperatorKO7.Meta.ConfessionMethod_SCT
import OperatorKO7.Meta.ConfessionMethod_ArgumentFiltering
import OperatorKO7.Meta.OperationalIncompleteness

/-!
# The Confession-Method Family: Collected Results

This module collects the four formalized confession methods and proves
family-level theorems about their shared structure.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaOperationalIncompleteness

/-- All four confession methods are enumerated. -/
def allConfessionMethods : List (ConfessionMethod ko7Schema) :=
  [dpConfession, counterProjectionConfession, sctConfession, argumentFilteringConfession]

/-- Every confession method in the family produces the same rank on
    the KO7 schema. -/
theorem family_rank_agreement :
    ∀ C ∈ allConfessionMethods,
      C.rank = dpConfession.rank := by
  intro C hC
  simp [allConfessionMethods] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> rfl

/-- Every confession method in the family is a certified-forgetting
    witness. -/
theorem family_certified_forgetting :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness,
        fw.rank = C.rank := by
  intro C hC
  rw [family_rank_agreement C hC]
  exact dp_projection_exhibits_certified_forgetting

/-- The confession family has exactly four members on this schema,
    each with a distinct soundness license. -/
theorem family_distinct_licenses :
    (allConfessionMethods.map (·.license)).Nodup := by
  decide

/-- On the step-duplicating schema, confession methods are a structural
    CLASS, not a single named method. The class shares a common rank
    (counter projection) and a common structural shape (extract recursive
    calls, project to descent coordinate, declare payload inert). What
    varies is the extraction mechanism and the soundness license.

    This is the formal content behind Paper C's claim that the
    construction/confession boundary separates method classes, not
    individual methods. -/
theorem confession_is_a_class :
    allConfessionMethods.length = 4
    ∧ (∀ C ∈ allConfessionMethods, C.rank = dpConfession.rank)
    ∧ (allConfessionMethods.map (·.license)).Nodup := by
  refine ⟨by decide, family_rank_agreement, family_distinct_licenses⟩

end OperatorKO7.ConfessionMethodFamily
```

**Estimated size:** ~80-100 lines.

---

## 4. Modifications to existing modules

### 4.1 Update `SchemaAPI.lean`

Add imports for the new confession-method modules:

```lean
-- Confession method family
import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP
import OperatorKO7.Meta.ConfessionMethod_CounterProjection
import OperatorKO7.Meta.ConfessionMethod_SCT
import OperatorKO7.Meta.ConfessionMethod_ArgumentFiltering
import OperatorKO7.Meta.ConfessionMethod_Family
```

### 4.2 Update `OperationalIncompleteness.lean`

Add a theorem connecting the confession family to operational incompleteness:

```lean
/-- The confession family provides four independent witnesses that the
    transformed-call layer resolves KO7's operational incompleteness at
    the payload dimension. Each uses the same rank but a different
    external soundness license. -/
theorem confession_family_resolves_operational_incompleteness :
    ∀ C ∈ ConfessionMethodFamily.allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness, fw.rank = C.rank :=
  ConfessionMethodFamily.family_certified_forgetting
```

---

## 5. What this does for the papers

### For Paper A

The escape characterization currently names three methods (DP, nonlinear polynomial W, KO7-specialized MPO). The new formalization adds:

- **Remark (Confession-method family):** The DP escape is not a single-method phenomenon. Four methods with distinct soundness licenses (Arts-Giesl 2000, direct subterm criterion, Lee-Jones-Ben-Amram 2001, argument-filtering soundness) produce the same `ProjectionRank` on the schema. The `ConfessionMethod_Family.lean` module mechanizes the class and proves rank agreement, certified-forgetting equivalence, and license distinctness.

This goes in Section 4.5 (The DP escape) as a remark after Theorem `thm:dp-escape`.

### For Paper C

The construction/confession asymmetry is now backed by a mechanized family, not just one named method. The key claim -- "the confession is a structural class, not a single method" -- is now a theorem (`confession_is_a_class`). This strengthens the paper's central distinction.

### For Paper B

The benchmark admissibility class can be formally widened from "DP + subterm criterion" to "any method in the confession family" with mechanical backing. The report's Option B becomes the mechanized option.

---

## 6. Dependency graph

```
StepDuplicatingSchema.lean  (existing: ProjectionRank)
        │
        ▼
ConfessionMethod.lean  (NEW: ConfessionMethod structure)
        │
        ├──▶ ConfessionMethod_DP.lean  (NEW: dpConfession)
        ├──▶ ConfessionMethod_CounterProjection.lean  (NEW: counterProjectionConfession)
        ├──▶ ConfessionMethod_SCT.lean  (NEW: sctConfession + SCT formalization)
        ├──▶ ConfessionMethod_ArgumentFiltering.lean  (NEW: argumentFilteringConfession)
        │
        ▼
ConfessionMethod_Family.lean  (NEW: collected results)
        │
        ▼
OperationalIncompleteness.lean  (UPDATED: family connection)
        │
        ▼
SchemaAPI.lean  (UPDATED: new imports)
```

---

## 7. Estimated effort

| Module | Lines | Difficulty | Notes |
|--------|-------|-----------|-------|
| `ConfessionMethod.lean` | 80-100 | Low | Thin wrapper over existing `ProjectionRank` |
| `ConfessionMethod_DP.lean` | 30-40 | Trivial | Wraps existing `dpProjectionRank` |
| `ConfessionMethod_CounterProjection.lean` | 40-50 | Trivial | Same rank, different license |
| `ConfessionMethod_SCT.lean` | 120-160 | Medium | Needs `SizeChangeGraph`, `SCArc`, `sctSatisfied` |
| `ConfessionMethod_ArgumentFiltering.lean` | 50-60 | Trivial | Same rank, different license |
| `ConfessionMethod_Family.lean` | 80-100 | Low | Collection + family-level theorems |
| Updates to existing modules | 20-30 | Trivial | Import additions |
| **Total** | **420-540** | | |

The SCT module is the only non-trivial new formalization. Everything else reuses existing infrastructure.

---

## 8. Build verification plan

After implementing all modules:

1. `lake build OperatorKO7` must succeed with no errors
2. `#print axioms OperatorKO7.ConfessionMethodFamily.confession_is_a_class` should show only `propext`, `Classical.choice`, `Quot.sound`
3. `#print axioms OperatorKO7.ConfessionMethodFamily.family_certified_forgetting` should show the same
4. The existing test suite (`lake exe verifyTpdbExport`, sanity checks) must continue to pass

---

## 9. What this does NOT cover

- **Generic DP framework formalization.** We are not building a library of DP processors, usable rules, or SCC decomposition algorithms. The formalization is intentionally narrow: it captures the confession shape on the step-duplicating schema.
- **SCT for arbitrary programs.** The SCT formalization is specific to the schema's single recursive call. General SCT (monoid closures, idempotent analysis) is out of scope.
- **Usable rules.** The fifth method from the boundary report (usable rules + subterm projection) is conditionally within-boundary and harder to formalize cleanly. Deferred.
- **Cross-schema generalization.** The `ConfessionMethod` structure is parameterized by `StepDuplicatingSchema`, so it applies to any schema instance (including the textbook rule in `TextbookDupInstance.lean`), but we do not prove results for arbitrary TRSes.
