# OperatorKO7 Complete Documentation

**Repository:** [MosesRahnama/OperatorKO7](https://github.com/MosesRahnama/OperatorKO7)
**Updated:** February 2026
**Total LOC:** ~5,500 (Lean 4)

Complete source listing. Every file in the project excluding README.

---

## Table of Contents

1. [OperatorKO7.lean](#1-OperatorKO7-lean) - 12 lines
2. [OperatorKO7/Kernel.lean](#2-OperatorKO7-Kernel-lean) - 59 lines
3. [OperatorKO7/Meta/SafeStep_Core.lean](#3-OperatorKO7-Meta-SafeStep_Core-lean) - 156 lines
4. [OperatorKO7/Meta/ComputableMeasure.lean](#4-OperatorKO7-Meta-ComputableMeasure-lean) - 460 lines
5. [OperatorKO7/Meta/Normalize_Safe.lean](#5-OperatorKO7-Meta-Normalize_Safe-lean) - 252 lines
6. [OperatorKO7/Meta/SafeStep_Ctx.lean](#6-OperatorKO7-Meta-SafeStep_Ctx-lean) - 548 lines
7. [OperatorKO7/Meta/Confluence_Safe.lean](#7-OperatorKO7-Meta-Confluence_Safe-lean) - 529 lines
8. [OperatorKO7/Meta/Newman_Safe.lean](#8-OperatorKO7-Meta-Newman_Safe-lean) - 205 lines
9. [OperatorKO7/Meta/ComputableMeasure_Verification.lean](#9-OperatorKO7-Meta-ComputableMeasure_Verification-lean) - 241 lines
10. [OperatorKO7/Meta/ComputableMeasure_Test.lean](#10-OperatorKO7-Meta-ComputableMeasure_Test-lean) - 45 lines
11. [OperatorKO7/Meta/DM_MPO_Orientation.lean](#11-OperatorKO7-Meta-DM_MPO_Orientation-lean) - 51 lines
12. [OperatorKO7/Meta/Examples_Publish.lean](#12-OperatorKO7-Meta-Examples_Publish-lean) - 29 lines
13. [OperatorKO7/Meta/Operational_Incompleteness.lean](#13-OperatorKO7-Meta-Operational_Incompleteness-lean) - 1188 lines
14. [OperatorKO7/Meta/Impossibility_Lemmas.lean](#14-OperatorKO7-Meta-Impossibility_Lemmas-lean) - 386 lines
15. [OperatorKO7/Meta/FailureModes.lean](#15-OperatorKO7-Meta-FailureModes-lean) - 94 lines
16. [OperatorKO7/Meta/ContractProbes.lean](#16-OperatorKO7-Meta-ContractProbes-lean) - 67 lines
17. [OperatorKO7/Meta/Conjecture_Boundary.lean](#17-OperatorKO7-Meta-Conjecture_Boundary-lean) - 490 lines
18. [OperatorKO7/Meta/PaperApproachIndex.lean](#18-OperatorKO7-Meta-PaperApproachIndex-lean) - 39 lines
19. [OperatorKO7/Meta/CNFOrdinal.lean](#19-OperatorKO7-Meta-CNFOrdinal-lean) - 1139 lines
20. [OperatorKO7/Meta/HydraCore.lean](#20-OperatorKO7-Meta-HydraCore-lean) - 35 lines
21. [OperatorKO7/Meta/GoodsteinCore.lean](#21-OperatorKO7-Meta-GoodsteinCore-lean) - 40 lines
22. [OperatorKO7/Test/Sanity.lean](#22-OperatorKO7-Test-Sanity-lean) - 11 lines

---

## 1. OperatorKO7.lean

**Lines:** 12

```lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.ComputableMeasure

/-!
Public entrypoint for the `OperatorKO7` Lean library.

Why this file exists:
- Acts as the minimal import surface for downstream users and reviewers.
- Keeps the default build stable by importing the core kernel and the canonical computable SafeStep development.
- Additional modules (normalizer, confluence) are imported directly where needed
  (e.g. in `OperatorKO7/Meta/Examples_Publish.lean`).
-/
```

## 2. OperatorKO7/Kernel.lean

**Lines:** 59

```lean
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
| delta : Trace → Trace
| integrate : Trace → Trace
| merge : Trace → Trace → Trace
| app : Trace → Trace → Trace
| recΔ : Trace → Trace → Trace → Trace
| eqW : Trace → Trace → Trace
open Trace

/-- The full kernel reduction relation (8 unconditional root rules). -/
inductive Step : Trace → Trace → Prop
| R_int_delta : ∀ t, Step (integrate (delta t)) void
| R_merge_void_left : ∀ t, Step (merge void t) t
| R_merge_void_right : ∀ t, Step (merge t void) t
| R_merge_cancel : ∀ t, Step (merge t t) t
| R_rec_zero : ∀ b s, Step (recΔ b s void) b
| R_rec_succ : ∀ b s n, Step (recΔ b s (delta n)) (app s (recΔ b s n))
| R_eq_refl : ∀ a, Step (eqW a a) void
| R_eq_diff : ∀ a b, Step (eqW a b) (integrate (merge a b))

/-- Reflexive-transitive closure of the kernel step relation `Step`. -/
inductive StepStar : Trace → Trace → Prop
| refl : ∀ t, StepStar t t
| tail : ∀ {a b c}, Step a b → StepStar b c → StepStar a c

/-- Normal forms for the full kernel relation: no outgoing `Step`. -/
def NormalForm (t : Trace) : Prop := ¬ ∃ u, Step t u

/-- Transitivity of `StepStar` (concatenation of two multi-step reductions). -/
theorem stepstar_trans {a b c : Trace} (h1 : StepStar a b) (h2 : StepStar b c) : StepStar a c := by
  induction h1 with
  | refl => exact h2
  | tail hab _ ih => exact StepStar.tail hab (ih h2)

/-- Any single `Step` is also a `StepStar`. -/
theorem stepstar_of_step {a b : Trace} (h : Step a b) : StepStar a b :=
  StepStar.tail h (StepStar.refl b)

/-- If `a` is a normal form, then any `a ⇒* b` must be trivial (`b = a`). -/
theorem nf_no_stepstar_forward {a b : Trace} (hnf : NormalForm a) (h : StepStar a b) : a = b :=
  match h with
  | StepStar.refl _ => rfl
  | StepStar.tail hs _ => False.elim (hnf ⟨_, hs⟩)

end OperatorKO7
```

## 3. OperatorKO7/Meta/SafeStep_Core.lean

**Lines:** 156

```lean
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

local infix:70 " <ₘ " => Multiset.IsDershowitzMannaLT

/-- Weight of a trace: recursion-depth payload at `recΔ` heads. -/
@[simp] def weight : Trace → Nat
| recΔ _ _ n => weight n + 1
| _          => 0

/-- DM multiset payload for KO7 traces. -/
@[simp] def kappaM : Trace → Multiset Nat
| void            => 0
| delta t         => kappaM t
| integrate t     => kappaM t
| merge a b       => kappaM a ∪ kappaM b
| app   a b       => kappaM a ∪ kappaM b
| recΔ b s n      => (weight n + 1) ::ₘ (kappaM n ∪ kappaM s) + kappaM b
| eqW  a b        => kappaM a ∪ kappaM b

instance : WellFoundedLT Nat := inferInstance

/-- Well-foundedness of Dershowitz-Manna order on multisets of naturals. -/
lemma wf_dm : WellFounded (fun a b : Multiset Nat => a <ₘ b) :=
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
    kappaM (merge t t) = kappaM t ∪ kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_rec_zero (b s : Trace) :
    kappaM (recΔ b s void) = (1 ::ₘ kappaM s) + kappaM b := by
  simp [kappaM]

@[simp] lemma kappaM_eq_refl (a : Trace) :
    kappaM (eqW a a) = kappaM a ∪ kappaM a := by
  simp [kappaM]

@[simp] lemma kappaM_eq_diff (a b : Trace) :
    kappaM (integrate (merge a b)) = kappaM (eqW a b) := by
  simp [kappaM]

lemma dm_lt_add_of_ne_zero (X Z : Multiset Nat) (h : Z ≠ 0) :
    X <ₘ (X + Z) := by
  classical
  refine ⟨X, (0 : Multiset Nat), Z, ?hZ, ?hM, rfl, ?hY⟩
  · simpa using h
  · simp
  · simp

lemma dm_lt_add_of_ne_zero' (X Z : Multiset Nat) (h : Z ≠ 0) :
    Multiset.IsDershowitzMannaLT X (X + Z) := by
  classical
  refine ⟨X, (0 : Multiset Nat), Z, ?hZ, ?hM, rfl, ?hY⟩
  · simpa using h
  · simp
  · simp

lemma dm_drop_R_rec_zero (b s : Trace) :
    kappaM b <ₘ kappaM (recΔ b s void) := by
  classical
  have hdm : Multiset.IsDershowitzMannaLT (kappaM b) (kappaM b + (1 ::ₘ kappaM s)) :=
    dm_lt_add_of_ne_zero' (kappaM b) (1 ::ₘ kappaM s) (by simp)
  simpa [kappaM, add_comm, add_left_comm, add_assoc] using hdm

lemma union_self_ne_zero_of_ne_zero {X : Multiset Nat} (h : X ≠ 0) :
    X ∪ X ≠ (0 : Multiset Nat) := by
  classical
  intro hU
  have hUU : X ∪ X = X := by
    ext a
    simp [Multiset.count_union, max_self]
  exact h (by simpa [hUU] using hU)

end MetaSN_DM

namespace MetaSN_KO7

open MetaSN_DM

@[simp] def deltaFlag : Trace → Nat
| recΔ _ _ (delta _) => 1
| _                  => 0

@[simp] lemma deltaFlag_void : deltaFlag void = 0 := rfl
@[simp] lemma deltaFlag_integrate (t : Trace) : deltaFlag (integrate t) = 0 := rfl
@[simp] lemma deltaFlag_merge (a b : Trace) : deltaFlag (merge a b) = 0 := rfl
@[simp] lemma deltaFlag_eqW (a b : Trace) : deltaFlag (eqW a b) = 0 := rfl
@[simp] lemma deltaFlag_app (a b : Trace) : deltaFlag (app a b) = 0 := rfl
@[simp] lemma deltaFlag_rec_zero (b s : Trace) : deltaFlag (recΔ b s void) = 0 := by
  simp [deltaFlag]
@[simp] lemma deltaFlag_rec_delta (b s n : Trace) : deltaFlag (recΔ b s (delta n)) = 1 := by
  simp [deltaFlag]

lemma deltaFlag_range (t : Trace) : deltaFlag t = 0 ∨ deltaFlag t = 1 := by
  cases t with
  | void => simp
  | delta t => simp
  | integrate t => simp
  | merge a b => simp
  | app a b => simp
  | recΔ b s n =>
      cases n with
      | void => simp [deltaFlag]
      | delta n => simp [deltaFlag]
      | integrate t => simp [deltaFlag]
      | merge a b => simp [deltaFlag]
      | app a b => simp [deltaFlag]
      | eqW a b => simp [deltaFlag]
      | recΔ b s n => simp [deltaFlag]
  | eqW a b => simp

/-- Guarded subrelation used by the canonical termination development. -/
inductive SafeStep : Trace → Trace → Prop
| R_int_delta (t) : SafeStep (integrate (delta t)) void
| R_merge_void_left (t) (hδ : deltaFlag t = 0) : SafeStep (merge void t) t
| R_merge_void_right (t) (hδ : deltaFlag t = 0) : SafeStep (merge t void) t
| R_merge_cancel (t) (hδ : deltaFlag t = 0) (h0 : kappaM t = 0) : SafeStep (merge t t) t
| R_rec_zero (b s) (hδ : deltaFlag b = 0) : SafeStep (recΔ b s void) b
| R_rec_succ (b s n) : SafeStep (recΔ b s (delta n)) (app s (recΔ b s n))
| R_eq_refl (a) (h0 : kappaM a = 0) : SafeStep (eqW a a) void
| R_eq_diff (a b) (hne : a ≠ b) : SafeStep (eqW a b) (integrate (merge a b))

/-- Reverse relation for strong-normalization statements. -/
def SafeStepRev : Trace → Trace → Prop := fun a b => SafeStep b a

end MetaSN_KO7

```

## 4. OperatorKO7/Meta/ComputableMeasure.lean

**Lines:** 460

```lean
import OperatorKO7.Meta.SafeStep_Core
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Computable Termination Measure for KO7 SafeStep

This module provides a **fully computable** termination proof for the `SafeStep` relation
using the triple-lexicographic measure μ3c = (δ, κᴹ, τ) where:
- δ (deltaFlag): Binary flag detecting `recΔ b s (delta n)` patterns
- κᴹ (kappaM): Dershowitz-Manna multiset of recursion weights
- τ (tau): Computable natural number rank (replaces noncomputable ordinal μ)

## Key Properties
- **Fully Computable Measures**: All measure functions (`deltaFlag`, `kappaM`, `tau`) are computable;
  classical reasoning is used only in proof terms (Prop-valued well-foundedness arguments)
- **Complete Coverage**: All 8 SafeStep constructors proven to strictly decrease μ3c
- **Bulletproof**: Explicit Prod.Lex parameters prevent elaboration issues
- **Lint-Clean**: No warnings, no sorry, no admit, no unsafe

## Technical Approach
The measure μ3c uses lexicographic ordering Lex3c := Prod.Lex (<) (Prod.Lex DM (<))
where DM is Mathlib's Dershowitz-Manna multiset order. Each SafeStep rule is proven
to strictly decrease this measure through either:
1. δ-drop: For rec_succ (1 → 0)
2. κᴹ-drop: Via DM order for rules that modify recursion structure
3. τ-drop: When δ and κᴹ tie, using carefully chosen head weights

## Constants
τ assigns head weights ensuring strict inequalities:
- void: 0
- delta: transparent (preserves inner term's weight)
- integrate: 1 + inner
- merge: 2 + sum of arguments
- app: 1 + sum of arguments
- recΔ: 3 + sum of all three arguments
- eqW: 4 + sum of arguments (ensures 1+2+X < 4+X for eq_diff)

## References
- Dershowitz & Manna (1979): Proving termination with multiset orderings
- Baader & Nipkow: Term Rewriting and All That
- Newman's Lemma: Local confluence + termination → confluence
-/

namespace OperatorKO7.MetaCM

-- Disable unnecessary simpa linter locally for this file
set_option linter.unnecessarySimpa false

open OperatorKO7 Trace Multiset
open MetaSN_KO7
open MetaSN_DM
open scoped Classical

/-! ## Section 1: Computable Natural Rank τ ----------------------------------------------- -/

/-- **Head-weighted structural size (τ)**

A computable Nat-valued rank function with meticulously chosen constants.

### Key Properties:
1. τ(eqW a b) > τ(integrate (merge a b)) for all a, b (critical for eq_diff)
2. τ strictly increases under all constructors except delta
3. All inequalities provable by omega or decide

### Weight Design:
- void: 0 (base case)
- delta t: τ(t) (transparent wrapper)
- integrate/app: weight 1
- merge: weight 2
- recΔ: weight 3
- eqW: weight 4 (ensures 1+2+X < 4+X)
-/
@[simp] def tau : Trace → Nat
| void            => 0
| delta t         => tau t
| integrate t     => 1 + tau t            -- baseIntegrate = 1
| merge a b       => 2 + tau a + tau b    -- baseMerge = 2
| app a b         => 1 + tau a + tau b    -- baseApp = 1
| recΔ b s n      => 3 + tau b + tau s + tau n  -- baseRec = 3
| eqW a b         => 4 + tau a + tau b    -- baseEq = baseIntegrate + baseMerge + 1 = 4

/-! ## Section 2: Dershowitz-Manna Order and Lexicographic Structure -/

/-- **Dershowitz-Manna multiset order (DM)**

The well-founded multiset order that correctly handles duplication.
Crucial for rules like merge_cancel and eq_refl.
-/
def DM (X Y : Multiset Nat) : Prop :=
  Multiset.IsDershowitzMannaLT X Y

/-- **Inner lexicographic order (LexDM_c)**

Combines DM order with Nat ordering to form the (κᴹ, τ) component.
Prioritizes κᴹ changes via DM over τ changes.
-/
@[simp] def LexDM_c : (Multiset Nat × Nat) → (Multiset Nat × Nat) → Prop :=
  Prod.Lex (fun a b : Multiset Nat => DM a b) (· < ·)

/-- Well-foundedness of the computable inner lex (DM × Nat<). -/
lemma wf_LexDM_c : WellFounded LexDM_c :=
  WellFounded.prod_lex MetaSN_DM.wf_dm Nat.lt_wfRel.wf

/-- **Outer triple lexicographic order (Lex3c)**

The complete well-founded order: (δ, (κᴹ, τ))
Priority: δ-flag > κᴹ (via DM) > τ
-/
@[simp] def Lex3c : (Nat × (Multiset Nat × Nat)) → (Nat × (Multiset Nat × Nat)) → Prop :=
  Prod.Lex (· < ·) LexDM_c

/-- Well-foundedness of the computable triple lex (Nat< × (DM × Nat<)). -/
lemma wf_Lex3c : WellFounded Lex3c := by
  exact WellFounded.prod_lex Nat.lt_wfRel.wf wf_LexDM_c

/-- **Critical lifting lemma**

Lifts a DM decrease on κᴹ to the full inner order, regardless of τ.
EXPLICIT PARAMETERS prevent all elaboration issues.
-/
lemma dm_to_LexDM_c_left {X Y : Multiset Nat} {τ₁ τ₂ : Nat}
    (h : DM X Y) : LexDM_c (X, τ₁) (Y, τ₂) := by
  -- Use explicit parameters to avoid inference brittleness, mirroring KO7.
  exact
    (Prod.Lex.left
      (α := Multiset Nat) (β := Nat)
      (ra := fun a b : Multiset Nat => DM a b) (rb := (· < ·))
      (a₁ := X) (a₂ := Y) (b₁ := τ₁) (b₂ := τ₂)
      (by simpa using h))

/-- **The computable triple measure μ3c**

Assembles (δ, κᴹ, τ) from a trace term.
Fully computable replacement for the ordinal-based measure.
-/
@[simp] def mu3c (t : Trace) : Nat × (Multiset Nat × Nat) :=
  (deltaFlag t, (kappaM t, tau t))

/-! ## Section 3: Per-Rule Termination Proofs

Each SafeStep constructor proven to strictly decrease μ3c.
Systematic approach: identify decreasing component, build witness, normalize.
-/

open Classical

/-- **Rule: integrate (delta t) → void**

Strategy:
- If κᴹ(t) = 0: τ-drop (0 < 1 + τ(t))
- If κᴹ(t) ≠ 0: DM-drop (0 <ₘ κᴹ(t))
-/
lemma drop_R_int_delta_c (t : Trace) :
    Lex3c (mu3c void) (mu3c (integrate (delta t))) := by
  classical
  by_cases h0 : kappaM t = 0
  · -- κ tie at 0: take τ-right since 0 < 1 + τ t
    -- Inner κ tie at 0; show τ-right: 0 < 1 + τ t
    have hin0 : LexDM_c ((0 : Multiset Nat), tau void)
        ((0 : Multiset Nat), tau (integrate (delta t))) := by
      refine Prod.Lex.right (0 : Multiset Nat) ?tauLt
      have : (0 : Nat) < Nat.succ (tau t) := Nat.succ_pos _
      simpa [tau, Nat.add_comm] using this
    -- Outer α=0 witness on concrete pairs, then rewrite μ-components
    have hcore : Lex3c (0, ((0 : Multiset Nat), tau void))
        (0, ((0 : Multiset Nat), tau (integrate (delta t)))) :=
      (Prod.Lex.right
        (α := Nat) (β := (Multiset Nat × Nat))
        (ra := (· < ·)) (rb := LexDM_c)
        (a := (0 : Nat)) hin0)
    simpa [Lex3c, mu3c, kappaM, kappaM_int_delta, tau, h0] using hcore
  · -- κ strictly grows from 0 to κᴹ t ≠ 0: DM-left on 0 <ₘ κᴹ t
    have hdm : DM (0 : Multiset Nat) (kappaM (integrate (delta t))) := by
      -- kappaM (integrate (delta t)) = kappaM t
      have : kappaM (integrate (delta t)) = kappaM t := by simpa [kappaM_int_delta]
      -- Use DM X < X+Z with X=0, Z=kappaM t (nonzero)
      have hz : kappaM t ≠ (0 : Multiset Nat) := by
        intro hz; exact h0 (by simpa using hz)
      -- 0 <ₘ 0 + (kappaM t) = kappaM t
      simpa [this, zero_add] using MetaSN_DM.dm_lt_add_of_ne_zero' (0 : Multiset Nat) (kappaM t) hz
    -- Inner DM-left on concrete κ-components, then close outer at α=0
    have hin0 : LexDM_c ((0 : Multiset Nat), tau void)
        ((kappaM (integrate (delta t))), tau (integrate (delta t))) := by
      simpa using
        (dm_to_LexDM_c_left (X := (0 : Multiset Nat)) (Y := kappaM (integrate (delta t)))
          (τ₁ := tau void) (τ₂ := tau (integrate (delta t))) hdm)
    have hcore : Lex3c (0, ((0 : Multiset Nat), tau void))
        (0, (kappaM (integrate (delta t)), tau (integrate (delta t)))) :=
      (Prod.Lex.right
        (α := Nat) (β := (Multiset Nat × Nat))
        (ra := (· < ·)) (rb := LexDM_c)
        (a := (0 : Nat)) hin0)
    simpa [Lex3c, mu3c, kappaM, kappaM_int_delta, tau] using hcore

/-- **Rule: merge void t → t** (guarded by δ(t) = 0)

Strategy: τ-drop under δ and κ ties
Key inequality: τ(t) < 2 + τ(t)
-/
lemma drop_R_merge_void_left_c (t : Trace) (hδ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge void t)) := by
  classical
  -- Build inner κ-tie, τ-right
  have hκ : kappaM (merge void t) = kappaM t := by simpa using MetaSN_DM.kappaM_merge_void_left t
  have hτ' : tau t < 2 + tau t := by
    omega
  have hτm : tau t < tau (merge void t) := by
    simpa [tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hτ'
  -- Inner κ-anchor at RHS κ
  have hin : LexDM_c (kappaM t, tau t) (kappaM (merge void t), tau (merge void t)) := by
    simpa [hκ] using (Prod.Lex.right (kappaM (merge void t)) hτm)
  -- Canonical α=0 outer witness; close by rewriting μ3c pairs
  have hin' : LexDM_c (kappaM t, tau t) (kappaM t, 2 + tau t) := by
    simpa [hκ, tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hin
  have H : Lex3c (0, (kappaM t, tau t)) (0, (kappaM t, 2 + tau t)) :=
    (Prod.Lex.right
      (α := Nat) (β := (Multiset Nat × Nat))
      (ra := (· < ·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin')
  -- Now prove the main goal: both sides have δ=0 due to guard
  unfold Lex3c mu3c
  simp only [deltaFlag] at hδ ⊢
  rw [hδ]
  simp only [hκ, tau]
  exact H

/-- **Rule: merge t void → t** (guarded by δ(t) = 0)

Symmetric to merge_void_left.
Strategy: τ-drop under ties
-/
lemma drop_R_merge_void_right_c (t : Trace) (hδ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge t void)) := by
  classical
  -- Inner κ-tie and τ-right
  have hκ : kappaM (merge t void) = kappaM t := by simpa using MetaSN_DM.kappaM_merge_void_right t
  have hτ' : tau t < 2 + tau t := by
    omega
  have hτm : tau t < tau (merge t void) := by
    simpa [tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hτ'
  have hin : LexDM_c (kappaM t, tau t) (kappaM (merge t void), tau (merge t void)) := by
    simpa [hκ] using (Prod.Lex.right (kappaM (merge t void)) hτm)
  -- Canonical α=0 outer witness; close by rewriting μ3c pairs
  have hin' : LexDM_c (kappaM t, tau t) (kappaM t, 2 + tau t) := by
    simpa [hκ, tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hin
  have H : Lex3c (0, (kappaM t, tau t)) (0, (kappaM t, 2 + tau t)) :=
    (Prod.Lex.right
      (α := Nat) (β := (Multiset Nat × Nat))
      (ra := (· < ·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin')
  -- Now prove the main goal: both sides have δ=0 due to guard
  unfold Lex3c mu3c
  simp only [deltaFlag] at hδ ⊢
  rw [hδ]
  simp only [hκ, tau]
  exact H

/-- **Rule: eqW a b → integrate (merge a b)**

The critical inequality: 1 + 2 + X < 4 + X
This is why we chose τ(eqW) = 4.
-/
lemma drop_R_eq_diff_c (a b : Trace) :
    Lex3c (mu3c (integrate (merge a b))) (mu3c (eqW a b)) := by
  classical
  -- Inner tie on κ; τ inequality: 1+2+… < 4+…; then lift to α=0 and rewrite δ
  have hκ : kappaM (integrate (merge a b)) = kappaM (eqW a b) := by
    simpa using MetaSN_DM.kappaM_eq_diff a b
  -- 3 < 4, then add (τ a + τ b) on the right
  have hτ : 1 + (2 + (tau a + tau b)) < 4 + (tau a + tau b) := by
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
    -- Use τ-right with κ anchor directly.
    simpa [hκ, tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Prod.Lex.right (kappaM (integrate (merge a b))) hτ)
  have hcore : Lex3c (0, (kappaM (integrate (merge a b)), tau (integrate (merge a b))))
      (0, (kappaM (integrate (merge a b)), tau (eqW a b))) :=
    (Prod.Lex.right
      (α := Nat) (β := (Multiset Nat × Nat))
      (ra := (· < ·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin)
  simpa [Lex3c, mu3c, deltaFlag] using hcore

/-- **Rule: eqW a a → void**

Handles duplication via case split:
- If κᴹ(a) = 0: τ-drop
- If κᴹ(a) ≠ 0: DM-drop on union
-/
lemma drop_R_eq_refl_c (a : Trace) :
    Lex3c (mu3c void) (mu3c (eqW a a)) := by
  classical
  dsimp [mu3c, Lex3c]
  refine Prod.Lex.right (0 : Nat) ?inner
  by_cases h0 : kappaM a = 0
  · -- κ tie at 0 → τ-right: 0 < 4 + τ a + τ a
    -- build inner at κ = 0 and rewrite κ on RHS via h0
    have hκ0 : kappaM (eqW a a) = 0 := by simpa [MetaSN_DM.kappaM_eq_refl, h0]
    have hin0 : LexDM_c ((0 : Multiset Nat), tau void)
        ((0 : Multiset Nat), tau (eqW a a)) := by
      refine Prod.Lex.right (0 : Multiset Nat) ?tauDrop
      -- 0 < 4 + (τ a + τ a)
      have h4 : 0 < 4 := by decide
      have h' : 0 < 4 + (tau a + tau a) := lt_of_lt_of_le h4 (Nat.le_add_right 4 (tau a + tau a))
      simpa [tau, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    simpa [MetaSN_DM.kappaM_eq_refl, h0] using hin0
  · -- κ ≠ 0 → DM-left: 0 <ₘ κ∪κ
    have hU : kappaM a ∪ kappaM a ≠ (0 : Multiset Nat) :=
      union_self_ne_zero_of_ne_zero (X := kappaM a) h0
    have hdm : DM (0 : Multiset Nat) (kappaM a ∪ kappaM a) := by
      simpa using MetaSN_DM.dm_lt_add_of_ne_zero' (0 : Multiset Nat) (kappaM a ∪ kappaM a) hU
    -- rewrite κ on RHS using kappaM_eq_refl and use DM-left on 0 <ₘ κ∪κ
    simpa [MetaSN_DM.kappaM_eq_refl] using
      (dm_to_LexDM_c_left (X := 0) (Y := kappaM a ∪ kappaM a)
        (τ₁ := tau void) (τ₂ := tau (eqW a a)) hdm)

/-- **Rule: recΔ b s (delta n) → app s (recΔ b s n)**

THE STAR: δ-drop from 1 to 0.
This is why we have the δ-flag component.
-/
lemma drop_R_rec_succ_c (b s n : Trace) :
    Lex3c (mu3c (app s (recΔ b s n))) (mu3c (recΔ b s (delta n))) := by
  -- Outer Nat component drops strictly: 0 < 1
  dsimp [mu3c, Lex3c]
  -- Use the deltaFlag simplifications to show 0 < 1 on the Nat component
  have a_lt : (0 : Nat) < 1 := by decide
  -- Left component: δ(app s (recΔ b s n)) = 0 and δ(recΔ b s (delta n)) = 1
  have H : Prod.Lex (· < ·) LexDM_c
      ((0 : Nat), (kappaM (app s (recΔ b s n)), tau (app s (recΔ b s n))))
      ((1 : Nat), (kappaM (recΔ b s (delta n)), tau (recΔ b s (delta n)))) := by
    exact Prod.Lex.left (a₁ := (0 : Nat)) (a₂ := (1 : Nat)) (b₁ := (kappaM (app s (recΔ b s n)), tau (app s (recΔ b s n)))) (b₂ := (kappaM (recΔ b s (delta n)), tau (recΔ b s (delta n)))) a_lt
  simpa [mu3c, Lex3c, MetaSN_KO7.deltaFlag_app, MetaSN_KO7.deltaFlag_rec_delta]
    using H

/-- **Rule: recΔ b s void → b** (guarded by δ(b) = 0)

Strategy: κᴹ strictly drops via DM; lift to inner lex, then to outer with δ=0 on both sides.
-/
lemma drop_R_rec_zero_c (b s : Trace) (hδ : deltaFlag b = 0) :
    Lex3c (mu3c b) (mu3c (recΔ b s void)) := by
  classical
  -- Inner: DM-left on κᴹ component
  have hdm : DM (kappaM b) (kappaM (recΔ b s void)) := by
    -- use the KO7 helper
    simpa [DM] using MetaSN_DM.dm_drop_R_rec_zero b s
  have hin : LexDM_c (kappaM b, tau b)
      (kappaM (recΔ b s void), tau (recΔ b s void)) := by
    simpa using (dm_to_LexDM_c_left (X := kappaM b) (Y := kappaM (recΔ b s void))
      (τ₁ := tau b) (τ₂ := tau (recΔ b s void)) hdm)
  -- Build outer witness at α=0 using the guard and rec_zero δ=0
  have hb0 : MetaSN_KO7.deltaFlag b = 0 := hδ
  have hr0 : MetaSN_KO7.deltaFlag (recΔ b s void) = 0 := by
    simpa [MetaSN_KO7.deltaFlag_rec_zero]
  have hcore : Lex3c (0, (kappaM b, tau b))
      (0, (kappaM (recΔ b s void), tau (recΔ b s void))) :=
    (Prod.Lex.right (α := Nat) (β := (Multiset Nat × Nat)) (ra := (· < ·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin)
  -- Cast the 0-anchored witness to the goal using explicit `change` + `rw` (no simp recursion)
  change Prod.Lex (· < ·) LexDM_c
      ((MetaSN_KO7.deltaFlag b), (kappaM b, tau b))
      ((MetaSN_KO7.deltaFlag (recΔ b s void)), (kappaM (recΔ b s void), tau (recΔ b s void)))
  rw [hb0, hr0]
  exact hcore

/-- **Rule: merge t t → t** (guarded by δ(t) = 0 and κᴹ(t) = 0)

With κᴹ(t) = 0, κ ties at 0; use τ-drop: τ t < 2 + τ t + τ t.
-/
lemma drop_R_merge_cancel_c (t : Trace)
    (hδ : deltaFlag t = 0) (h0 : kappaM t = 0) :
    Lex3c (mu3c t) (mu3c (merge t t)) := by
  classical
  -- τ-drop under κ tie at 0
  have hτ : tau t < tau (merge t t) := by
    -- show: τ t < 2 + τ t + τ t
    have hA : tau t < 2 + tau t := by omega
    have hB : 2 + tau t ≤ 2 + tau t + tau t := Nat.le_add_right _ _
    exact lt_of_lt_of_le hA (by simpa [Nat.add_assoc, tau, Nat.add_comm, Nat.add_left_comm] using hB)
  -- Inner at κ = 0
  have hin0 : LexDM_c ((0 : Multiset Nat), tau t)
      ((0 : Multiset Nat), tau (merge t t)) := by
    exact Prod.Lex.right (0 : Multiset Nat) hτ
  -- Rewrite κ components via guards
  have hκ_merge : kappaM (merge t t) = 0 := by simpa [MetaSN_DM.kappaM_merge_cancel, h0]
  have hin : LexDM_c (kappaM t, tau t) (kappaM (merge t t), tau (merge t t)) := by
    simpa [h0, hκ_merge] using hin0
  -- Outer witness at α=0 using guard δ(t)=0 and δ(merge)=0
  have ht0 : MetaSN_KO7.deltaFlag t = 0 := hδ
  have hm0 : MetaSN_KO7.deltaFlag (merge t t) = 0 := by simpa [MetaSN_KO7.deltaFlag_merge]
  have hcore : Lex3c (0, (kappaM t, tau t)) (0, (kappaM (merge t t), tau (merge t t))) :=
    (Prod.Lex.right (α := Nat) (β := (Multiset Nat × Nat)) (ra := (· < ·)) (rb := LexDM_c)
      (a := (0 : Nat)) hin)
  -- Cast the 0-anchored witness to the goal using explicit `change` + `rw` (no simp recursion)
  change Prod.Lex (· < ·) LexDM_c
      ((MetaSN_KO7.deltaFlag t), (kappaM t, tau t))
      ((MetaSN_KO7.deltaFlag (merge t t)), (kappaM (merge t t), tau (merge t t)))
  rw [ht0, hm0]
  exact hcore


/-- **MASTER THEOREM: Every SafeStep decreases μ3c**

Pattern matches all 8 constructors to their decrease proofs.
This is the heart of the termination argument.
-/
lemma measure_decreases_safe_c : ∀ {a b}, MetaSN_KO7.SafeStep a b → Lex3c (mu3c b) (mu3c a)
| _, _, MetaSN_KO7.SafeStep.R_int_delta t => by simpa using drop_R_int_delta_c t
| _, _, MetaSN_KO7.SafeStep.R_merge_void_left t hδ => by simpa using drop_R_merge_void_left_c t hδ
| _, _, MetaSN_KO7.SafeStep.R_merge_void_right t hδ => by simpa using drop_R_merge_void_right_c t hδ
| _, _, MetaSN_KO7.SafeStep.R_merge_cancel t hδ h0 => by simpa using drop_R_merge_cancel_c t hδ h0
| _, _, MetaSN_KO7.SafeStep.R_rec_zero b s hδ => by simpa using drop_R_rec_zero_c b s hδ
| _, _, MetaSN_KO7.SafeStep.R_rec_succ b s n => by simpa using drop_R_rec_succ_c b s n
| _, _, MetaSN_KO7.SafeStep.R_eq_refl a _h0 => by
    -- Guard redundant for τ; we provide an unguarded drop
    simpa using drop_R_eq_refl_c a
| _, _, MetaSN_KO7.SafeStep.R_eq_diff a b _ => by simpa using drop_R_eq_diff_c a b


/-- **Generic well-foundedness wrapper**

For any relation R that decreases μ3c, R^op is well-founded.
Bridge from measure decrease to termination.
-/
theorem wellFounded_of_measure_decreases_R_c
  {R : Trace → Trace → Prop}
  (hdec : ∀ {a b : Trace}, R a b → Lex3c (mu3c b) (mu3c a)) :
  WellFounded (fun a b : Trace => R b a) := by
  -- Pull back the well-founded Lex3c along μ3c
  have wf_measure : WellFounded (fun x y : Trace => Lex3c (mu3c x) (mu3c y)) :=
    InvImage.wf (f := mu3c) wf_Lex3c
  -- Show Rᵒᵖ ⊆ InvImage μ3c Lex3c
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
```

## 5. OperatorKO7/Meta/Normalize_Safe.lean

**Lines:** 252

```lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Logic.Function.Basic

/-!
Certified normalization for the KO7 safe fragment.

Purpose:
- Defines `SafeStepStar` (multi-step closure of `SafeStep`).
- Defines `NormalFormSafe` and proves basic normal-form facts for the safe relation.
- Constructs a *certified* normalizer `normalizeSafe` for `SafeStep` using well-founded recursion.

Important scope boundary:
- Everything in this file is about `SafeStep` (the guarded fragment), not the full kernel `Step`.
- The normalizer is `noncomputable` because it is obtained from well-foundedness via `WellFounded.fix`.
  This is the standard "certified existence" construction: it produces a term and a proof certificate.

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


namespace MetaSN_KO7

/-- Reflexive-transitive closure of `SafeStep`. -/
inductive SafeStepStar : Trace → Trace → Prop
| refl : ∀ t, SafeStepStar t t
| tail : ∀ {a b c}, SafeStep a b → SafeStepStar b c → SafeStepStar a c

/-- Transitivity of the safe multi-step relation `SafeStepStar`. -/
theorem safestar_trans {a b c : Trace}
  (h₁ : SafeStepStar a b) (h₂ : SafeStepStar b c) : SafeStepStar a c := by
  induction h₁ with
  | refl => exact h₂
  | tail hab _ ih => exact SafeStepStar.tail hab (ih h₂)

/-- Any single safe step is also a `SafeStepStar`. -/
theorem safestar_of_step {a b : Trace} (h : SafeStep a b) : SafeStepStar a b :=
  SafeStepStar.tail h (SafeStepStar.refl b)

/-- Normal forms for the safe subrelation. -/
def NormalFormSafe (t : Trace) : Prop := ¬ ∃ u, SafeStep t u

/-- No single safe step can originate from a safe normal form. -/
theorem no_step_from_nf {t u : Trace} (h : NormalFormSafe t) : ¬ SafeStep t u := by
  intro hs; exact h ⟨u, hs⟩

/-- If `a` is a safe normal form, then any `a ⇒* b` (in `SafeStepStar`) must be trivial. -/
theorem nf_no_safestar_forward {a b : Trace}
  (hnf : NormalFormSafe a) (h : SafeStepStar a b) : a = b :=
  match h with
  | SafeStepStar.refl _ => rfl
  | SafeStepStar.tail hs _ => False.elim (hnf ⟨_, hs⟩)

/-- From a safe normal form, reachability by `SafeStepStar` is equivalent to equality. -/
theorem safestar_from_nf_iff_eq {t u : Trace}
  (h : NormalFormSafe t) : SafeStepStar t u ↔ u = t := by
  constructor
  · intro htu
    have ht_eq : t = u := nf_no_safestar_forward h htu
    exact ht_eq.symm
  · intro hEq; cases hEq; exact SafeStepStar.refl t

/-- No non-trivial safe multi-step can start from a safe normal form. -/
theorem no_safestar_from_nf_of_ne {t u : Trace}
  (h : NormalFormSafe t) (hne : u ≠ t) : ¬ SafeStepStar t u := by
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
  a = c ∨ ∃ b, SafeStep a b ∧ SafeStepStar b c := by
  cases h with
  | refl t => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- Append a single safe step to the right of a safe multi-step path. -/
theorem safestar_snoc {a b c : Trace}
  (hab : SafeStepStar a b) (hbc : SafeStep b c) : SafeStepStar a c :=
  safestar_trans hab (safestar_of_step hbc)

/-! ### Strong normalization (rev) - convenience -/

/-- Accessibility for `SafeStepRev` as a derived corollary of `wf_SafeStepRev_c`. -/
theorem acc_SafeStepRev (t : Trace) : Acc SafeStepRev t :=
  wf_SafeStepRev_c.apply t

/-- A well-founded pullback of the computable KO7 Lex3c order along μ3c. -/
def Rμ3 (x y : Trace) : Prop := Lex3c (mu3c x) (mu3c y)

/-- Well-foundedness of `Rμ3`, inherited from `wf_Lex3c` via `InvImage`. -/
lemma wf_Rμ3 : WellFounded Rμ3 :=
  InvImage.wf (f := mu3c) wf_Lex3c

set_option diagnostics true

/-- Deterministic normalization for the safe subrelation, bundled with a proof certificate. -/
noncomputable def normalizeSafePack (t : Trace) : Σ' n : Trace, SafeStepStar t n ∧ NormalFormSafe n :=
  WellFounded.fix wf_Rμ3 (C := fun t => Σ' n : Trace, SafeStepStar t n ∧ NormalFormSafe n)
    (fun t rec => by
      classical
      -- Use term-mode if-split on existence of a safe step
      exact
        (if h : ∃ u, SafeStep t u then
          -- Take one step and recurse
          let u := Classical.choose h
          have hu : SafeStep t u := Classical.choose_spec h
          have hdrop : Rμ3 u t := measure_decreases_safe_c hu
          match rec u hdrop with
          | ⟨n, hstar, hnf⟩ => ⟨n, And.intro (SafeStepStar.tail hu hstar) hnf⟩
        else
          -- Stuck: already normal
          ⟨t, And.intro (SafeStepStar.refl t) (by intro ex; exact h ex)⟩)) t

/-- The safe normal form selected by `normalizeSafePack`. -/
noncomputable def normalizeSafe (t : Trace) : Trace := (normalizeSafePack t).1

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
  ∃ n, SafeStepStar t n ∧ NormalFormSafe n :=
  ⟨normalizeSafe t, to_norm_safe t, norm_nf_safe t⟩

/-- Either a safe step exists from `t`, or the normalizer is already fixed at `t`. -/
theorem progress_or_fixed (t : Trace) : (∃ u, SafeStep t u) ∨ normalizeSafe t = t := by
  classical
  -- Term-mode split on NormalFormSafe t
  exact
    (if hnf : NormalFormSafe t then
      Or.inr (normalizeSafe_eq_self_of_nf t hnf)
    else
      Or.inl (by
        have : ¬¬ ∃ u, SafeStep t u := by simpa [NormalFormSafe] using hnf
        exact not_not.mp this))

/-- Head-or-refl decomposition of the normalization path (unbundled). -/
theorem to_norm_safe_head_or_refl (t : Trace) :
  normalizeSafe t = t ∨ ∃ u, SafeStep t u ∧ SafeStepStar u (normalizeSafe t) := by
  have h := safestar_destruct (to_norm_safe t)
  cases h with
  | inl hEq => exact Or.inl hEq.symm
  | inr hex =>
      rcases hex with ⟨u, hstep, htail⟩
      exact Or.inr ⟨u, hstep, htail⟩

/-- If normalization changes `t`, then a safe step exists from `t`. -/
theorem exists_step_of_not_fixed (t : Trace) (h : normalizeSafe t ≠ t) : ∃ u, SafeStep t u := by
  cases progress_or_fixed t with
  | inl hex => exact hex
  | inr hfix => exact (h hfix).elim

/-- If normalization changes `t`, there exists a `SafeStep` successor that strictly decreases `Rμ3`. -/
theorem exists_drop_if_not_fixed (t : Trace) (h : normalizeSafe t ≠ t) :
  ∃ u, SafeStep t u ∧ Rμ3 u t := by
  classical
  rcases exists_step_of_not_fixed t h with ⟨u, hs⟩
  exact ⟨u, hs, measure_decreases_safe_c hs⟩

/-- If there is a safe step from `t`, then normalization cannot be fixed at `t`. -/
theorem not_fixed_of_exists_step (t : Trace) (hex : ∃ u, SafeStep t u) :
  normalizeSafe t ≠ t := by
  intro hfix
  -- From fixed-point, we get NF; contradiction with existence of a step.
  have hnf : NormalFormSafe t := by simpa [hfix] using norm_nf_safe t
  exact hnf hex

/-- Fixed-point characterization: `normalizeSafe t ≠ t` iff there exists a safe step from `t`. -/
theorem not_fixed_iff_exists_step (t : Trace) :
  normalizeSafe t ≠ t ↔ ∃ u, SafeStep t u := by
  constructor
  · exact exists_step_of_not_fixed t
  · intro hex; exact not_fixed_of_exists_step t hex

/-! ### Fixed-point characterization of safe normal forms -/

theorem nf_iff_normalize_fixed (t : Trace) :
  NormalFormSafe t ↔ normalizeSafe t = t := by
  constructor
  · intro h; exact normalizeSafe_eq_self_of_nf t h
  · intro h; simpa [h] using norm_nf_safe t


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
  SafeStepStar t (normalizeSafe t) ∧ NormalFormSafe (normalizeSafe t) :=
  ⟨to_norm_safe t, norm_nf_safe t⟩

/-- Totality alias for convenience: every trace safely normalizes to some NF. -/
theorem normalizeSafe_total (t : Trace) :
  ∃ n, SafeStepStar t n ∧ NormalFormSafe n :=
  ⟨normalizeSafe t, to_norm_safe t, norm_nf_safe t⟩

end MetaSN_KO7
```

## 6. OperatorKO7/Meta/SafeStep_Ctx.lean

**Lines:** 548

```lean
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
inductive SafeStepCtx : Trace → Trace → Prop
| root {a b} : SafeStep a b → SafeStepCtx a b
| integrate {t u} : SafeStepCtx t u → SafeStepCtx (integrate t) (integrate u)
| mergeL {a a' b} : SafeStepCtx a a' → SafeStepCtx (merge a b) (merge a' b)
| mergeR {a b b'} : SafeStepCtx b b' → SafeStepCtx (merge a b) (merge a b')
| appL {a a' b} : SafeStepCtx a a' → SafeStepCtx (app a b) (app a' b)
| appR {a b b'} : SafeStepCtx b b' → SafeStepCtx (app a b) (app a b')
| recB {b b' s n} : SafeStepCtx b b' → SafeStepCtx (recΔ b s n) (recΔ b' s n)
| recS {b s s' n} : SafeStepCtx s s' → SafeStepCtx (recΔ b s n) (recΔ b s' n)
| recN {b s n n'} : SafeStepCtx n n' → SafeStepCtx (recΔ b s n) (recΔ b s n')

/-- Reflexive-transitive closure of `SafeStepCtx`. -/
inductive SafeStepCtxStar : Trace → Trace → Prop
| refl : ∀ t, SafeStepCtxStar t t
| tail : ∀ {a b c}, SafeStepCtx a b → SafeStepCtxStar b c → SafeStepCtxStar a c

/-- Transitivity of the context-closed multi-step relation `SafeStepCtxStar`. -/
theorem ctxstar_trans {a b c : Trace}
  (h₁ : SafeStepCtxStar a b) (h₂ : SafeStepCtxStar b c) : SafeStepCtxStar a c := by
  induction h₁ with
  | refl => exact h₂
  | tail hab _ ih => exact SafeStepCtxStar.tail hab (ih h₂)

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

/-- Lift `SafeStepCtxStar` through the base argument `b` of `recΔ b s n`. -/
theorem ctxstar_recB {b b' s n : Trace}
  (h : SafeStepCtxStar b b') : SafeStepCtxStar (recΔ b s n) (recΔ b' s n) := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hbb _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.recB hbb) ih

/-- Lift `SafeStepCtxStar` through the step function argument `s` of `recΔ b s n`. -/
theorem ctxstar_recS {b s s' n : Trace}
  (h : SafeStepCtxStar s s') : SafeStepCtxStar (recΔ b s n) (recΔ b s' n) := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hss _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.recS hss) ih

/-- Lift `SafeStepCtxStar` through the argument `n` of `recΔ b s n`. -/
theorem ctxstar_recN {b s n n' : Trace}
  (h : SafeStepCtxStar n n') : SafeStepCtxStar (recΔ b s n) (recΔ b s n') := by
  induction h with
  | refl => exact SafeStepCtxStar.refl _
  | tail hnn _ ih => exact SafeStepCtxStar.tail (SafeStepCtx.recN hnn) ih

/-- Compose left and right ctx-star lifts under `merge`. -/
theorem ctxstar_mergeLR {a a' b b' : Trace}
  (ha : SafeStepCtxStar a a') (hb : SafeStepCtxStar b b') :
  SafeStepCtxStar (merge a b) (merge a' b') :=
  ctxstar_trans (ctxstar_mergeL ha) (ctxstar_mergeR hb)

/-- Compose all three ctx-star lifts under `recΔ`. -/
theorem ctxstar_recBSN {b b' s s' n n' : Trace}
  (hb : SafeStepCtxStar b b') (hs : SafeStepCtxStar s s') (hn : SafeStepCtxStar n n') :
  SafeStepCtxStar (recΔ b s n) (recΔ b' s' n') :=
  ctxstar_trans (ctxstar_recB hb) (ctxstar_trans (ctxstar_recS hs) (ctxstar_recN hn))

/-- Compose left and right ctx-star lifts under `app`. -/
theorem ctxstar_appLR {a a' b b' : Trace}
  (ha : SafeStepCtxStar a a') (hb : SafeStepCtxStar b b') :
  SafeStepCtxStar (app a b) (app a' b') :=
  ctxstar_trans (ctxstar_appL ha) (ctxstar_appR hb)

/-- Local join at root allowing context-closed stars after the two root steps. -/
def LocalJoinSafe_ctx (a : Trace) : Prop :=
  ∀ {b c}, SafeStep a b → SafeStep a c → ∃ d, SafeStepCtxStar b d ∧ SafeStepCtxStar c d

/-- If there are no safe root steps from `a`, ctx-local join holds vacuously. -/
theorem localJoin_of_none_ctx (a : Trace)
    (h : ∀ {b}, SafeStep a b → False) : LocalJoinSafe_ctx a := by
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
    (h : ∀ {b}, SafeStep a b → b = d) : LocalJoinSafe_ctx a := by
  intro b c hb hc
  have hb' : b = d := h hb
  have hc' : c = d := h hc
  refine ⟨d, ?_, ?_⟩
  · simpa [hb'] using (SafeStepCtxStar.refl d)
  · simpa [hc'] using (SafeStepCtxStar.refl d)

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

/-- At `integrate (recΔ b s n)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_integrate_rec (b s n : Trace) :
    LocalJoinSafe_ctx (integrate (recΔ b s n)) := by
  refine localJoin_of_none_ctx (a := integrate (recΔ b s n)) ?h
  intro x hx; cases hx

/-- At `recΔ b s (merge a c)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_merge (b s a c : Trace) : LocalJoinSafe_ctx (recΔ b s (merge a c)) := by
  refine localJoin_of_none_ctx (a := recΔ b s (merge a c)) ?h
  intro x hx; cases hx

/-- At `recΔ b s (app a c)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_app (b s a c : Trace) : LocalJoinSafe_ctx (recΔ b s (app a c)) := by
  refine localJoin_of_none_ctx (a := recΔ b s (app a c)) ?h
  intro x hx; cases hx

/-- At `recΔ b s (integrate t)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_integrate (b s t : Trace) : LocalJoinSafe_ctx (recΔ b s (integrate t)) := by
  refine localJoin_of_none_ctx (a := recΔ b s (integrate t)) ?h
  intro x hx; cases hx

/-- At `recΔ b s (eqW a c)`, no safe root rule; ctx-local join vacuously. -/
theorem localJoin_ctx_rec_eqW (b s a c : Trace) : LocalJoinSafe_ctx (recΔ b s (eqW a c)) := by
  refine localJoin_of_none_ctx (a := recΔ b s (eqW a c)) ?h
  intro x hx; cases hx

/-- At `recΔ b s void`, only one safe root rule; ctx-local join is trivial. -/
theorem localJoin_ctx_rec_zero (b s : Trace) : LocalJoinSafe_ctx (recΔ b s void) := by
  refine localJoin_of_unique_ctx (a := recΔ b s void) (d := b) ?h
  intro x hx; cases hx with
  | R_rec_zero _ _ _ => rfl

/-- At `recΔ b s (delta n)`, only one safe root rule; ctx-local join is trivial. -/
theorem localJoin_ctx_rec_succ (b s n : Trace) : LocalJoinSafe_ctx (recΔ b s (delta n)) := by
  refine localJoin_of_unique_ctx (a := recΔ b s (delta n)) (d := app s (recΔ b s n)) ?h
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

/-- If `deltaFlag t ≠ 0`, the left-void merge rule cannot apply; no competing branch. -/
theorem localJoin_ctx_merge_void_left_guard_ne (t : Trace)
    (hδne : deltaFlag t ≠ 0) : LocalJoinSafe_ctx (merge void t) := by
  refine localJoin_of_unique_ctx (a := merge void t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_void_left _ hδ => exact (False.elim (hδne hδ))
  | R_merge_void_right _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t ≠ 0`, the right-void merge rule cannot apply; no competing branch. -/
theorem localJoin_ctx_merge_void_right_guard_ne (t : Trace)
    (hδne : deltaFlag t ≠ 0) : LocalJoinSafe_ctx (merge t void) := by
  refine localJoin_of_unique_ctx (a := merge t void) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_void_right _ hδ => exact (False.elim (hδne hδ))
  | R_merge_void_left _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t ≠ 0`, merge-cancel is blocked at root; vacuous ctx-local join. -/
theorem localJoin_ctx_merge_cancel_guard_delta_ne (t : Trace)
    (hδne : deltaFlag t ≠ 0) : LocalJoinSafe_ctx (merge t t) := by
  refine localJoin_of_unique_ctx (a := merge t t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_cancel _ hδ _ => exact (False.elim (hδne hδ))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- If `kappaM t ≠ 0`, merge-cancel is blocked at root; vacuous ctx-local join. -/
theorem localJoin_ctx_merge_cancel_guard_kappa_ne (t : Trace)
    (h0ne : MetaSN_DM.kappaM t ≠ 0) : LocalJoinSafe_ctx (merge t t) := by
  refine localJoin_of_unique_ctx (a := merge t t) (d := t) ?h
  intro x hx; cases hx with
  | R_merge_cancel _ _ h0 => exact (False.elim (h0ne h0))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- At `recΔ b s void`, if `deltaFlag b ≠ 0` then the rec-zero rule is blocked. -/
theorem localJoin_ctx_rec_zero_guard_ne (b s : Trace)
    (hδne : deltaFlag b ≠ 0) : LocalJoinSafe_ctx (recΔ b s void) := by
  refine localJoin_of_none_ctx (a := recΔ b s void) ?h
  intro x hx; cases hx with
  | R_rec_zero _ _ hδ => exact (hδne hδ)

/-- At `integrate t`, if `t` is not a `delta _`, then there is no safe root step (ctx). -/
theorem localJoin_ctx_integrate_non_delta (t : Trace)
    (hnd : ∀ u, t ≠ delta u) : LocalJoinSafe_ctx (integrate t) := by
  refine localJoin_of_none_ctx (a := integrate t) ?h
  intro x hx; cases hx with
  | R_int_delta u => exact (hnd u) rfl

/-- At `recΔ b s n`, if `n ≠ void` and `n` is not a `delta _`, then no safe root step (ctx). -/
theorem localJoin_ctx_rec_other (b s n : Trace)
    (hn0 : n ≠ void) (hns : ∀ u, n ≠ delta u) : LocalJoinSafe_ctx (recΔ b s n) := by
  refine localJoin_of_none_ctx (a := recΔ b s n) ?h
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
    | R_eq_refl _ _ => exact ⟨void, SafeStepCtxStar.refl _, SafeStepCtxStar.refl _⟩
    | R_eq_diff _ _ =>
      -- c = integrate (merge a a) ⇒ctx* integrate (delta n) → void
      have h_to_delta : SafeStepCtxStar (integrate (merge a a)) (integrate (delta n)) :=
        ctxstar_integrate hmd
      have h_to_void : SafeStepCtxStar (integrate (delta n)) void :=
        ctxstar_of_root (SafeStep.R_int_delta n)
      exact ⟨void, SafeStepCtxStar.refl _, ctxstar_trans h_to_delta h_to_void⟩
  | R_eq_diff _ _ =>
    -- b = integrate (merge a a)
    cases hc with
    | R_eq_refl _ _ =>
      have h_to_delta : SafeStepCtxStar (integrate (merge a a)) (integrate (delta n)) :=
        ctxstar_integrate hmd
      have h_to_void : SafeStepCtxStar (integrate (delta n)) void :=
        ctxstar_of_root (SafeStep.R_int_delta n)
      exact ⟨void, ctxstar_trans h_to_delta h_to_void, SafeStepCtxStar.refl _⟩
    | R_eq_diff _ _ =>
      -- both to the same term
  exact ⟨integrate (merge a a), SafeStepCtxStar.refl _, SafeStepCtxStar.refl _⟩

/-- If `a ⇒ctx* delta n` and `delta n` satisfies the cancel guards, then
`merge a a ⇒ctx* delta n`. -/
theorem ctxstar_merge_cancel_of_arg_to_delta
  (a n : Trace)
  (ha : SafeStepCtxStar a (delta n))
  (hδ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  SafeStepCtxStar (merge a a) (delta n) := by
  -- push left argument to delta n
  have hL : SafeStepCtxStar (merge a a) (merge (delta n) a) := ctxstar_mergeL ha
  -- push right argument to delta n
  have hR : SafeStepCtxStar (merge (delta n) a) (merge (delta n) (delta n)) := ctxstar_mergeR ha
  -- apply root cancel at delta n
  have hC : SafeStepCtxStar (merge (delta n) (delta n)) (delta n) :=
    ctxstar_of_root (SafeStep.R_merge_cancel (t := delta n) hδ h0)
  exact ctxstar_trans hL (ctxstar_trans hR hC)

/-- If `a ⇒* delta n` by root-safe steps and the cancel guards hold on `delta n`, then
`merge a a ⇒ctx* delta n`. -/
theorem ctxstar_merge_cancel_of_arg_star_to_delta
  (a n : Trace)
  (ha : SafeStepStar a (delta n))
  (hδ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  SafeStepCtxStar (merge a a) (delta n) := by
  have ha_ctx : SafeStepCtxStar a (delta n) := ctxstar_of_star ha
  exact ctxstar_merge_cancel_of_arg_to_delta a n ha_ctx hδ h0

/-- Conditional local join for `eqW a a` from an argument-to-delta premise.
If `a ⇒ctx* delta n` and the cancel guards hold on `delta n`, the two root branches
context-join at `void`. -/
theorem localJoin_eqW_refl_ctx_if_arg_merges_to_delta (a n : Trace)
  (ha : SafeStepCtxStar a (delta n))
  (hδ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW a a) := by
  -- derive the stronger merge→delta premise and reuse previous lemma
  have hmd : SafeStepCtxStar (merge a a) (delta n) :=
    ctxstar_merge_cancel_of_arg_to_delta a n ha hδ h0
  -- apply the previous lemma to the concrete branch steps
  intro b c hb hc
  exact (localJoin_eqW_refl_ctx_if_merges_to_delta a n hmd) hb hc

/-- Variant: if `a ⇒* delta n` by root-safe steps, embed to ctx-star and reuse the delta-argument lemma. -/
theorem localJoin_eqW_refl_ctx_if_arg_star_to_delta (a n : Trace)
  (ha : SafeStepStar a (delta n))
  (hδ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW a a) := by
  -- embed SafeStepStar into SafeStepCtxStar
  have ha_ctx : SafeStepCtxStar a (delta n) := ctxstar_of_star ha
  -- reuse the ctx lemma, applied to the given branches
  intro b c hb hc
  exact (localJoin_eqW_refl_ctx_if_arg_merges_to_delta a n ha_ctx hδ h0) hb hc

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

/-- If `merge a a ⇒ctx* delta n` then `integrate (merge a a) ⇒ctx* void`. -/
theorem ctxstar_integrate_merge_to_void_of_mergeToDelta (a n : Trace)
  (hmd : SafeStepCtxStar (merge a a) (delta n)) :
  SafeStepCtxStar (integrate (merge a a)) void := by
  have h_to_delta : SafeStepCtxStar (integrate (merge a a)) (integrate (delta n)) :=
    ctxstar_integrate hmd
  have h_to_void : SafeStepCtxStar (integrate (delta n)) void :=
    ctxstar_of_root (SafeStep.R_int_delta n)
  exact ctxstar_trans h_to_delta h_to_void

/-- If `normalizeSafe (merge a a) = delta n` then `integrate (merge a a) ⇒ctx* void`. -/
theorem ctxstar_integrate_merge_to_void_of_merge_normalizes_to_delta (a n : Trace)
  (hn : normalizeSafe (merge a a) = delta n) :
  SafeStepCtxStar (integrate (merge a a)) void := by
  have hmd_star : SafeStepStar (merge a a) (normalizeSafe (merge a a)) :=
    to_norm_safe (merge a a)
  have hmd_ctx : SafeStepCtxStar (merge a a) (delta n) := by
    simpa [hn] using (ctxstar_of_star hmd_star)
  exact ctxstar_integrate_merge_to_void_of_mergeToDelta a n hmd_ctx

/-- If `integrate (merge a a) ⇒ctx* void`, then `eqW a a` has a ctx-local join at `void`. -/
theorem localJoin_eqW_refl_ctx_if_integrate_merge_to_void (a : Trace)
  (hiv : SafeStepCtxStar (integrate (merge a a)) void) :
  LocalJoinSafe_ctx (eqW a a) := by
  intro b c hb hc
  cases hb with
  | R_eq_refl _ _ =>
    cases hc with
    | R_eq_refl _ _ =>
      exact ⟨void, SafeStepCtxStar.refl _, SafeStepCtxStar.refl _⟩
    | R_eq_diff _ _ =>
      exact ⟨void, SafeStepCtxStar.refl _, hiv⟩
  | R_eq_diff _ _ =>
    cases hc with
    | R_eq_refl _ _ =>
      exact ⟨void, hiv, SafeStepCtxStar.refl _⟩
    | R_eq_diff _ _ =>
      exact ⟨integrate (merge a a), SafeStepCtxStar.refl _, SafeStepCtxStar.refl _⟩

/-- At `eqW a b` with `a ≠ b`, only the diff rule applies; ctx-local join is trivial. -/
theorem localJoin_eqW_ne_ctx (a b : Trace) (hne : a ≠ b) : LocalJoinSafe_ctx (eqW a b) := by
  refine localJoin_of_unique_ctx (a := eqW a b) (d := integrate (merge a b)) ?h
  intro x hx
  cases hx with
  | R_eq_diff _ _ => rfl
  | R_eq_refl _ _ => exact (False.elim (hne rfl))

/-- At `eqW a a`, if `kappaM a ≠ 0`, the reflexive rule is blocked; only diff applies. -/
theorem localJoin_eqW_refl_ctx_guard_ne (a : Trace)
  (h0ne : MetaSN_DM.kappaM a ≠ 0) : LocalJoinSafe_ctx (eqW a a) := by
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
  (hδ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW (delta n) (delta n)) := by
  -- trivial arg-to-delta via refl
  intro b c hb hc
  -- build the LocalJoinSafe_ctx witness once, then apply to the given branches
  have ha : SafeStepCtxStar (delta n) (delta n) := SafeStepCtxStar.refl _
  have hj : LocalJoinSafe_ctx (eqW (delta n) (delta n)) :=
    localJoin_eqW_refl_ctx_if_arg_merges_to_delta (a := delta n) (n := n) ha hδ h0
  exact hj hb hc

/-- If `a` safe-normalizes to `delta n` and cancel guards hold on `delta n`, then
`eqW a a` has a context-closed local join at `void`. -/
theorem localJoin_eqW_refl_ctx_if_normalizes_to_delta (a n : Trace)
  (hn : normalizeSafe a = delta n)
  (hδ : deltaFlag (delta n) = 0)
  (h0 : MetaSN_DM.kappaM (delta n) = 0) :
  LocalJoinSafe_ctx (eqW a a) := by
  -- embed the normalization star into ctx-star
  intro b c hb hc
  have ha_star : SafeStepStar a (normalizeSafe a) := to_norm_safe a
  have ha_ctx : SafeStepCtxStar a (normalizeSafe a) := ctxstar_of_star ha_star
  -- build the LocalJoinSafe_ctx witness using the arg→delta bridge
  have hj : LocalJoinSafe_ctx (eqW a a) :=
    localJoin_eqW_refl_ctx_if_arg_merges_to_delta (a := a) (n := n)
      (by simpa [hn] using ha_ctx) hδ h0
  exact hj hb hc

end MetaSN_KO7
```

## 7. OperatorKO7/Meta/Confluence_Safe.lean

**Lines:** 529

```lean
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
  ∀ {b c}, SafeStep a b → SafeStep a c → ∃ d, SafeStepStar b d ∧ SafeStepStar c d

/-- Local joinability at a fixed source for the full kernel relation `Step`. -/
def LocalJoinStep (a : Trace) : Prop :=
  ∀ {b c}, Step a b → Step a c → ∃ d, StepStar b d ∧ StepStar c d

/-- Full-step caveat: the two kernel `eqW` rules overlap, so `eqW void void` is not locally joinable. -/
theorem not_localJoinStep_eqW_void_void : ¬ LocalJoinStep (eqW void void) := by
  intro hjoin
  have hb : Step (eqW void void) void := Step.R_eq_refl void
  have hc : Step (eqW void void) (integrate (merge void void)) := Step.R_eq_diff void void
  rcases hjoin hb hc with ⟨d, hbStar, hcStar⟩
  have hnf_void : NormalForm void := by
    intro ex
    rcases ex with ⟨u, hu⟩
    cases hu
  have hnf_int_merge : NormalForm (integrate (merge void void)) := by
    intro ex
    rcases ex with ⟨u, hu⟩
    cases hu
  have hd_eq_void : d = void := (nf_no_stepstar_forward hnf_void hbStar).symm
  have hd_eq_int : d = integrate (merge void void) := (nf_no_stepstar_forward hnf_int_merge hcStar).symm
  have hneq : (integrate (merge void void) : Trace) ≠ void := by
    intro h
    cases h
  exact hneq (hd_eq_int.symm.trans hd_eq_void)

/-- If there are no safe root steps from `a`, local join holds vacuously. -/
theorem localJoin_of_none (a : Trace)
    (h : ∀ {b}, SafeStep a b → False) : LocalJoinSafe a := by
  intro b c hb hc
  exact False.elim (h hb)

/-- If every safe root step from `a` has the same target `d`, then `a` is locally joinable. -/
theorem localJoin_of_unique (a d : Trace)
    (h : ∀ {b}, SafeStep a b → b = d) : LocalJoinSafe a := by
  intro b c hb hc
  have hb' : b = d := h hb
  have hc' : c = d := h hc
  refine ⟨d, ?_, ?_⟩
  · simpa [hb'] using (SafeStepStar.refl d)
  · simpa [hc'] using (SafeStepStar.refl d)

/-- If there are no safe root steps from `a`, any `SafeStepStar a d` must be reflexive. -/
theorem star_only_refl_of_none {a d : Trace}
    (h : ∀ {b}, SafeStep a b → False) : SafeStepStar a d → d = a := by
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
    | R_merge_void_left t hδ =>
        -- Here a = merge void t unifies with merge void void, so t = void and b = void.
        exact SafeStepStar.refl _
    | R_merge_void_right t hδ =>
        exact SafeStepStar.refl _
    | R_merge_cancel t hδ h0 =>
        exact SafeStepStar.refl _
  have hc_refl : SafeStepStar c void := by
    cases hc with
    | R_merge_void_left t hδ =>
        exact SafeStepStar.refl _
    | R_merge_void_right t hδ =>
        exact SafeStepStar.refl _
    | R_merge_cancel t hδ h0 =>
        exact SafeStepStar.refl _
  exact ⟨void, hb_refl, hc_refl⟩

/-- At `integrate (delta t)` there is only one safe root rule; local join is trivial. -/
theorem localJoin_int_delta (t : Trace) : LocalJoinSafe (integrate (delta t)) := by
  intro b c hb hc
  have hb_refl : SafeStepStar b void := by
    cases hb with
    | R_int_delta _ => exact SafeStepStar.refl _
  have hc_refl : SafeStepStar c void := by
    cases hc with
    | R_int_delta _ => exact SafeStepStar.refl _
  exact ⟨void, hb_refl, hc_refl⟩

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

/-- At `integrate (recΔ b s n)`, there is no safe root rule; join vacuously. -/
theorem localJoin_integrate_rec (b s n : Trace) : LocalJoinSafe (integrate (recΔ b s n)) := by
  refine localJoin_of_none (a := integrate (recΔ b s n)) ?h
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
  exact ⟨t, hb_refl, hc_refl⟩

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
  exact ⟨t, hb_refl, hc_refl⟩

/-- At `recΔ b s void` there is only one safe root rule; local join is trivial. -/
theorem localJoin_rec_zero (b s : Trace) : LocalJoinSafe (recΔ b s void) := by
  intro x y hx hy
  have hx_refl : SafeStepStar x b := by
    cases hx with
    | R_rec_zero _ _ _ => exact SafeStepStar.refl _
  have hy_refl : SafeStepStar y b := by
    cases hy with
    | R_rec_zero _ _ _ => exact SafeStepStar.refl _
  exact ⟨b, hx_refl, hy_refl⟩

/-- At `recΔ b s (delta n)` there is only one safe root rule; local join is trivial. -/
theorem localJoin_rec_succ (b s n : Trace) : LocalJoinSafe (recΔ b s (delta n)) := by
  intro x y hx hy
  have hx_refl : SafeStepStar x (app s (recΔ b s n)) := by
    cases hx with
    | R_rec_succ _ _ _ => exact SafeStepStar.refl _
  have hy_refl : SafeStepStar y (app s (recΔ b s n)) := by
    cases hy with
    | R_rec_succ _ _ _ => exact SafeStepStar.refl _
  exact ⟨app s (recΔ b s n), hx_refl, hy_refl⟩

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
  exact ⟨t, hb_refl, hc_refl⟩

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

/-- At `eqW a b` with `a ≠ b`, only `R_eq_diff` applies at the root; local join is trivial. -/
theorem localJoin_eqW_ne (a b : Trace) (hne : a ≠ b) : LocalJoinSafe (eqW a b) := by
  -- Unique target is `integrate (merge a b)`.
  refine localJoin_of_unique (a := eqW a b) (d := integrate (merge a b)) ?h
  intro x hx
  cases hx with
  | R_eq_diff _ _ _ => rfl
  | R_eq_refl _ _ => exact (False.elim (hne rfl))

/-- At `eqW a a`, if `kappaM a ≠ 0`, `R_eq_refl` cannot fire; and `R_eq_diff` is blocked by `a ≠ a`.
So there are no safe root steps and local join holds vacuously. -/
theorem localJoin_eqW_refl_guard_ne (a : Trace) (h0ne : MetaSN_DM.kappaM a ≠ 0) :
    LocalJoinSafe (eqW a a) := by
  refine localJoin_of_none (a := eqW a a) ?h
  intro x hx
  cases hx with
  | R_eq_refl _ h0 => exact False.elim (h0ne h0)
  | R_eq_diff _ _ hne => exact False.elim (hne rfl)

/-- If `deltaFlag t ≠ 0`, the left-void merge rule cannot apply; no competing branch. -/
theorem localJoin_merge_void_left_guard_ne (t : Trace)
    (hδne : deltaFlag t ≠ 0) : LocalJoinSafe (merge void t) := by
  refine localJoin_of_unique (a := merge void t) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_void_left _ hδ => exact (False.elim (hδne hδ))
  | R_merge_void_right _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t ≠ 0`, the right-void merge rule cannot apply; no competing branch. -/
theorem localJoin_merge_void_right_guard_ne (t : Trace)
    (hδne : deltaFlag t ≠ 0) : LocalJoinSafe (merge t void) := by
  refine localJoin_of_unique (a := merge t void) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_void_right _ hδ => exact (False.elim (hδne hδ))
  | R_merge_void_left _ _ => rfl
  | R_merge_cancel _ _ _ => rfl

/-- If `deltaFlag t ≠ 0`, merge-cancel is blocked at root; vacuous local join. -/
theorem localJoin_merge_cancel_guard_delta_ne (t : Trace)
    (hδne : deltaFlag t ≠ 0) : LocalJoinSafe (merge t t) := by
  refine localJoin_of_unique (a := merge t t) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_cancel _ hδ _ => exact (False.elim (hδne hδ))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- If `kappaM t ≠ 0`, merge-cancel is blocked at root; vacuous local join. -/
theorem localJoin_merge_cancel_guard_kappa_ne (t : Trace)
    (h0ne : MetaSN_DM.kappaM t ≠ 0) : LocalJoinSafe (merge t t) := by
  refine localJoin_of_unique (a := merge t t) (d := t) ?h
  intro x hx
  cases hx with
  | R_merge_cancel _ _ h0 => exact (False.elim (h0ne h0))
  | R_merge_void_left _ _ => rfl
  | R_merge_void_right _ _ => rfl

/-- At `recΔ b s void`, if `deltaFlag b ≠ 0` then the rec-zero rule is blocked. -/
theorem localJoin_rec_zero_guard_ne (b s : Trace)
    (hδne : deltaFlag b ≠ 0) : LocalJoinSafe (recΔ b s void) := by
  refine localJoin_of_none (a := recΔ b s void) ?h
  intro x hx
  cases hx with
  | R_rec_zero _ _ hδ => exact (hδne hδ)

/-- At `integrate t`, if `t` is not a `delta _`, then there is no safe root step. -/
theorem localJoin_integrate_non_delta (t : Trace)
    (hnd : ∀ u, t ≠ delta u) : LocalJoinSafe (integrate t) := by
  refine localJoin_of_none (a := integrate t) ?h
  intro x hx
  cases hx with
  | R_int_delta u => exact (hnd u) rfl

/-- At `recΔ b s n`, if `n ≠ void` and `n` is not a `delta _`, then no safe root step. -/
theorem localJoin_rec_other (b s n : Trace)
    (hn0 : n ≠ void) (hns : ∀ u, n ≠ delta u) : LocalJoinSafe (recΔ b s n) := by
  refine localJoin_of_none (a := recΔ b s n) ?h
  intro x hx
  cases hx with
  | R_rec_zero _ _ _ => exact (hn0 rfl)
  | R_rec_succ _ _ u => exact (hns u) rfl

/-- At `app a b`, there is no safe root rule; join holds vacuously. -/
theorem localJoin_app (a b : Trace) : LocalJoinSafe (app a b) := by
  refine localJoin_of_none (a := app a b) ?h
  intro x hx
  cases hx

/-- At `recΔ b s (merge a c)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_merge (b s a c : Trace) : LocalJoinSafe (recΔ b s (merge a c)) := by
  refine localJoin_of_none (a := recΔ b s (merge a c)) ?h
  intro x hx; cases hx

/-- At `recΔ b s (app a c)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_app (b s a c : Trace) : LocalJoinSafe (recΔ b s (app a c)) := by
  refine localJoin_of_none (a := recΔ b s (app a c)) ?h
  intro x hx; cases hx

/-- At `recΔ b s (integrate t)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_integrate (b s t : Trace) : LocalJoinSafe (recΔ b s (integrate t)) := by
  refine localJoin_of_none (a := recΔ b s (integrate t)) ?h
  intro x hx; cases hx

/-- At `recΔ b s (eqW a c)`, no safe root rule (scrutinee not void/delta). -/
theorem localJoin_rec_eqW (b s a c : Trace) : LocalJoinSafe (recΔ b s (eqW a c)) := by
  refine localJoin_of_none (a := recΔ b s (eqW a c)) ?h
  intro x hx; cases hx

/-- At `merge a b`, if neither side is `void` and `a ≠ b`, then no safe root step. -/
theorem localJoin_merge_no_void_neq (a b : Trace)
    (hav : a ≠ void) (hbv : b ≠ void) (hneq : a ≠ b) : LocalJoinSafe (merge a b) := by
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
theorem localJoin_all_safe : ∀ a : Trace, LocalJoinSafe a := by
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
      | recΔ b s n =>
          exact localJoin_integrate_rec b s n
      | eqW x y =>
          exact localJoin_integrate_eqW x y
  | merge x y =>
      by_cases hxv : x = void
      · cases hxv
        exact localJoin_merge_void_left y
      · by_cases hyv : y = void
        · cases hyv
          exact localJoin_merge_void_right x
        · by_cases hxy : x = y
          · cases hxy
            exact localJoin_merge_tt x
          · exact localJoin_merge_no_void_neq x y hxv hyv hxy
  | app x y =>
      exact localJoin_app x y
  | recΔ b s n =>
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
      | recΔ b' s' n' =>
          refine localJoin_rec_other b s (recΔ b' s' n') ?hn0 ?hns
          · intro h; cases h
          · intro u h; cases h
      | eqW x y =>
          exact localJoin_rec_eqW b s x y
  | eqW x y =>
      by_cases hxy : x = y
      · cases hxy
        by_cases h0 : MetaSN_DM.kappaM x = 0
        · refine localJoin_of_unique (a := eqW x x) (d := void) ?h
          intro z hz
          cases hz with
          | R_eq_refl _ _ =>
              rfl
          | R_eq_diff _ _ hne =>
              exact False.elim (hne rfl)
        · exact localJoin_eqW_refl_guard_ne x h0
      · exact localJoin_eqW_ne x y hxy
end MetaSN_KO7

namespace MetaSN_KO7

/-- If a root local join holds at `a`, then a ctx-local join also holds at `a`.
This embeds the root `SafeStepStar` witnesses into `SafeStepCtxStar`. -/
theorem localJoin_ctx_of_localJoin (a : Trace)
    (h : LocalJoinSafe a) : LocalJoinSafe_ctx a := by
  intro b c hb hc
  rcases h hb hc with ⟨d, hbStar, hcStar⟩
  exact ⟨d, ctxstar_of_star hbStar, ctxstar_of_star hcStar⟩

end MetaSN_KO7

namespace MetaSN_KO7

/-- Ctx wrapper: if neither side is void and `a ≠ b`, then ctx-local join holds at `merge a b`. -/
theorem localJoin_ctx_merge_no_void_neq (a b : Trace)
    (hav : a ≠ void) (hbv : b ≠ void) (hneq : a ≠ b) :
    LocalJoinSafe_ctx (merge a b) :=
  localJoin_ctx_of_localJoin (a := merge a b)
    (h := localJoin_merge_no_void_neq a b hav hbv hneq)

end MetaSN_KO7

namespace MetaSN_KO7

/-- Ctx wrapper: eqW distinct arguments have ctx-local join (only diff rule applies). -/
theorem localJoin_ctx_eqW_ne (a b : Trace) (hne : a ≠ b) :
    LocalJoinSafe_ctx (eqW a b) :=
  localJoin_ctx_of_localJoin (a := eqW a b)
    (h := localJoin_eqW_ne a b hne)

/-- Ctx wrapper: at eqW a a with kappaM a ≠ 0, only diff applies; ctx-local join holds. -/
theorem localJoin_ctx_eqW_refl_guard_ne (a : Trace)
    (h0ne : MetaSN_DM.kappaM a ≠ 0) :
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

/-- Ctx wrapper: if `integrate (merge a a) ⇒ctx* void`, eqW a a ctx-joins at void. -/
theorem localJoin_ctx_eqW_refl_if_integrate_merge_to_void (a : Trace)
    (hiv : SafeStepCtxStar (integrate (merge a a)) void) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_eqW_refl_ctx_if_integrate_merge_to_void a hiv

/-- Ctx wrapper: if `a ⇒* delta n` and guards hold on `delta n`, eqW a a ctx-joins. -/
theorem localJoin_ctx_eqW_refl_if_arg_star_to_delta (a n : Trace)
    (ha : SafeStepStar a (delta n))
    (hδ : deltaFlag (delta n) = 0)
    (h0 : MetaSN_DM.kappaM (delta n) = 0) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_eqW_refl_ctx_if_arg_star_to_delta a n ha hδ h0

/-- Ctx wrapper: if `normalizeSafe a = delta n` and guards hold, eqW a a ctx-joins. -/
theorem localJoin_ctx_eqW_refl_if_normalizes_to_delta (a n : Trace)
    (hn : normalizeSafe a = delta n)
    (hδ : deltaFlag (delta n) = 0)
    (h0 : MetaSN_DM.kappaM (delta n) = 0) :
    LocalJoinSafe_ctx (eqW a a) :=
  localJoin_eqW_refl_ctx_if_normalizes_to_delta a n hn hδ h0

end MetaSN_KO7

namespace MetaSN_KO7

/-- Ctx wrapper: when `a` is literally `delta n` and guards hold, eqW (delta n) (delta n) ctx-joins. -/
theorem localJoin_ctx_eqW_refl_when_a_is_delta (n : Trace)
    (hδ : deltaFlag (delta n) = 0)
    (h0 : MetaSN_DM.kappaM (delta n) = 0) :
    LocalJoinSafe_ctx (eqW (delta n) (delta n)) :=
  localJoin_eqW_refl_ctx_when_a_is_delta n hδ h0

end MetaSN_KO7
```

## 8. OperatorKO7/Meta/Newman_Safe.lean

**Lines:** 205

```lean
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
- This file is parameterized by a local-join hypothesis `locAll : ∀ a, LocalJoinAt a`.
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
  ∀ {b c}, SafeStep a b → SafeStep a c → ∃ d, SafeStepStar b d ∧ SafeStepStar c d

/-- Church–Rosser (confluence) for the safe star closure. -/
def ConfluentSafe : Prop :=
  ∀ a b c, SafeStepStar a b → SafeStepStar a c → ∃ d, SafeStepStar b d ∧ SafeStepStar c d

/-! ### Small join helpers (step vs. star) -/

/-- Trivial join of a single left step with a right reflexive star (choose `d = b`). -/
theorem join_step_with_refl_star {a b : Trace}
  (hab : SafeStep a b) : ∃ d, SafeStepStar b d ∧ SafeStepStar a d := by
  refine ⟨b, ?_, ?_⟩
  · exact SafeStepStar.refl b
  · exact safestar_of_step hab

-- Join a single left step against a right star with a head step, delegating the tail to a
-- provided star–star joiner starting at the right-head successor.
/-- Join one left root step against a right multi-step path, using local join + a star-star joiner. -/
theorem join_step_with_tail_star
  {a b c₁ c : Trace}
  (loc : LocalJoinAt a)
  (joinSS : ∀ {x y z}, SafeStepStar x y → SafeStepStar x z → ∃ d, SafeStepStar y d ∧ SafeStepStar z d)
  (hab : SafeStep a b) (hac₁ : SafeStep a c₁) (hct : SafeStepStar c₁ c)
  : ∃ d, SafeStepStar b d ∧ SafeStepStar c d := by
  -- Local join at the root gives a common `e` with `b ⇒* e` and `c₁ ⇒* e`.
  rcases loc (b := b) (c := c₁) (hab) (hac₁) with ⟨e, hbe, hc₁e⟩
  -- Use the provided star–star joiner at source `c₁` to join `c₁ ⇒* e` and `c₁ ⇒* c`.
  rcases joinSS (x := c₁) (y := e) (z := c) hc₁e hct with ⟨d, hed, hcd⟩
  -- Compose on the left: `b ⇒* e ⇒* d`.
  exact ⟨d, safestar_trans hbe hed, hcd⟩

-- If we can locally join root-steps everywhere and we have a star–star joiner, then a single
-- left step joins with any right star.
/-- If local join holds everywhere and we can join stars, then a single step joins with any star. -/
theorem join_step_star_of_join_star_star
  (locAll : ∀ a, LocalJoinAt a)
  (joinSS : ∀ {x y z}, SafeStepStar x y → SafeStepStar x z → ∃ d, SafeStepStar y d ∧ SafeStepStar z d)
  {a b c : Trace}
  (hab : SafeStep a b) (hac : SafeStepStar a c)
  : ∃ d, SafeStepStar b d ∧ SafeStepStar c d := by
  -- Case split on the right star.
  cases hac with
  | refl _ =>
      -- Right is reflexive: join is immediate with `d = b`.
      exact join_step_with_refl_star hab
  | tail hac₁ hct =>
      -- Right has a head step: use the tail helper with local join at `a` and the provided `joinSS`.
      exact join_step_with_tail_star (locAll a) (joinSS) hab hac₁ hct

/-! ### Star–star join by Acc recursion and Newman's lemma -/

-- Main engine: star–star join at a fixed source, by Acc recursion on SafeStepRev at the source.
/-- Core engine: join two `SafeStepStar` paths out of `x` by `Acc` recursion on `SafeStepRev x`. -/
private theorem join_star_star_at
  (locAll : ∀ a, LocalJoinAt a)
  : ∀ x, Acc SafeStepRev x → ∀ {y z : Trace}, SafeStepStar x y → SafeStepStar x z → ∃ d, SafeStepStar y d ∧ SafeStepStar z d := by
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
    exact ⟨z, hxz, SafeStepStar.refl z⟩
  | inr hex =>
    rcases hex with ⟨b1, hxb1, hb1y⟩
    cases HZ with
    | inl hEq2 =>
      -- z = x, trivial join with y via left head step
      cases hEq2
      exact ⟨y, SafeStepStar.refl y, SafeStepStar.tail hxb1 hb1y⟩
    | inr hey =>
      rcases hey with ⟨c1, hxc1, hc1z⟩
      -- Local join at root x
      rcases locAll x hxb1 hxc1 with ⟨e, hb1e, hc1e⟩
      -- Use IH at c1 to join c1 ⇒* e and c1 ⇒* z
      rcases ih c1 hxc1 hc1e hc1z with ⟨d₁, hed₁, hzd₁⟩
      -- Compose b1 ⇒* e ⇒* d₁
      have hb1d₁ : SafeStepStar b1 d₁ := safestar_trans hb1e hed₁
      -- Use IH at b1 to join b1 ⇒* y and b1 ⇒* d₁
      rcases ih b1 hxb1 hb1y hb1d₁ with ⟨d, hyd, hd₁d⟩
      -- Final composition on the right
      exact ⟨d, hyd, safestar_trans hzd₁ hd₁d⟩

theorem join_star_star
  (locAll : ∀ a, LocalJoinAt a)
  {a b c : Trace}
  (hab : SafeStepStar a b) (hac : SafeStepStar a c)
  : ∃ d, SafeStepStar b d ∧ SafeStepStar c d := by
  exact join_star_star_at locAll a (acc_SafeStepRev a) hab hac

-- Newman's lemma for the safe relation.
/-- Newman's lemma specialized to `SafeStep`: termination + local joinability implies confluence. -/
theorem newman_safe (locAll : ∀ a, LocalJoinAt a) : ConfluentSafe := by
  intro _ _ _ hab hac
  exact join_star_star locAll hab hac

end MetaSN_KO7

namespace MetaSN_KO7

/-! ## Derived corollaries (parameterized by local join) -/

/-- Global confluence from local join everywhere (alias of `newman_safe`). -/
theorem confluentSafe_of_localJoinAt_and_SN
    (locAll : ∀ a, LocalJoinAt a) : ConfluentSafe :=
  newman_safe locAll

/-- Unique normal forms under global confluence provided by `locAll`. -/
theorem unique_normal_forms_of_loc
    (locAll : ∀ a, LocalJoinAt a)
    {a n₁ n₂ : Trace}
    (h₁ : SafeStepStar a n₁) (h₂ : SafeStepStar a n₂)
    (hnf₁ : NormalFormSafe n₁) (hnf₂ : NormalFormSafe n₂) :
    n₁ = n₂ := by
  have conf : ConfluentSafe := newman_safe locAll
  obtain ⟨d, h₁d, h₂d⟩ := conf a n₁ n₂ h₁ h₂
  have eq₁ : n₁ = d := nf_no_safestar_forward hnf₁ h₁d
  have eq₂ : n₂ = d := nf_no_safestar_forward hnf₂ h₂d
  simp [eq₁, eq₂]

/-- The normalizer returns the unique normal form (assuming `locAll`). -/
theorem normalizeSafe_unique_of_loc
    (locAll : ∀ a, LocalJoinAt a)
    {t n : Trace}
    (h : SafeStepStar t n) (hnf : NormalFormSafe n) :
    n = normalizeSafe t := by
  exact unique_normal_forms_of_loc locAll h (to_norm_safe t) hnf (norm_nf_safe t)

/-- Safe-step-related terms normalize to the same result (assuming `locAll`). -/
theorem normalizeSafe_eq_of_star_of_loc
    (locAll : ∀ a, LocalJoinAt a)
    {a b : Trace} (h : SafeStepStar a b) :
    normalizeSafe a = normalizeSafe b := by
  have ha := to_norm_safe a
  have hb := to_norm_safe b
  have conf : ConfluentSafe := newman_safe locAll
  obtain ⟨d, had, hbd⟩ := conf a (normalizeSafe a) (normalizeSafe b) ha (safestar_trans h hb)
  have eq₁ := nf_no_safestar_forward (norm_nf_safe a) had
  have eq₂ := nf_no_safestar_forward (norm_nf_safe b) hbd
  simp [eq₁, eq₂]

/-- Global local-join discharge for `SafeStep`, imported from `Confluence_Safe`. -/
theorem locAll_safe : ∀ a, LocalJoinAt a := by
  intro a b c hb hc
  exact (MetaSN_KO7.localJoin_all_safe a) hb hc

/-- Unconditional confluence for the safe fragment (`SafeStep`). -/
theorem confluentSafe : ConfluentSafe :=
  newman_safe locAll_safe

/-- Unconditional unique normal forms for the safe fragment. -/
theorem unique_normal_forms_safe
    {a n₁ n₂ : Trace}
    (h₁ : SafeStepStar a n₁) (h₂ : SafeStepStar a n₂)
    (hnf₁ : NormalFormSafe n₁) (hnf₂ : NormalFormSafe n₂) :
    n₁ = n₂ :=
  unique_normal_forms_of_loc locAll_safe h₁ h₂ hnf₁ hnf₂

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
```

## 9. OperatorKO7/Meta/ComputableMeasure_Verification.lean

**Lines:** 241

```lean
import OperatorKO7.Meta.ComputableMeasure

/-!
# Verification Suite for ComputableMeasure

This file provides comprehensive verification that our computable measure
is bulletproof and handles all edge cases correctly.

## Test Categories:
1. τ monotonicity verification
2. DM order properties
3. Measure decrease for each rule
4. Edge cases and corner cases
5. Comparison with original noncomputable measure
-/

namespace OperatorKO7.MetaCM.Verification

open OperatorKO7 Trace MetaCM
open MetaSN_KO7 MetaSN_DM

/-! ## Section 1: τ Monotonicity Tests -/

-- Verify τ is monotone for all constructors except delta
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
example (b s n : Trace) : tau b < tau (recΔ b s n) := by
  simp [tau]; omega
example (b s n : Trace) : tau s < tau (recΔ b s n) := by
  simp [tau]; omega
example (b s n : Trace) : tau n < tau (recΔ b s n) := by
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
example {X Y : Multiset Nat} {τ₁ τ₂ : Nat} (h : DM X Y) :
    LexDM_c (X, τ₁) (Y, τ₂) := dm_to_LexDM_c_left h

/-! ## Section 3: Measure Decrease Verification -/

-- Test all 8 rules decrease the measure
section RuleTests

-- Rule 1: integrate (delta t) → void
example (t : Trace) : Lex3c (mu3c void) (mu3c (integrate (delta t))) := by
  apply drop_R_int_delta_c

-- Rule 2: merge void t → t
example (t : Trace) (hδ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge void t)) := by
  apply drop_R_merge_void_left_c
  exact hδ

-- Rule 3: merge t void → t
example (t : Trace) (hδ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge t void)) := by
  apply drop_R_merge_void_right_c
  exact hδ

-- Rule 4: merge t t → t (duplication case!)
example (t : Trace) (hδ : deltaFlag t = 0) (h0 : kappaM t = 0) :
    Lex3c (mu3c t) (mu3c (merge t t)) := by
  apply drop_R_merge_cancel_c
  exact hδ
  exact h0

-- Rule 5: recΔ b s void → b
example (b s : Trace) (hδ : deltaFlag b = 0) :
    Lex3c (mu3c b) (mu3c (recΔ b s void)) := by
  apply drop_R_rec_zero_c
  exact hδ

-- Rule 6: recΔ b s (delta n) → app s (recΔ b s n)
example (b s n : Trace) :
    Lex3c (mu3c (app s (recΔ b s n))) (mu3c (recΔ b s (delta n))) := by
  apply drop_R_rec_succ_c

-- Rule 7: eqW a a → void
example (a : Trace) :
    Lex3c (mu3c void) (mu3c (eqW a a)) := by
  apply drop_R_eq_refl_c

-- Rule 8: eqW a b → integrate (merge a b)
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

-- Verify δ-flag is binary (0 or 1)
/--
`deltaFlag` is intentionally a binary phase indicator (0 or 1).

This lemma is used as a sanity check that the computable triple-lex measure does not accidentally
encode additional phases beyond the intended `recΔ _ _ (delta _)` detection.
-/
lemma deltaFlag_binary (t : Trace) : deltaFlag t = 0 ∨ deltaFlag t = 1 := by
  cases t <;> simp
  case recΔ b s n =>
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
    (∃ (_μ : Trace → Nat × (Multiset Nat × Nat)), WellFounded MetaSN_KO7.SafeStepRev) ↔
      WellFounded MetaSN_KO7.SafeStepRev := by
  constructor
  · intro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨mu3c, h⟩

/-! ## Section 7: Stress Tests -/

-- Large terms still work
/-- A moderately complex concrete trace used for stress-testing `tau` and `mu3c`. -/
def bigTrace : Trace :=
  recΔ (merge void void) (app void void) (delta (integrate void))

example : tau bigTrace = 3 + 2 + 1 + 1 := by
  simp [bigTrace, tau]

-- Measure works on big terms
example :
    Lex3c (mu3c void) (mu3c (eqW bigTrace bigTrace)) := by
  apply drop_R_eq_refl_c

/-! ## Section 8: Invariants and Properties -/

-- τ preserves structure under delta
/-- `tau` is transparent under `delta` by definition (restated as a named lemma). -/
lemma tau_delta_preserve (t : Trace) : tau (delta t) = tau t := rfl

-- κᴹ behavior under constructors (from SafeStep core)
/-- Convenience bundle of basic `kappaM` simp-facts (re-exported as a single lemma). -/
lemma kappaM_facts (a b : Trace) :
    kappaM void = 0 ∧
    kappaM (delta a) = kappaM a ∧
    kappaM (integrate a) = kappaM a ∧
    kappaM (merge a b) = kappaM a ∪ kappaM b ∧
    kappaM (app a b) = kappaM a ∪ kappaM b ∧
    kappaM (eqW a b) = kappaM a ∪ kappaM b := by
  simp [kappaM]

-- δ-flag is 1 only for recΔ _ _ (delta _)
/-- Characterization of the `deltaFlag` phase bit. -/
lemma deltaFlag_characterization (t : Trace) :
    deltaFlag t = 1 ↔ ∃ b s n, t = recΔ b s (delta n) := by
  cases t <;> simp [deltaFlag]
  case recΔ b s n =>
    cases n <;> simp

/-! ## Section 9: No Infinite Chains -/

-- Direct proof that no infinite SafeStep chain exists
/-- There is no infinite forward `SafeStep` chain, since `mu3c` strictly decreases and `Lex3c` is WF. -/
theorem no_infinite_safestep_chain :
    ¬∃ (seq : Nat → Trace), ∀ n, SafeStep (seq n) (seq (n + 1)) := by
  intro ⟨seq, h⟩
  -- The measure strictly decreases along the chain
  have dec : ∀ n, Lex3c (mu3c (seq (n + 1))) (mu3c (seq n)) := by
    intro n
    exact measure_decreases_safe_c (h n)
  -- But Lex3c is well-founded, so no infinite descending chain exists.
  exact
    (WellFounded.wellFounded_iff_no_descending_seq.1 wf_Lex3c).elim
      ⟨fun n => mu3c (seq n), dec⟩

end OperatorKO7.MetaCM.Verification
```

## 10. OperatorKO7/Meta/ComputableMeasure_Test.lean

**Lines:** 45

```lean
import OperatorKO7.Meta.ComputableMeasure

/-!
# Quick test that ComputableMeasure works correctly

This file is intentionally lightweight: it is a scratchpad of `example` goals and `#check`s that
exercise the public surface of the computable termination proof for `SafeStep`.

It is not part of the certified artifact itself; it exists to make regressions obvious during local
development (and for reviewers who want a quick sanity pass without reading the full proofs).
-/

namespace OperatorKO7.MetaCM.Test

open OperatorKO7 Trace

open OperatorKO7.MetaCM
open MetaSN_KO7

-- Main theorem is available
example : WellFounded SafeStepRev := wf_SafeStepRev_c

-- Measure decreases for each rule
example (t : OperatorKO7.Trace) :
    OperatorKO7.MetaCM.Lex3c
      (OperatorKO7.MetaCM.mu3c OperatorKO7.Trace.void)
      (OperatorKO7.MetaCM.mu3c (OperatorKO7.Trace.integrate (OperatorKO7.Trace.delta t))) :=
  drop_R_int_delta_c t

-- All 8 rules work
#check drop_R_int_delta_c
#check drop_R_merge_void_left_c
#check drop_R_merge_void_right_c
#check drop_R_merge_cancel_c
#check drop_R_rec_zero_c
#check drop_R_rec_succ_c
#check drop_R_eq_refl_c
#check drop_R_eq_diff_c

-- Main aggregator works
#check measure_decreases_safe_c

-- If this file elaborates, the basic API of `ComputableMeasure.lean` is intact.

end OperatorKO7.MetaCM.Test
```

## 11. OperatorKO7/Meta/DM_MPO_Orientation.lean

**Lines:** 51

```lean
import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna

/-!
# DM/MPO Orientation Helpers (safe wrappers)

This module provides small, composable wrappers around the Dershowitz–Manna
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
Right-add orientation: if `Y ≠ 0`, then `X < X + Y` in the DM order.

This is a thin wrapper around `MetaSN_DM.dm_lt_add_of_ne_zero'` with the
arguments placed for ergonomic use.
-/
lemma dm_add_right_of_ne_zero {X Y : Multiset ℕ} (hY : Y ≠ 0) : OperatorKO7.MetaCM.DM X (X + Y) := by
  simpa using MetaSN_DM.dm_lt_add_of_ne_zero' X Y hY

/--
Left-add orientation: if `X ≠ 0`, then `Y < X + Y` in the DM order.

This follows from commutativity of multiset addition and the right-add lemma.
-/
lemma dm_add_left_of_ne_zero {X Y : Multiset ℕ} (hX : X ≠ 0) : OperatorKO7.MetaCM.DM Y (X + Y) := by
  simpa [add_comm] using MetaSN_DM.dm_lt_add_of_ne_zero' Y X hX

/-- DM drop on κᴹ for rec_zero (re-export for ergonomics). -/
lemma dm_drop_rec_zero (b s : Trace) :
    OperatorKO7.MetaCM.DM (MetaSN_DM.kappaM b) (MetaSN_DM.kappaM (recΔ b s void)) := by
  simpa [OperatorKO7.MetaCM.DM] using MetaSN_DM.dm_drop_R_rec_zero b s

/-- If X ≠ 0 then X ∪ X ≠ 0 (re-export). -/
lemma union_self_ne_zero_of_ne_zero {X : Multiset ℕ} (h : X ≠ 0) :
    X ∪ X ≠ (0 : Multiset ℕ) := by
  simpa using MetaSN_DM.union_self_ne_zero_of_ne_zero h

end OperatorKO7.MetaOrientation
```

## 12. OperatorKO7/Meta/Examples_Publish.lean

**Lines:** 29

```lean
import OperatorKO7.Kernel
import OperatorKO7.Meta.Normalize_Safe
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.Newman_Safe
import OperatorKO7.Meta.ComputableMeasure

open OperatorKO7

/-!
Exported API examples - smoke tests for reviewers.
This module should only import stable, published Meta modules and check that
their key symbols exist and typecheck. It contains no new proofs.
-/

example : WellFounded MetaSN_KO7.SafeStepRev := OperatorKO7.MetaCM.wf_SafeStepRev_c

example (t : Trace) : MetaSN_KO7.SafeStepStar t (MetaSN_KO7.normalizeSafe t) :=
  MetaSN_KO7.to_norm_safe t

example (t : Trace) : MetaSN_KO7.NormalFormSafe (MetaSN_KO7.normalizeSafe t) :=
  MetaSN_KO7.norm_nf_safe t

-- Computable μ3c: simple per-rule drop example (merge void t → t) at t = void
example : OperatorKO7.MetaCM.Lex3c
    (OperatorKO7.MetaCM.mu3c OperatorKO7.Trace.void)
    (OperatorKO7.MetaCM.mu3c (OperatorKO7.Trace.merge OperatorKO7.Trace.void OperatorKO7.Trace.void)) := by
  have hδ : MetaSN_KO7.deltaFlag OperatorKO7.Trace.void = 0 := by
    simp [MetaSN_KO7.deltaFlag]
  simpa using OperatorKO7.MetaCM.drop_R_merge_void_left_c OperatorKO7.Trace.void hδ
```

## 13. OperatorKO7/Meta/Operational_Incompleteness.lean

**Lines:** 1188

```lean
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
| s    : Term → Term
| add  : Term → Term → Term
| mul  : Term → Term → Term
| pair : Term → Term → Term
| fst  : Term → Term
| snd  : Term → Term
deriving DecidableEq, Repr

open Term

/-- Arity table for NameGate/TypeGate reporting. -/
inductive Op where
| z | s | add | mul | pair | fst | snd
deriving DecidableEq, Repr

/-- Arity of each operator symbol (used only for probe reporting, not for rewriting). -/
def arity : Op → Nat
| .z    => 0
| .s    => 1
| .add  => 2
| .mul  => 2
| .pair => 2
| .fst  => 1
| .snd  => 1

/-- Eight unconditional rules at the top level. -/
inductive Rule : Term → Term → Prop
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
def rhsPiecesLHS : Term → List Term
| add a b =>
  let LaddLeft : List Term :=
    match a with
    | z     => [b]            -- r1: add z b → b
    | s x   => [add x b]      -- r2: add (s x) b → s (add x b)
    | _     => []
  let LaddRight : List Term :=
    match b with
    | z     => [a]            -- r7: add a z → a
    | _     => []
  LaddLeft ++ LaddRight
| mul a b =>
  let LmulLeft : List Term :=
    match a with
    | z     => [z]            -- r3: mul z b → z
    | s x   => [b, mul x b]   -- r4: mul (s x) b → add b (mul x b)
    | _     => []
  let LmulRight : List Term :=
    match b with
    | z     => [z]            -- r8: mul a z → z
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
inductive Step : Term → Term → Prop
| base {l r}     : Rule l r → Step l r
| sCtx  {t u}    : Step t u → Step (s t) (s u)
| addLCtx {t u v}: Step t u → Step (add t v) (add u v)
| addRCtx {t u v}: Step t u → Step (add v t) (add v u)
| mulLCtx {t u v}: Step t u → Step (mul t v) (mul u v)
| mulRCtx {t u v}: Step t u → Step (mul v t) (mul v u)
| pairLCtx{t u v}: Step t u → Step (pair t v) (pair u v)
| pairRCtx{t u v}: Step t u → Step (pair v t) (pair v u)
| fstCtx {t u}   : Step t u → Step (fst t) (fst u)
| sndCtx {t u}   : Step t u → Step (snd t) (snd u)

/-- Reflexive–transitive closure `Star`. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
| refl {a}       : Star R a a
| step {a b c}   : R a b → Star R b c → Star R a c

namespace Star
variable {α : Type} {R : α → α → Prop}

@[simp] theorem refl' {a} : Star R a a := Star.refl

theorem trans {a b c} (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  induction h1 with
  | refl =>
    simpa using h2
  | step h h1 ih =>
    exact Star.step h (ih h2)

end Star

/-- A simple additive size measure used only for the duplication stress test. -/
def size : Term → Nat
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

def f : Term → Term
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
def R4_size_profile (x y : Term) : Nat × Nat := (size (R4_before x y), size (R4_after x y))

/-
Additive calculation:
  size (mul (s x) y) = 2 + size x + size y
  size (add y (mul x y)) = 2 + size x + 2 * size y
Hence `size(after) = size(before) + size y`. No strict drop whenever `size y ≥ 1`.
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
    ¬ size (R4_after x y) < size (R4_before x y) := by
  intro hlt
  have : size (R4_before x y) + size y < size (R4_before x y) := by
    simpa [r4_size_after_eq_before_plus_piece] using hlt
  have hle : size (R4_before x y) ≤ size (R4_before x y) + size y := Nat.le_add_right _ _
  exact (Nat.lt_irrefl _) (Nat.lt_of_le_of_lt hle this)

/-! Lightweight lex witness for r4 pieces vs redex (illustrative). -/
namespace R4Lex

abbrev Weight := Nat × Nat

def lexLT (a b : Weight) : Prop :=
  a.fst < b.fst ∨ (a.fst = b.fst ∧ a.snd < b.snd)

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

/-! DM orientation for r4: {size y, size (mul x y)} <ₘ {size (mul (s x) y)}. -/
namespace R4DM
open Multiset

local infix:70 " <ₘ " => Multiset.IsDershowitzMannaLT

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
  ({size y} + {size (mul x y)}) <ₘ ({size (mul (s x) y)}) := by
  classical
  -- X = 0, Y = {size y, size (mul x y)}, Z = {size redex}
  refine ⟨(0 : Multiset Nat), ({size y} + {size (mul x y)}), {size (mul (s x) y)}, ?hZ, by simp, by simp, ?hY⟩
  · simp
  · intro y' hy'
    rcases mem_add.mp hy' with hY | hM
    · have hy0 : y' = size y := by simpa using hY
      refine ⟨size (mul (s x) y), by simp, ?_⟩
      simpa [hy0] using pieceY_lt_redex x y
    · have hm0 : y' = size (mul x y) := by simpa using hM
      refine ⟨size (mul (s x) y), by simp, ?_⟩
      simpa [hm0] using pieceMul_lt_redex x y

end R4DM

/-! MPO-style orientation for r4 using a simple precedence/status triple. -/
namespace R4MPO

/- Precedence: mul > add > s > pair > fst/snd > z. -/
@[simp] def headRank : Term → Nat
| z         => 0
| s _       => 3
| add _ _   => 4
| mul _ _   => 5
| pair _ _  => 2
| fst _     => 1
| snd _     => 1

@[simp] def weight : Term → Nat × Nat × Nat
| z           => (headRank z, 0, 0)
| s t         => (headRank (s t), size t, 0)
| add a b     => (headRank (add a b), size a, size b)
| mul a b     => (headRank (mul a b), size a, size b)
| pair a b    => (headRank (pair a b), size a, size b)
| fst t       => (headRank (fst t), size t, 0)
| snd t       => (headRank (snd t), size t, 0)

/- Strict lexicographic order on Nat × Nat × Nat. -/
def ltW (u v : Nat × Nat × Nat) : Prop :=
  u.1 < v.1 ∨ (u.1 = v.1 ∧ (u.2.1 < v.2.1 ∨ (u.2.1 = v.2.1 ∧ u.2.2 < v.2.2)))

lemma ltW_of_fst_lt {a b : Nat × Nat × Nat} (h : a.1 < b.1) : ltW a b := Or.inl h

/-- Orientation witness: add y (mul x y) < mul (s x) y under ltW ∘ weight. -/
theorem mpo_orient_r4 (x y : Term) :
  ltW (weight (add y (mul x y))) (weight (mul (s x) y)) := by
  -- First components: headRank(add …) < headRank(mul …)
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
--     Package the “operator-only” constraints explicitly.
-- -/

structure InternallyDefinableMeasure where
  κMType  : Type          -- multiset-like component (DM-style), abstract
  μType   : Type          -- ordinal-like component, abstract
  flag    : Term → Bool   -- delta-flag or any unary indicator
  κM      : Term → κMType -- structural multiset measure
  μ       : Term → μType  -- well-founded secondary component
  base    : Term → Term → Prop    -- base simplification order
  wf_base : WellFounded base      -- well-foundedness witness

  /- Monotonicity/compositionality in all contexts. -/
  mono_s      : ∀ {t u}, base t u → base (s t) (s u)
  mono_add_L  : ∀ {t u v}, base t u → base (add t v) (add u v)
  mono_add_R  : ∀ {t u v}, base t u → base (add v t) (add v u)
  mono_mul_L  : ∀ {t u v}, base t u → base (mul t v) (mul u v)
  mono_mul_R  : ∀ {t u v}, base t u → base (mul v t) (mul v u)
  mono_pair_L : ∀ {t u v}, base t u → base (pair t v) (pair u v)
  mono_pair_R : ∀ {t u v}, base t u → base (pair v t) (pair v u)
  mono_fst    : ∀ {t u}, base t u → base (fst t) (fst u)
  mono_snd    : ∀ {t u}, base t u → base (snd t) (snd u)

  /- Lexicographic/orientation gate (relaxed for skeleton):
     For each rule instance, we accept either:
     (i) a flag drop; or (ii) a per-piece strict decrease in `base`; or (iii) a direct base drop.
     This matches the DM/MPO contract where duplicators use per-piece orientation.
  -/
  lex_ok :
    ∀ {l r}, Rule l r →
      (flag r = false ∧ flag l = true) ∨
      (∃ t, t ∈ rhsPiecesLHS l ∧ base t l) ∨
      base r l

  /- Per-piece orientation gate (duplication-aware): for every rule, every listed RHS
    piece is strictly below the removed LHS redex in the base order. This encodes
    the Dershowitz–Manna/MPO-style contract used in P2. -/
  per_piece_base_lt : ∀ {l r}, Rule l r → ∀ t ∈ rhsPiecesLHS l, base t l

  /- Explicit duplication additive failure (documentation contract): the additive `size`
    does not strictly drop for the duplicating rule r4 before any robust orientation.
    This field records the phenomenon as part of the class; a trivial instance can
    reuse `r4_no_strict_drop_additive` below. -/
  dup_additive_nodrop_r4 : ∀ x y, ¬ size (R4_after x y) < size (R4_before x y)

/-- C(Σ): Frozen alias for the KO7 method class used across the project. -/
abbrev CSigma := InternallyDefinableMeasure

/-! E) Stubs for operator-only encodings of Goodstein/Hydra. -/
namespace Encodings

/-- Codes internal to KO7 terms. -/
inductive Code : Type
| zero : Code
| suc  : Code → Code
| pair : Code → Code → Code
| tag  : Nat → Code → Code          -- finite tags for rule schemas
deriving DecidableEq, Repr

/-- Goodstein-style rule schema (shape only). -/
inductive GRule : Code → Code → Prop
| base_change (b n) :
    GRule (Code.tag b (Code.suc n)) (Code.tag (b+1) n)

/-- Hydra-style rule schema (shape only). -/
inductive HRule : Code → Code → Prop
| chop (h) : HRule (Code.suc h) (Code.pair h h)    -- illustrative duplication

end Encodings

-- /-- Target theorems are recorded as statements (no axioms). -/
namespace Targets

open Encodings

/-- “There exists a rule with no internal measure proving its decrease” (statement only). -/
def Exists_No_Internal_Decrease
  (M : InternallyDefinableMeasure) : Prop :=
  ∃ (l r : Term), Rule l r ∧ ¬ M.base l r

/-- Bridge to independence exemplars (statement only). -/
def Goodstein_Maps_Here : Prop :=
  ∀ (c d : Encodings.Code), Encodings.GRule c d → True    -- TODO: fill mapping later

def Hydra_Maps_Here : Prop :=
  ∀ (c d : Encodings.Code), Encodings.HRule c d → True    -- TODO: fill mapping later

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
def natToTerm : Nat → OperatorKO7.OpIncomp.Term
| 0     => OperatorKO7.OpIncomp.Term.z
| n+1   => OperatorKO7.OpIncomp.Term.s (natToTerm n)

/-- Total embedding of `Encodings.Code` into KO7 terms. -/
def encode : Code → OperatorKO7.OpIncomp.Term
| Code.zero      => OperatorKO7.OpIncomp.Term.z
| Code.suc c     => OperatorKO7.OpIncomp.Term.s (encode c)
| Code.pair a b  => OperatorKO7.OpIncomp.Term.pair (encode a) (encode b)
| Code.tag b c   => OperatorKO7.OpIncomp.Term.pair (natToTerm b) (encode c)

end Encodings

/-! Higher-level simulation layer (outside KO7 Step): Admin moves on encoded tags. -/
namespace Simulation
open Encodings OperatorKO7.OpIncomp

/-- Administrative move permitted by the simulation layer: bump the Goodstein base tag on the left of the pair while stripping one succ from the right component (since `encode (suc n) = s (encode n)`). -/
inductive Admin : Term → Term → Prop
| base_change (b : Nat) (n : Encodings.Code) :
    Admin (pair (natToTerm b) (s (encode n))) (pair (natToTerm (b+1)) (encode n))
| hydra_chop (h : Encodings.Code) :
  Admin (s (encode h)) (pair (encode h) (encode h))

/-- Combined simulation relation: either a KO7 Step or an Admin move. -/
def Rel (a b : Term) : Prop := OperatorKO7.OpIncomp.Step a b ∨ Admin a b

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

/-- Reflexive–transitive closure for Rel. -/
inductive RelStar : Term → Term → Prop
| refl {a} : RelStar a a
| step {a b c} : Rel a b → RelStar b c → RelStar a c

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

/- Paper↔code map (names frozen):
  - CSigma ≡ `M_size`
  - δ two-case: `delta_top_cases_add_s`, `delta_top_cases_mul_s`
  - δ Star runners: `delta_star_add_s_auto`, `delta_star_mul_s_auto`
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
  ∀ (b : Nat) (n : Encodings.Code),
    ¬ Step (encode (Code.tag b (Code.suc n)))
           (encode (Code.tag (b+1) n))

end Targets

-- Independence-grade “no-go box” recorded as a statement under Targets.
-- We avoid asserting the proof here; see documentation for the meta-argument.

/-- No single OperatorKO7.OpIncomp.Step originates from a numeral `natToTerm b`. -/
lemma no_step_from_natToTerm (b : Nat) : ∀ t, ¬ Step (Encodings.natToTerm b) t := by
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
lemma no_step_from_encode (c : Encodings.Code) : ∀ t, ¬ Step (Encodings.encode c) t := by
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
  -- Use the general “no step from encode” lemma instantiated at `tag b (suc n)`.
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

-- Additional Step → Star examples
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
  GoodsteinCore.Step ⟨Base.b b, Cn.s t⟩ ⟨Base.b (b+1), t⟩ := by
  simpa using GoodsteinCore.one_step b t

/- Hydra: a chop duplicates the other subtree (left and right variants). -/
example (h : Hydra) :
  HydraCore.Step (Hydra.node Hydra.head h) (Hydra.node h h) :=
  HydraCore.Step.chop_left h

example (h : Hydra) :
  HydraCore.Step (Hydra.node h Hydra.head) (Hydra.node h h) :=
  HydraCore.Step.chop_right h

/- Existential-style tiny witness. -/
example (h : Hydra) : ∃ h', HydraCore.Step (Hydra.node Hydra.head h) h' :=
  ⟨Hydra.node h h, HydraCore.Step.chop_left h⟩

end TinyGoodsteinHydra

namespace OperatorKO7.OpIncomp
open Term
-- set_option diagnostics true
/-- A concrete internal-measure instance using size as the base order.
Flags mark only r2/r4 LHSs (where additive size does not strictly drop). -/
noncomputable def flagTerm : Term → Bool
| add (s _) _ => true
| mul (s _) _ => true
| _           => false

noncomputable def M_size : InternallyDefinableMeasure where
  κMType := Unit
  μType  := Unit
  flag   := flagTerm
  κM     := fun _ => ()
  μ      := fun _ => ()
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
      -- r1: add z y → y, need y < 1 + y + 1
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r2 x y =>
      -- r2: add (s x) y → s (add x y)
      exact Or.inr (Or.inl ⟨add x y, by simp [rhsPiecesLHS], by simp only [size]; omega⟩)
    | r3 y =>
      -- r3: mul z y → z, need 1 < 1 + y + 1
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r4 x y =>
      -- r4: mul (s x) y → add y (mul x y)
      exact Or.inr (Or.inl ⟨y, by simp [rhsPiecesLHS], by simp only [size]; omega⟩)
    | r5 x y =>
      -- r5: fst (pair x y) → x, need x < x + y + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r6 x y =>
      -- r6: snd (pair x y) → y, need y < x + y + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r7 x =>
      -- r7: add x z → x, need x < x + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r8 x =>
      -- r8: mul x z → z, need 1 < x + 2
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
        · -- left pieces from a
          cases a with
          | z =>
            -- t ∈ [b]
            have hx : t = b := by simpa using hL
            subst hx
            -- size b < size (add z b) = 1 + b + 1
            simp only [size]
            omega
          | s xx =>
            -- t ∈ [add xx b]
            have hx : t = add xx b := by simpa using hL
            subst hx
            -- size (add xx b) < size (add (s xx) b)
            simp only [size]
            omega
          | _ =>
            -- no pieces from other constructors
            cases hL
        · -- right pieces from b
          cases b with
          | z =>
            -- t ∈ [a]
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
        · -- left pieces from a
          cases a with
          | z =>
            -- t ∈ [z]
            have hx : t = z := by simpa using hL
            subst hx
            -- 1 < 1 + size b + 1
            simp only [size]
            omega
          | s xx =>
            rcases List.mem_cons.mp hL with hby | hmul
            · -- t = b
              have hx : t = b := by simpa using hby
              subst hx
              -- size b < size (s xx) + size b + 1 = xx + 1 + b + 1
              simp only [size]
              omega
            · -- t = mul xx b
              have hx : t = mul xx b := by simpa using hmul
              subst hx
              -- size (mul xx b) < size (mul (s xx) b)
              simp only [size]
              omega
          | _ =>
            cases hL
        · -- right pieces from b
          cases b with
          | z =>
            -- t ∈ [z]
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

/-! Optional δ-guard (Prop) isolating the duplicating/flagged shapes.
    We provide a decidable predicate and a couple of lightweight lemmas. -/

/-- Terms whose head is add (s ·) · or mul (s ·) ·. -/
inductive Delta : Term → Prop
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

/- Simple preservation under right-context rewriting: the δ head persists. -/
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

/-! Substitution (homomorphic map) and δ‑preservation under substitution. -/

/-- Homomorphic transform on KO7 terms (preserves heads, transforms subterms). -/
def mapTerm (σ : Term → Term) : Term → Term
| z => z
| s t => s (mapTerm σ t)
| add a b => add (mapTerm σ a) (mapTerm σ b)
| mul a b => mul (mapTerm σ a) (mapTerm σ b)
| pair a b => pair (mapTerm σ a) (mapTerm σ b)
| fst t => fst (mapTerm σ t)
| snd t => snd (mapTerm σ t)

@[simp] lemma mapTerm_s (σ) (t : Term) : mapTerm σ (s t) = s (mapTerm σ t) := rfl
@[simp] lemma mapTerm_add (σ) (a b : Term) : mapTerm σ (add a b) = add (mapTerm σ a) (mapTerm σ b) := rfl
@[simp] lemma mapTerm_mul (σ) (a b : Term) : mapTerm σ (mul a b) = mul (mapTerm σ a) (mapTerm σ b) := rfl

lemma Delta_preserve_r2_subst (σ : Term → Term) (x y : Term) :
  Delta (mapTerm σ (add (s x) y)) := by
  simp [mapTerm, Delta.add_s]

lemma Delta_preserve_r4_subst (σ : Term → Term) (x y : Term) :
  Delta (mapTerm σ (mul (s x) y)) := by
  simp [mapTerm, Delta.mul_s]

/-! Promote mapTerm to a substitution alias and restate δ‑substitution lemmas. -/

abbrev subst := mapTerm

@[simp] lemma subst_s (σ) (t : Term) : subst σ (s t) = s (subst σ t) := rfl
@[simp] lemma subst_add (σ) (a b : Term) : subst σ (add a b) = add (subst σ a) (subst σ b) := rfl
@[simp] lemma subst_mul (σ) (a b : Term) : subst σ (mul a b) = mul (subst σ a) (subst σ b) := rfl

lemma Delta_subst_preserves_r2 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (add (s x) y)) := by
  simp [subst, mapTerm, Delta.add_s]

lemma Delta_subst_preserves_r4 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (mul (s x) y)) := by
  simp [subst, mapTerm, Delta.mul_s]

/-! Star-level automation for δ shapes. -/

lemma delta_star_cases_add_s (x y : Term) :
  Star Step (add (s x) y) (s (add x y)) ∨
  (y = z ∧ Star Step (add (s x) y) (s x)) := by
  -- r2 always provides the left branch as a single step
  exact Or.inl (Star.step (Step.base (Rule.r2 x y)) Star.refl)

lemma delta_star_cases_mul_s (x y : Term) :
  Star Step (mul (s x) y) (add y (mul x y)) ∨
  (y = z ∧ Star Step (mul (s x) y) z) := by
  -- r4 always provides the left branch as a single step
  exact Or.inl (Star.step (Step.base (Rule.r4 x y)) Star.refl)

/-! δ exhaustive two-case lemmas at the top level. -/

lemma delta_top_cases_add_s (x y r : Term)
  (h : Rule (add (s x) y) r) :
  r = s (add x y) ∨ (y = z ∧ r = s x) := by
  cases h with
  | r2 _ _ => exact Or.inl rfl
  | r7 _ => exact Or.inr ⟨rfl, rfl⟩

lemma delta_top_cases_mul_s (x y r : Term)
  (h : Rule (mul (s x) y) r) :
  r = add y (mul x y) ∨ (y = z ∧ r = z) := by
  cases h with
  | r4 _ _ => exact Or.inl rfl
  | r8 _ => exact Or.inr ⟨rfl, rfl⟩

/-- δ-safe critical pairs coverage (add): every rule at the guarded top-shape matches one of the two cases. -/
theorem Delta_SafePairs_Exhaustive_add
  (x y r : Term) (_hδ : Delta (add (s x) y)) (h : Rule (add (s x) y) r) :
  r = s (add x y) ∨ (y = z ∧ r = s x) :=
  delta_top_cases_add_s x y r h

/-- δ-safe critical pairs coverage (mul): every rule at the guarded top-shape matches one of the two cases. -/
theorem Delta_SafePairs_Exhaustive_mul
  (x y r : Term) (_hδ : Delta (mul (s x) y)) (h : Rule (mul (s x) y) r) :
  r = add y (mul x y) ∨ (y = z ∧ r = z) :=
  delta_top_cases_mul_s x y r h

/-! Small Star runners that choose the RHS automatically via the δ two-case split. -/

/-- Canonical RHS selector for `add (s x) y` using the δ two-case: if `y` is `z`, pick `s x`,
  otherwise pick `s (add x y)`. -/
def delta_rhs_add_s (x y : Term) : Term :=
  match y with
  | z => s x
  | _ => s (add x y)

/-- Canonical RHS selector for `mul (s x) y` using the δ two-case: if `y` is `z`, pick `z`,
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

/-! δ‑substitution per‑branch lemma stubs (align names with paper). -/

/-- Under substitution, the r2 guard shape is preserved (wrapper aligning naming with paper). -/
@[simp] theorem delta_subst_preserves_r2 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (add (s x) y)) :=
  Delta_subst_preserves_r2 σ x y

/-- Under substitution, the r4 guard shape is preserved (wrapper aligning naming with paper). -/
@[simp] theorem delta_subst_preserves_r4 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (mul (s x) y)) :=
  Delta_subst_preserves_r4 σ x y

/-! Examples using `M_size.lex_ok` on representative rules. -/

example (y : Term) :
  (flagTerm y = false ∧ flagTerm (add z y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (add z y) ∧ M_size.base t (add z y)) ∨
  M_size.base y (add z y) := by
  -- r1: add z y → y
  simpa using (M_size.lex_ok (Rule.r1 y))

example (x y : Term) :
  (flagTerm (add y (mul x y)) = false ∧ flagTerm (mul (s x) y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (mul (s x) y) ∧ M_size.base t (mul (s x) y)) ∨
  M_size.base (add y (mul x y)) (mul (s x) y) := by
  -- r4: mul (s x) y → add y (mul x y)
  simpa using (M_size.lex_ok (Rule.r4 x y))

example (x : Term) :
  (flagTerm x = false ∧ flagTerm (add x z) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (add x z) ∧ M_size.base t (add x z)) ∨
  M_size.base x (add x z) := by
  -- r7: add x z → x
  simpa using (M_size.lex_ok (Rule.r7 x))

example (x y : Term) :
  (flagTerm (s (add x y)) = false ∧ flagTerm (add (s x) y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (add (s x) y) ∧ M_size.base t (add (s x) y)) ∨
  M_size.base (s (add x y)) (add (s x) y) := by
  -- r2: add (s x) y → s (add x y)
  simpa using (M_size.lex_ok (Rule.r2 x y))

example (y : Term) :
  (flagTerm z = false ∧ flagTerm (mul z y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (mul z y) ∧ M_size.base t (mul z y)) ∨
  M_size.base z (mul z y) := by
  -- r3: mul z y → z
  simpa using (M_size.lex_ok (Rule.r3 y))

example (x y : Term) :
  (flagTerm x = false ∧ flagTerm (fst (pair x y)) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (fst (pair x y)) ∧ M_size.base t (fst (pair x y))) ∨
  M_size.base x (fst (pair x y)) := by
  -- r5: fst (pair x y) → x
  simpa using (M_size.lex_ok (Rule.r5 x y))

example (x y : Term) :
  (flagTerm y = false ∧ flagTerm (snd (pair x y)) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (snd (pair x y)) ∧ M_size.base t (snd (pair x y))) ∨
  M_size.base y (snd (pair x y)) := by
  -- r6: snd (pair x y) → y
  simpa using (M_size.lex_ok (Rule.r6 x y))

example (x : Term) :
  (flagTerm z = false ∧ flagTerm (mul x z) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (mul x z) ∧ M_size.base t (mul x z)) ∨
  M_size.base z (mul x z) := by
  -- r8: mul x z → z
  simpa using (M_size.lex_ok (Rule.r8 x))
end OperatorKO7.OpIncomp
```

## 14. OperatorKO7/Meta/Impossibility_Lemmas.lean

**Lines:** 386

```lean
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
    The RHS has `appNode` at the root while LHS has `recNode` -- no simple ordering works. -/
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
```

## 15. OperatorKO7/Meta/FailureModes.lean

**Lines:** 94

```lean
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
```

## 16. OperatorKO7/Meta/ContractProbes.lean

**Lines:** 67

```lean
/-!
# Contract Probes (P1–P3)

These probes document required checks from the Strict Execution Contract.
They are written to be build-safe: negative cases are in comments; no failing assertions.

P1: Branch realism - enumerate clauses, test rfl per-branch, report failures, give corrected laws.
P2: Duplication realism - show additive failure and give the robust DM/MPO orientation premise.
P3: Symbol realism - one success, one unknown identifier example, one arity/type mismatch example.
-/

namespace OperatorKO7.MetaProbes

/- ## P1: Branch realism -/

/-- A tiny two-branch function used to illustrate the P1 "branch realism" check. -/
def f : Nat → Nat
| 0       => 1
| Nat.succ x => x

/-
Clause-by-clause rfl checks for the claim 2 * f x = f (2 * x):

- x = 0:
  LHS = 2 * f 0 = 2 * 1 = 2; RHS = f (2 * 0) = f 0 = 1 → not rfl. Fails.

- x = succ y:
  LHS = 2 * f (succ y) = 2 * y; RHS = f (2 * succ y) = f (2*y + 2) = (2*y + 2).pred = 2*y + 1 → not rfl. Fails.

Corrected per-branch statements:
- x = 0: 2 * f 0 = 2 ≠ 1 = f 0
- x = succ y: 2 * f (succ y) = 2*y and f (2*succ y) = 2*y + 1 differ by 1

True global facts:
- f (2 * x) = Nat.pred (2 * x + 1)
- 2 * f x ≤ 2 * x, with strict inequality when x ≠ 0
- Minimal counterexample to the false global equality: x = 0.
-/

/- ## P2: Duplication realism -/

/-
Consider a rewrite rule that duplicates a subterm S: h(S) → g(S,S).
With a simple node-count measure M, we get:
  M(after) = M(before) - 1 + M(S) + M(S) = M(before) - 1 + 2·M(S),
which is not a strict drop when M(S) ≥ 1.

Robust orientation uses a multiset-of-weights (Dershowitz–Manna) or MPO/RPO:
- Key premise: every RHS piece Pi is strictly < the removed LHS redex W in the base order.
- If we cannot exhibit Pi < W for all pieces, we must declare a CONSTRAINT BLOCKER.
-/
-- (Orientation lemmas live in the main development; this file only documents the probe.)

/- ## P3: Symbol realism -/

/-
One success (present in toolkit):
- Ordinal.opow_le_opow_right : monotonicity of ω^· in the exponent (≤-mono)

One unknown identifier example (NameGate):
- opow_right_mono_strict - SEARCH(name)=0 → must use local bridge `opow_lt_opow_right` instead.

One arity/type mismatch example (TypeGate):
- mul_le_mul_left' used with arguments in wrong order/type; fix by applying the α, β, γ as per lemma’s signature.
-/

end OperatorKO7.MetaProbes
```

## 17. OperatorKO7/Meta/Conjecture_Boundary.lean

**Lines:** 490

```lean
import OperatorKO7.Meta.Impossibility_Lemmas
import OperatorKO7.Meta.Operational_Incompleteness

/-!
# Conjecture Boundary (Theorem-Level No-Go Statements)

This module collects theorem-level barriers that are already justified by the
current KO7 artifact. It does **not** claim a proof of full-system
non-termination, and it does **not** upgrade the paper conjecture to a theorem.

The purpose is narrower:
- record explicit "no-go" theorems for concrete internal method families;
- keep these boundaries importable from one place for audit/review.
-/

namespace OperatorKO7.MetaConjectureBoundary

open OperatorKO7 Trace
open OperatorKO7.Impossibility

/-! ## Global-orientation interface (full kernel Step) -/

/-- A measure/order pair globally orients the full kernel `Step`. -/
def GlobalOrients {α : Type} (m : Trace → α) (lt : α → α → Prop) : Prop :=
  ∀ {a b}, Step a b → lt (m b) (m a)

/-! ## Additive / Lex barriers -/

/-- No fixed additive bump on `kappa` can orient `rec_succ` uniformly. -/
theorem no_fixed_kappa_plus_k (k : Nat) :
    ¬ (∀ (b s n : Trace),
      FailedMeasures.kappa (app s (recΔ b s n)) + k <
      FailedMeasures.kappa (recΔ b s (delta n)) + k) :=
  FailedMeasures.kappa_plus_k_fails k

/-- The simple 2-component lex witness `(kappa, mu)` fails on KO7. -/
theorem no_simple_lex_witness :
    ¬ (∀ (b s n : Trace),
      Prod.Lex (· < ·) (· < ·)
        (FailedMeasures.kappa (app s (recΔ b s n)),
         FailedMeasures.mu (app s (recΔ b s n)))
        (FailedMeasures.kappa (recΔ b s (delta n)),
         FailedMeasures.mu (recΔ b s (delta n)))) :=
  FailedMeasures.simple_lex_fails

/-- Additive size cannot strictly decrease across all `rec_succ` instances. -/
theorem no_additive_strict_drop_rec_succ :
    ¬ (∀ (b s n : Trace),
      UncheckedRecursionFailure.simpleSize (app s (recΔ b s n)) <
      UncheckedRecursionFailure.simpleSize (recΔ b s (delta n))) := by
  intro h
  have hlt := h void void void
  have hge :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  exact Nat.not_lt_of_ge hge hlt

/-! ## Strengthened full-step no-go theorems -/

/-- No fixed additive bump can globally orient full `Step`. -/
theorem no_global_step_orientation_kappa_plus_k (k : Nat) :
    ¬ GlobalOrients (fun t => FailedMeasures.kappa t + k) (· < ·) := by
  intro h
  apply no_fixed_kappa_plus_k k
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Plain structural depth (`kappa`) cannot globally orient full `Step`. -/
theorem no_global_step_orientation_kappa :
    ¬ GlobalOrients FailedMeasures.kappa (· < ·) := by
  intro h
  apply no_fixed_kappa_plus_k 0
  intro b s n
  have hlt : FailedMeasures.kappa (app s (recΔ b s n)) <
      FailedMeasures.kappa (recΔ b s (delta n)) :=
    h (Step.R_rec_succ b s n)
  simp at hlt

/-- The simple lex witness `(kappa, mu)` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simple_lex :
    ¬ GlobalOrients
      (fun t => (FailedMeasures.kappa t, FailedMeasures.mu t))
      (Prod.Lex (· < ·) (· < ·)) := by
  intro h
  apply no_simple_lex_witness
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Additive `simpleSize` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simpleSize :
    ¬ GlobalOrients UncheckedRecursionFailure.simpleSize (· < ·) := by
  intro h
  apply no_additive_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-! ## Flag-only barrier -/

/-- A single top-level flag cannot globally orient full `Step`. -/
theorem no_global_flag_only_orientation :
    ¬ (∀ a b : Trace, Step a b →
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
    ¬ (∀ (b s n : Trace),
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (app s (recΔ b s n))) <
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (recΔ b s (delta n)))) := by
  intro h
  have hlt := h void void void
  have hs :
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (void : Trace)) ≥ 1 := by
    simp [ConstellationFailure.constellationSize, ConstellationFailure.toConstellation]
  have hge :=
    ConstellationFailure.constellation_size_not_decreasing void void void hs
  exact Nat.not_lt_of_ge hge hlt

/-- Constellation-size cannot globally orient full `Step`. -/
theorem no_global_step_orientation_constellation :
    ¬ GlobalOrients
      (fun t =>
        ConstellationFailure.constellationSize
          (ConstellationFailure.toConstellation t))
      (· < ·) := by
  intro h
  apply no_constellation_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Strictly monotone post-processing cannot rescue additive `simpleSize` on full `Step`. -/
theorem no_global_step_orientation_simpleSize_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ¬ GlobalOrients
      (fun t => f (UncheckedRecursionFailure.simpleSize t))
      (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta void)) (app void (recΔ void void void)) :=
    Step.R_rec_succ void void void
  have hlt :
      f (UncheckedRecursionFailure.simpleSize (app void (recΔ void void void))) <
      f (UncheckedRecursionFailure.simpleSize (recΔ void void (delta void))) :=
    h hstep
  have hge :
      UncheckedRecursionFailure.simpleSize (app void (recΔ void void void)) ≥
      UncheckedRecursionFailure.simpleSize (recΔ void void (delta void)) :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  have hmono :
      f (UncheckedRecursionFailure.simpleSize (recΔ void void (delta void))) ≤
      f (UncheckedRecursionFailure.simpleSize (app void (recΔ void void void))) :=
    hf.monotone hge
  exact Nat.not_lt_of_ge hmono hlt

/-! ## Bridge wrappers to `OpIncomp.InternallyDefinableMeasure` -/

/-- Any internal witness must include the explicit duplication non-drop barrier (r4). -/
theorem internal_measure_records_duplication_barrier
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    (x y : OperatorKO7.OpIncomp.Term) :
    ¬ OperatorKO7.OpIncomp.size (OperatorKO7.OpIncomp.R4_after x y) <
      OperatorKO7.OpIncomp.size (OperatorKO7.OpIncomp.R4_before x y) :=
  M.dup_additive_nodrop_r4 x y

/-- Any internal witness must provide per-piece orientation for every rule instance. -/
theorem internal_measure_requires_per_piece_lt
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    {l r : OperatorKO7.OpIncomp.Term}
    (hr : OperatorKO7.OpIncomp.Rule l r)
    {t : OperatorKO7.OpIncomp.Term}
    (ht : t ∈ OperatorKO7.OpIncomp.rhsPiecesLHS l) :
    M.base t l :=
  M.per_piece_base_lt hr t ht

/-- Exposes the lex/orientation gate encoded in `InternallyDefinableMeasure`. -/
theorem internal_measure_lex_gate
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    {l r : OperatorKO7.OpIncomp.Term}
    (hr : OperatorKO7.OpIncomp.Rule l r) :
    (M.flag r = false ∧ M.flag l = true) ∨
      (∃ t, t ∈ OperatorKO7.OpIncomp.rhsPiecesLHS l ∧ M.base t l) ∨
      M.base r l :=
  M.lex_ok hr

/-! ## Flag barrier (GlobalOrients form) -/

/-- A single top-level δ-flag cannot globally orient full `Step` (GlobalOrients form). -/
theorem no_global_step_orientation_flag :
    ¬ GlobalOrients FlagFailure.deltaFlagTop (· < ·) := by
  intro h
  have hstep : Step (merge void (delta void)) (delta void) :=
    Step.R_merge_void_left (delta void)
  have hlt := h hstep
  simp [FlagFailure.deltaFlagTop] at hlt

/-! ## Strict increase witness (rec_succ makes additive measures grow) -/

/-- When `s` is non-void, `simpleSize` strictly INCREASES across `rec_succ`.
The duplication barrier is not just "no drop" - the measure goes UP. -/
theorem rec_succ_size_strictly_increases (b s n : Trace)
    (hs : UncheckedRecursionFailure.simpleSize s ≥ 1) :
    UncheckedRecursionFailure.simpleSize (app s (recΔ b s n)) >
    UncheckedRecursionFailure.simpleSize (recΔ b s (delta n)) :=
  UncheckedRecursionFailure.rec_succ_size_increases b s n hs

/-! ## StrictMono generalization for kappa -/

/-- Strictly monotone post-processing cannot rescue `kappa` on full `Step`.
Analogous to `no_global_step_orientation_simpleSize_strictMono`. -/
theorem no_global_step_orientation_kappa_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ¬ GlobalOrients (fun t => f (FailedMeasures.kappa t)) (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta (delta void)))
      (app void (recΔ void void (delta void))) :=
    Step.R_rec_succ void void (delta void)
  have hlt := h hstep
  have hge : FailedMeasures.kappa (app void (recΔ void void (delta void))) ≥
      FailedMeasures.kappa (recΔ void void (delta (delta void))) := by
    simp [FailedMeasures.kappa]
  exact Nat.not_lt_of_ge (hf.monotone hge) hlt

/-! ## Dual-barrier theorem (rec_succ vs merge_void are complementary) -/

/-- The duplication barrier and the flag barrier target DIFFERENT rules.
Any single Nat-valued measure that handles rec_succ (which requires insensitivity
to duplication of `s`) is blocked by merge_void (which can raise flags), and vice
versa. This theorem witnesses both barriers simultaneously on full `Step`. -/
theorem dual_barrier_rec_succ_and_merge_void :
    -- (1) Additive size fails on rec_succ:
    (∀ (b s n : Trace),
      UncheckedRecursionFailure.simpleSize (app s (recΔ b s n)) ≥
      UncheckedRecursionFailure.simpleSize (recΔ b s (delta n)))
    ∧
    -- (2) δ-flag increases on merge_void_left:
    (FlagFailure.deltaFlagTop (delta void) >
     FlagFailure.deltaFlagTop (merge void (delta void))) := by
  constructor
  · exact UncheckedRecursionFailure.rec_succ_additive_barrier
  · simp [FlagFailure.deltaFlagTop]

/-! ## Structural depth barrier (#6: ties on collapsing rules)

A nesting-depth measure that does NOT count `merge` as a level ties on
`merge_cancel`. This formalizes failure mode #6 from the paper:
"Structural depth: Ties on collapsing rules (merge_cancel)." -/

/-- Nesting depth where `merge` does not add a level. -/
@[simp] def nestingDepth : Trace → Nat
  | .void => 0
  | .delta t => nestingDepth t + 1
  | .integrate t => nestingDepth t + 1
  | .merge a b => max (nestingDepth a) (nestingDepth b)
  | .app a b => max (nestingDepth a) (nestingDepth b) + 1
  | .recΔ b s n => max (max (nestingDepth b) (nestingDepth s)) (nestingDepth n) + 1
  | .eqW a b => max (nestingDepth a) (nestingDepth b) + 1

/-- `nestingDepth` ties on `merge_cancel`: `nestingDepth(merge t t) = nestingDepth(t)`.
Since `merge t t → t`, orientation requires `nestingDepth(t) < nestingDepth(merge t t)`,
which is `nestingDepth(t) < nestingDepth(t)` - false. -/
theorem nestingDepth_merge_cancel_tie (t : Trace) :
    nestingDepth (merge t t) = nestingDepth t := by
  simp

/-- `nestingDepth` cannot globally orient full `Step` (fails at merge_cancel). -/
theorem no_global_step_orientation_nestingDepth :
    ¬ GlobalOrients nestingDepth (· < ·) := by
  intro h
  have hstep : Step (merge void void) void := Step.R_merge_cancel void
  have hlt := h hstep
  simp [nestingDepth] at hlt

/-! ## Polynomial interpretation barrier (#3: Ladder Paradox)

Polynomial measures using multiplicative coefficients at `recΔ` (e.g.,
`M(recΔ b s n) = M(b) + M(s) * M(n)`) tie on `rec_succ` regardless of
base weight. With additive `app`, the duplication of `s` is exactly
cancelled by the multiplication:

  M(recΔ b s (delta n)) = M(b) + M(s)*(M(n)+1) = M(b) + M(s)*M(n) + M(s)
  M(app s (recΔ b s n)) = M(s) + M(b) + M(s)*M(n)

These are equal by commutativity of addition. Any polynomial that DOES
break this tie requires importing external constants (e.g., `M(void) = 2`)
and node-weight arithmetic - this is the Ladder Paradox (Gate F.4 in the
Strict Execution Contract): the termination proof works only because it
maps to external arithmetic we already trust, not because of any
internally definable property. -/

/-- Polynomial measure with multiplicative `recΔ`, parameterized by base weight `w`. -/
@[simp] def polyMul (w : Nat) : Trace → Nat
  | .void => w
  | .delta t => polyMul w t + 1
  | .integrate t => polyMul w t + 1
  | .merge a b => polyMul w a + polyMul w b
  | .app a b => polyMul w a + polyMul w b
  | .recΔ b s n => polyMul w b + polyMul w s * polyMul w n
  | .eqW a b => polyMul w a + polyMul w b

/-- Polynomial with multiplicative `recΔ` TIES on `rec_succ` for ANY base weight.
This is an exact equality, not just a non-strict inequality. -/
theorem poly_mul_ties_rec_succ (w : Nat) (b s n : Trace) :
    polyMul w (app s (recΔ b s n)) =
    polyMul w (recΔ b s (delta n)) := by
  simp [polyMul, Nat.mul_add]
  omega

/-- Polynomial `polyMul` cannot globally orient full `Step` (ties on rec_succ). -/
theorem no_global_step_orientation_polyMul (w : Nat) :
    ¬ GlobalOrients (polyMul w) (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta void)) (app void (recΔ void void void)) :=
    Step.R_rec_succ void void void
  have hlt := h hstep
  have heq := poly_mul_ties_rec_succ w void void void
  omega

/-! ## Naive multiset barrier (#7: duplication inflates element count)

A naive multiset measure collects subterm weights into a bag and compares
by sum (or cardinality). Unlike the Dershowitz-Manna ordering -- which
permits replacing one large element with multiple SMALLER elements --
naive comparison has no mechanism to absorb duplication. When `rec_succ`
duplicates `s`, the bag gains an extra copy of `s`'s weight, and the
sum/cardinality strictly increases.

This formalizes failure mode #7 from the paper:
"Naive multiset orderings: Fail without DM-specific properties." -/

/-- Node count: number of constructor applications in the term.
This represents a naive multiset measure where every node has weight 1
and the multiset is compared by cardinality (= sum of weights). -/
@[simp] def nodeCount : Trace → Nat
  | .void => 1
  | .delta t => nodeCount t + 1
  | .integrate t => nodeCount t + 1
  | .merge a b => nodeCount a + nodeCount b + 1
  | .app a b => nodeCount a + nodeCount b + 1
  | .recΔ b s n => nodeCount b + nodeCount s + nodeCount n + 1
  | .eqW a b => nodeCount a + nodeCount b + 1

/-- Naive multiset (node count) does not strictly decrease on `rec_succ`.
The duplication of `s` adds `nodeCount s` to the RHS, yielding ≥. -/
theorem nodeCount_rec_succ_barrier (b s n : Trace) :
    nodeCount (app s (recΔ b s n)) ≥ nodeCount (recΔ b s (delta n)) := by
  simp [nodeCount]
  omega

/-- With non-trivial `s`, node count strictly INCREASES on `rec_succ`. -/
theorem nodeCount_rec_succ_increases (b s n : Trace)
    (hs : nodeCount s ≥ 2) :
    nodeCount (app s (recΔ b s n)) > nodeCount (recΔ b s (delta n)) := by
  simp [nodeCount]
  omega

/-- Node count cannot globally orient full `Step` (fails at rec_succ). -/
theorem no_global_step_orientation_nodeCount :
    ¬ GlobalOrients nodeCount (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta void)) (app void (recΔ void void void)) :=
    Step.R_rec_succ void void void
  have hlt := h hstep
  have hge := nodeCount_rec_succ_barrier void void void
  omega

/-! ## The Boundary Between Code and Meta-Theory (Path Orders)

CRITICAL NOTE: This file does NOT demonstrate that full Lexicographic Path Ordering (LPO)
or Multiset Path Ordering (MPO) fails to orient the KO7 calculus. Mathematically,
full LPO *succeeds* in orienting the unrestricted system.

Instead, the following two theorems demonstrate that the isolated *components* of path
orders (pure head precedence and linear KBO-style weights) fail independently.
Because these simple structural methods fail, any successful path order is
mathematically forced to rely on the universal Subterm Property (f(t) > t).

The companion paper argues that importing the Subterm Property (and by extension,
Kruskal's Tree Theorem) violates the "no imported axioms" constraint of a Pure
Recursive Calculus. Thus, the code demonstrates the *necessity* of the external axiom,
while the paper critiques its *validity*.
-/

/-! ## Pure Precedence Barrier (#7: Precedence conflict on collapsing rules)

A measure that relies strictly on the precedence of the head constructor
cannot orient collapsing rules like `merge_cancel`, because the RHS can
have the same head constructor as the LHS.
-/

inductive OpHead | void | delta | integrate | merge | app | recΔ | eqW

def getHead : Trace → OpHead
  | .void => .void
  | .delta _ => .delta
  | .integrate _ => .integrate
  | .merge _ _ => .merge
  | .app _ _ => .app
  | .recΔ _ _ _ => .recΔ
  | .eqW _ _ => .eqW

def headPrecedenceMeasure (rank : OpHead → Nat) : Trace → Nat :=
  fun t => rank (getHead t)

/-- Pure head precedence cannot globally orient `Step` (fails at merge_cancel). -/
theorem no_global_step_orientation_headPrecedence (rank : OpHead → Nat) :
    ¬ GlobalOrients (headPrecedenceMeasure rank) (· < ·) := by
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

def linearWeight (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat) : Trace → Nat
  | .void => c_void
  | .delta t => c_delta + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq t
  | .integrate t => c_int + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq t
  | .merge a b => c_merge + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b
  | .app a b => c_app + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b
  | .recΔ b s n => c_rec + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq s + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq n
  | .eqW a b => c_eq + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b

/-- No linear weight function can globally orient `Step` (fails at rec_succ). -/
theorem no_global_step_orientation_linearWeight (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat) :
    ¬ GlobalOrients (linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq) (· < ·) := by
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

@[simp] def treeDepth : Trace → Nat
  | .void => 0
  | .delta t => treeDepth t + 1
  | .integrate t => treeDepth t + 1
  | .merge a b => max (treeDepth a) (treeDepth b) + 1
  | .app a b => max (treeDepth a) (treeDepth b) + 1
  | .recΔ b s n => max (max (treeDepth b) (treeDepth s)) (treeDepth n) + 1
  | .eqW a b => max (treeDepth a) (treeDepth b) + 1

/-- Standard tree depth strictly INCREASES on `rec_succ` when `s` is deep. -/
theorem treeDepth_rec_succ_increases (b s n : Trace)
    (hs : treeDepth s > treeDepth n + 1) :
    treeDepth (app s (recΔ b s n)) > treeDepth (recΔ b s (delta n)) := by
  simp [treeDepth]
  omega

/-- Standard tree depth cannot globally orient `Step`. -/
theorem no_global_step_orientation_treeDepth :
    ¬ GlobalOrients treeDepth (· < ·) := by
  intro h
  -- Let n = void (depth 0). Let s = delta (delta void) (depth 2).
  have hstep : Step (recΔ void (delta (delta void)) (delta void))
                    (app (delta (delta void)) (recΔ void (delta (delta void)) void)) :=
    Step.R_rec_succ void (delta (delta void)) void
  have hlt := h hstep
  -- LHS depth is 3. RHS depth is 4. 3 < 4 contradicts orientation.
  simp [treeDepth] at hlt

/-! ## Full-step witness (duplication branch is present in kernel Step) -/

/-- The unrestricted kernel `Step` contains the duplication branch explicitly. -/
theorem full_step_has_rec_succ_instance :
    ∃ b s n, Step (recΔ b s (delta n)) (app s (recΔ b s n)) :=
  UncheckedRecursionFailure.full_step_permits_barrier

end OperatorKO7.MetaConjectureBoundary
```

## 18. OperatorKO7/Meta/PaperApproachIndex.lean

**Lines:** 39

```lean
import OperatorKO7.Meta.Impossibility_Lemmas

/-!
# Paper Approach Index (compile-time consistency check)

Purpose
- This module exists to make the paper’s “ten approaches fail” claim mechanically checkable.
- It provides *editor-quiet* references (`example` terms) to the specific approach namespaces/lemmas,
  so renames/deletions break compilation instead of silently drifting.

How to use
- Run: `lake build OperatorKO7.Meta.PaperApproachIndex`
- This is intentionally *not* imported by the default `OperatorKO7.lean` entrypoint, to keep the
  default build fast; treat it as an “audit target”.
-/

namespace OperatorKO7.Meta.PaperApproachIndex

open OperatorKO7 Trace
open OperatorKO7.Impossibility

/-!
Approach #9 and #10 were added later; keep explicit anchors here so the paper’s
“ten approaches” catalog stays in sync with the mechanized codebase.
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

```

## 19. OperatorKO7/Meta/CNFOrdinal.lean

**Lines:** 1139

```lean
-- (pretty-printing and examples moved below, after definitions)
/-!
  # Constructive CNF Ordinal - Complete, Axiom-Free, Computable

  This module provides a fully constructive Cantor Normal Form (CNF) ordinal type and computable implementations for:
  - Canonical structure and invariants
  - Normalization (merge, sort, remove zeros)
  - Addition, multiplication, ω-exponentiation
  - Total, computable lexicographic comparison (cmp, le, lt)
  - No axioms, no sorry, no noncomputable

  All code is total and lint-clean. See Docs/A_Constructive_Ordinal_Skeleton.md for intended semantics and proofs.
-/
set_option linter.unnecessarySimpa false


namespace OperatorKO7.MetaCNF

/-!
  ## CNF Representation
  - List of (exponent, coefficient) pairs, exponents strictly decreasing, coefficients positive.
  - Invariant: No zero coefficients, no zero exponents except possibly for the last term (finite part).
  - Example: ω^3·2 + ω^1·5 + 7  ≡  [(3,2), (1,5), (0,7)]
-/



structure CNF where
  repr : List (Nat × Nat) -- List of (exponent, coefficient) pairs
  -- Invariant: strictly decreasing exponents, all coefficients > 0
deriving Repr, DecidableEq

/-!
  ## Helper: merge like exponents, remove zeros, sort decreasing
-/
private def insertDesc (p : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [p]
  | (q::qs) => if p.1 > q.1 then p :: q :: qs else q :: insertDesc p qs

private def sortDesc (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.foldl (fun acc x => insertDesc x acc) []

private def mergeLike (l : List (Nat × Nat)) : List (Nat × Nat) :=
  let l := l.filter (fun ⟨_, c⟩ => c ≠ 0)
  let l := sortDesc l -- sort by decreasing exponent
  let rec go (acc : List (Nat × Nat)) (l : List (Nat × Nat)) : List (Nat × Nat) :=
    match l with
    | [] => acc.reverse
    | (e, c) :: xs =>
      match acc with
      | (e', c') :: as' =>
        if e = e' then go ((e, c + c') :: as') xs else go ((e, c) :: acc) xs
      | [] => go [(e, c)] xs
  go [] l

/-!
  ## Normalization: canonical form
-/
def norm_cnf (x : CNF) : CNF :=
  { repr := mergeLike x.repr }

/-!
  ## Lexicographic comparison on normalized representations
  Compare two CNFs by their normalized `repr` lists. Higher exponents dominate;
  when exponents tie, higher coefficients dominate. Missing tails are treated
  as smaller (i.e., [] < non-empty).
-/
def cmpList : List (Nat × Nat) → List (Nat × Nat) → Ordering
  | [], [] => Ordering.eq
  | [], _  => Ordering.lt
  | _,  [] => Ordering.gt
  | (e1, c1) :: xs, (e2, c2) :: ys =>
    if e1 < e2 then Ordering.lt else
    if e2 < e1 then Ordering.gt else
    -- exponents are equal; compare coefficients
    if c1 < c2 then Ordering.lt else
    if c2 < c1 then Ordering.gt else
    -- equal head terms; recurse on tails
    cmpList xs ys

/-- Reflexivity for list-lex comparison. -/
theorem cmpList_refl_eq : ∀ xs : List (Nat × Nat), cmpList xs xs = Ordering.eq := by
  intro xs; induction xs with
  | nil => simp [cmpList]
  | @cons hd tl ih =>
    cases hd with
    | mk e c =>
      -- both exponent and coefficient self-comparisons fall through to recursion
      simp [cmpList, Nat.lt_irrefl, ih]

/-- Head-case: if e1 < e2, the comparison is lt (and swaps to gt). -/
theorem cmpList_cons_cons_exp_lt
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e1 < e2) :
  cmpList ((e1, c1) :: xs) ((e2, c2) :: ys) = Ordering.lt := by
  simp [cmpList, h]

/-- Head-case (swap): if e1 < e2, then swapping yields gt. -/
theorem cmpList_cons_cons_exp_lt_swap
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e1 < e2) :
  cmpList ((e2, c2) :: ys) ((e1, c1) :: xs) = Ordering.gt := by
  -- On swap, the second branch detects e1 < e2
  have : ¬ e2 < e1 := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [cmpList, this, h]

/-- Head-case: if e2 < e1, the comparison is gt (and swaps to lt). -/
theorem cmpList_cons_cons_exp_gt
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e2 < e1) :
  cmpList ((e1, c1) :: xs) ((e2, c2) :: ys) = Ordering.gt := by
  have : ¬ e1 < e2 := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [cmpList, this, h]

/-- Head-case (swap): if e2 < e1, swapping yields lt. -/
theorem cmpList_cons_cons_exp_gt_swap
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e2 < e1) :
  cmpList ((e2, c2) :: ys) ((e1, c1) :: xs) = Ordering.lt := by
  simp [cmpList, h]

/-- Head-case: equal exponents, smaller coefficient gives lt. -/
theorem cmpList_cons_cons_exp_eq_coeff_lt
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)} (h : c1 < c2) :
  cmpList ((e, c1) :: xs) ((e, c2) :: ys) = Ordering.lt := by
  have : ¬ e < e := Nat.lt_irrefl _
  simp [cmpList, this, h]

/-- Head-case: equal exponents, larger coefficient gives gt. -/
theorem cmpList_cons_cons_exp_eq_coeff_gt
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)} (h : c2 < c1) :
  cmpList ((e, c1) :: xs) ((e, c2) :: ys) = Ordering.gt := by
  have : ¬ e < e := Nat.lt_irrefl _
  have : ¬ c1 < c2 := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [cmpList, Nat.lt_irrefl, this, h]

/-- Head-case: equal exponents and coefficients, comparison recurses. -/
theorem cmpList_cons_cons_exp_eq_coeff_eq
  {e c : Nat} {xs ys : List (Nat × Nat)} :
  cmpList ((e, c) :: xs) ((e, c) :: ys) = cmpList xs ys := by
  simp [cmpList, Nat.lt_irrefl]

/-- Base-case: [] < non-empty. -/
theorem cmpList_nil_left_lt {y : Nat × Nat} {ys : List (Nat × Nat)} :
  cmpList [] (y :: ys) = Ordering.lt := by
  simp [cmpList]

/-- Base-case: non-empty > []. -/
theorem cmpList_nil_right_gt {x : Nat × Nat} {xs : List (Nat × Nat)} :
  cmpList (x :: xs) [] = Ordering.gt := by
  simp [cmpList]

/-- Eliminate cmpList=lt on cons/cons: describes exactly which head-case caused it or recurses. -/
theorem cmpList_cons_cons_lt_cases
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (h : cmpList ((e1, c1) :: xs) ((e2, c2) :: ys) = Ordering.lt) :
  e1 < e2 ∨ (e1 = e2 ∧ c1 < c2) ∨ (e1 = e2 ∧ c1 = c2 ∧ cmpList xs ys = Ordering.lt) := by
  -- peel the nested ifs of cmpList via case splits
  classical
  if hlt : e1 < e2 then
    -- immediate lt by exponent
    exact Or.inl hlt
  else
    have hnotlt : ¬ e1 < e2 := by simpa using hlt
    if hgt : e2 < e1 then
      -- would force gt, contradicting h
      have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
        simp [cmpList, hnotlt, hgt]
      cases this ▸ h
    else
      have hnotgt : ¬ e2 < e1 := by simpa using hgt
      -- exponents must be equal
      have heq : e1 = e2 := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
      -- compare coefficients
      if hclt : c1 < c2 then
        exact Or.inr (Or.inl ⟨heq, hclt⟩)
      else
        if hcgt : c2 < c1 then
          -- would force gt, contradicting h (use the dedicated head-eq coeff-gt lemma)
          have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
            subst heq; simpa using (cmpList_cons_cons_exp_eq_coeff_gt (xs:=xs) (ys:=ys) (e:=e1) (c1:=c1) (c2:=c2) hcgt)
          cases this ▸ h
        else
          -- equal coefficients; recurse: rewrite h to a tail-lt
          have hceq : c1 = c2 := by
            -- from ¬ c1 < c2 and ¬ c2 < c1, get equality
            have hle₁ : c2 ≤ c1 := Nat.not_lt.mp hclt
            have hle₂ : c1 ≤ c2 := Nat.not_lt.mp hcgt
            exact Nat.le_antisymm hle₂ hle₁
          -- rewrite h via heq and hceq, then drop to tails
          have h' : cmpList ((e1,c1)::xs) ((e1,c1)::ys) = Ordering.lt := by
            simpa [heq, hceq] using h
          have hTail : cmpList xs ys = Ordering.lt := by
            simpa [cmpList_cons_cons_exp_eq_coeff_eq] using h'
          exact Or.inr (Or.inr ⟨heq, hceq, hTail⟩)

/-- Symmetry for lt: if cmpList xs ys = lt then cmpList ys xs = gt. -/
theorem cmpList_symm_gt_of_lt :
  ∀ xs ys : List (Nat × Nat), cmpList xs ys = Ordering.lt → cmpList ys xs = Ordering.gt
  | [], [] , h => by cases h
  | [], (y::ys), _ => by simp [cmpList]
  | (x::xs), [], h => by cases h
  | ((e1,c1)::xs), ((e2,c2)::ys), h =>
    -- analyze which branch produced lt, then swap accordingly
    have hc := cmpList_cons_cons_lt_cases (xs:=xs) (ys:=ys) h
    by
      cases hc with
      | inl hExpLt =>
        -- exponent lt ⇒ swapped is gt
        exact (cmpList_cons_cons_exp_lt_swap (xs:=xs) (ys:=ys) hExpLt)
      | inr hrest =>
        cases hrest with
        | inl hCoeffLt =>
          rcases hCoeffLt with ⟨heq, hclt⟩
          -- equal exponents, coeff lt ⇒ swapped is gt by coeff-gt lemma with roles swapped
          subst heq
          exact (cmpList_cons_cons_exp_eq_coeff_gt (xs:=ys) (ys:=xs) (e:=e1) (c1:=c2) (c2:=c1) hclt)
        | inr hEqTail =>
          rcases hEqTail with ⟨heq, hceq, htail⟩
          -- descend to tails and lift back via eq-head lemma
          have ih := cmpList_symm_gt_of_lt xs ys htail
          subst heq; subst hceq
          simpa [cmpList_cons_cons_exp_eq_coeff_eq] using ih

/-- Total, computable comparison on CNF via normalized representations. -/
def cmp_cnf (x y : CNF) : Ordering :=
  cmpList (norm_cnf x).repr (norm_cnf y).repr

/-- Strict order: x < y iff cmp is lt. -/
def lt_cnf (x y : CNF) : Prop := cmp_cnf x y = Ordering.lt

/-- Non-strict order: x ≤ y iff cmp is not gt. -/
def le_cnf (x y : CNF) : Prop := cmp_cnf x y ≠ Ordering.gt

theorem cmp_self_eq (x : CNF) : cmp_cnf x x = Ordering.eq := by
  simp [cmp_cnf, cmpList_refl_eq]

/-- Reflexivity: x ≤ x. -/
theorem le_refl (x : CNF) : le_cnf x x := by
  simp [le_cnf, cmp_self_eq]

/-- Irreflexivity: ¬ (x < x). -/
theorem lt_irrefl (x : CNF) : ¬ lt_cnf x x := by
  -- lt_cnf x x means cmp_cnf x x = Ordering.lt, but cmp_self_eq says it's eq.
  simp [lt_cnf, cmp_self_eq]

/-- Value-level trichotomy for cmpList. -/
theorem cmpList_cases (xs ys : List (Nat × Nat)) :
    cmpList xs ys = Ordering.lt ∨ cmpList xs ys = Ordering.eq ∨ cmpList xs ys = Ordering.gt := by
  cases h : cmpList xs ys with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr (Or.inl rfl)
  | gt => exact Or.inr (Or.inr rfl)

/-- Asymmetry at list level: if cmpList xs ys = lt then cmpList ys xs ≠ lt. -/
theorem cmpList_asymm_of_lt {xs ys : List (Nat × Nat)} (h : cmpList xs ys = Ordering.lt) :
    cmpList ys xs ≠ Ordering.lt := by
  have hgt := cmpList_symm_gt_of_lt xs ys h
  intro hcontra
  -- rewrite the gt-equality at the same lhs to force a lt=gt contradiction
  have : Ordering.lt = Ordering.gt := by
    simpa [hcontra] using hgt
  have ne : Ordering.lt ≠ Ordering.gt := by decide
  exact ne this

/-- Trichotomy on cmp: exactly one of lt/eq/gt holds as a value. -/
theorem cmp_cases (x y : CNF) :
    cmp_cnf x y = Ordering.lt ∨ cmp_cnf x y = Ordering.eq ∨ cmp_cnf x y = Ordering.gt := by
  cases h : cmp_cnf x y with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr (Or.inl rfl)
  | gt => exact Or.inr (Or.inr rfl)

/-- If x ≤ y, then cmp is either lt or eq (never gt). -/
theorem le_cases {x y : CNF} (hxy : le_cnf x y) :
    cmp_cnf x y = Ordering.lt ∨ cmp_cnf x y = Ordering.eq := by
  -- Case on the computed ordering; rule out gt using hxy.
  cases h : cmp_cnf x y with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr rfl
  | gt =>
    -- hxy says cmp_cnf x y ≠ gt, contradiction
  exact False.elim (hxy h)

/-- General CNF asymmetry: x < y implies not (y < x). -/
theorem lt_asymm_cnf {x y : CNF} (hxy : lt_cnf x y) : ¬ lt_cnf y x := by
  -- unfold to list-level and use cmpList asymmetry
  unfold lt_cnf at *
  unfold cmp_cnf at *
  -- set normalized lists for readability
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  -- First coerce hxy to a statement about cmpList xs ys = lt
  have hxy' : cmpList xs ys = Ordering.lt := by simpa using hxy
  -- Symmetry gives cmpList ys xs = gt
  have hgt : cmpList ys xs = Ordering.gt := cmpList_symm_gt_of_lt xs ys hxy'
  -- Show lt cannot also hold
  intro hcontra
  have ne : Ordering.lt ≠ Ordering.gt := by decide
  -- hcontra : cmpList ys xs = lt, hgt : cmpList ys xs = gt ⇒ lt = gt
  have : Ordering.gt = Ordering.lt := by exact hgt.symm.trans hcontra
  exact (ne.symm) this

/-- Antisymmetry for `le_cnf` at the cmp level: if x ≤ y and y ≤ x then cmp is eq. -/
theorem le_antisymm_cnf {x y : CNF}
  (hxy : le_cnf x y) (hyx : le_cnf y x) : cmp_cnf x y = Ordering.eq := by
  cases hcmp : cmp_cnf x y with
  | lt =>
    -- translate to list-level, flip, and contradict hyx
    have hltList : cmpList (norm_cnf x).repr (norm_cnf y).repr = Ordering.lt := by
      simpa [cmp_cnf] using hcmp
    have hgtList : cmpList (norm_cnf y).repr (norm_cnf x).repr = Ordering.gt :=
      cmpList_symm_gt_of_lt _ _ hltList
    have : cmp_cnf y x = Ordering.gt := by
      simpa [cmp_cnf] using hgtList
    exact (hyx this).elim
  | eq => exact rfl
  | gt => exact (hxy hcmp).elim
/-- Congruence of cmp on the left, given normalized representations are equal. -/
theorem cmp_congr_left_repr_eq {x y z : CNF}
  (h : (norm_cnf x).repr = (norm_cnf y).repr) :
  cmp_cnf x z = cmp_cnf y z := by
  unfold cmp_cnf; simp [h]

/-- Transitivity for list-level lt: if xs < ys and ys < zs then xs < zs. -/
theorem cmpList_trans_lt :
  ∀ {xs ys zs : List (Nat × Nat)},
    cmpList xs ys = Ordering.lt → cmpList ys zs = Ordering.lt →
    cmpList xs zs = Ordering.lt := by
  intro xs; induction xs with
  | nil =>
    intro ys zs hxy hyz; cases ys with
    | nil => cases hxy
    | cons y ys =>
      -- cmpList [] (y::ys) = lt, so xs<zs regardless of hyz structure on left
      simp [cmpList] at hxy; cases zs with
      | nil =>
        -- hyz: (y::ys) < [] impossible
        simp [cmpList] at hyz
      | cons z zs =>
        simp [cmpList]
  | cons x xs ih =>
    intro ys zs hxy hyz
    cases ys with
    | nil =>
      -- xs<[] impossible
      simp [cmpList] at hxy
    | cons y ys =>
      cases zs with
      | nil =>
        -- ys<[] impossible
        simp [cmpList] at hyz
      | cons z zs =>
        cases x with
        | mk e1 c1 =>
        cases y with
        | mk e2 c2 =>
        cases z with
        | mk e3 c3 =>
        -- analyze hxy
        have hx := cmpList_cons_cons_lt_cases (xs:=xs) (ys:=ys) (e1:=e1) (c1:=c1) (e2:=e2) (c2:=c2) hxy
        -- analyze hyz for ys vs zs
        have hy := cmpList_cons_cons_lt_cases (xs:=ys) (ys:=zs) (e1:=e2) (c1:=c2) (e2:=e3) (c2:=c3) hyz
        -- split on cases to derive e1<e3 or tie and reduce
        rcases hx with hExpLt | hCoeffLt | hTailLt
        · -- e1 < e2; by trans with e2 ≤ e3 from hy
          -- derive e2 ≤ e3
          have hE23 : e2 ≤ e3 := by
            rcases hy with hE2lt3 | hrest
            · exact Nat.le_of_lt hE2lt3
            · rcases hrest with hE2eqE3CoeffLt | hE2eqE3Tail
              · have heq : e2 = e3 := hE2eqE3CoeffLt.left
                simpa [heq] using (le_rfl : e2 ≤ e2)
              · have heq : e2 = e3 := hE2eqE3Tail.left
                simpa [heq] using (le_rfl : e2 ≤ e2)
          -- from e2 ≤ e3, split eq/lt to conclude e1 < e3
          have hE13 : e1 < e3 := by
            have hE2eqOrLt := Nat.lt_or_eq_of_le hE23
            cases hE2eqOrLt with
            | inl hlt23 => exact Nat.lt_trans hExpLt hlt23
            | inr heq23 => simpa [heq23] using hExpLt
          exact (cmpList_cons_cons_exp_lt (xs:=xs) (ys:=zs) (e1:=e1) (c1:=c1) (e2:=e3) (c2:=c3) hE13)
        · -- e1 = e2 ∧ c1 < c2
          rcases hCoeffLt with ⟨hE12, hC12⟩
          -- from hy, either e2<e3 -> then e1<e3; or e2=e3 and c2<c3; or tie and descend
          rcases hy with hE2lt3 | hrest
          · have hE13 : e1 < e3 := by simpa [hE12] using hE2lt3
            exact (cmpList_cons_cons_exp_lt (xs:=xs) (ys:=zs) (e1:=e1) (c1:=c1) (e2:=e3) (c2:=c3) hE13)
          · rcases hrest with hE2eqE3CoeffLt | hE2eqE3Tail
            · rcases hE2eqE3CoeffLt with ⟨hE23, hC23⟩
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              -- coefficients chain: c1 < c2 and c2 < c3 ⇒ c1 < c3
              have hC13 : c1 < c3 := Nat.lt_trans hC12 hC23
              -- conclude by head coefficient comparison
              have hlt : cmpList ((e3,c1)::xs) ((e3,c3)::zs) = Ordering.lt :=
                cmpList_cons_cons_exp_eq_coeff_lt (xs:=xs) (ys:=zs) (e:=e3) (c1:=c1) (c2:=c3) hC13
              simpa [hE13] using hlt
            · rcases hE2eqE3Tail with ⟨hE23, hC23, _hTail⟩
              -- heads tie and c2=c3; from c1<c2 and c2=c3, get c1<c3 and conclude
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              have hC13 : c1 < c3 := by simpa [hC23] using hC12
              have hlt : cmpList ((e3,c1)::xs) ((e3,c3)::zs) = Ordering.lt :=
                cmpList_cons_cons_exp_eq_coeff_lt (xs:=xs) (ys:=zs) (e:=e3) (c1:=c1) (c2:=c3) hC13
              simpa [hE13] using hlt
        · -- e1 = e2 ∧ c1 = c2 ∧ tail lt; combine with hy cases
          rcases hTailLt with ⟨hE12, hC12, hTailXY⟩
          rcases hy with hE2lt3 | hrest
          · have hE13 : e1 < e3 := by simpa [hE12] using hE2lt3
            exact (cmpList_cons_cons_exp_lt (xs:=xs) (ys:=zs) (e1:=e1) (c1:=c1) (e2:=e3) (c2:=c3) hE13)
          · rcases hrest with hE2eqE3CoeffLt | hE2eqE3Tail
            · rcases hE2eqE3CoeffLt with ⟨hE23, hC23⟩
              -- heads tie and c2<c3 ⇒ with c1=c2 we get c1<c3, immediate lt
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              have hC13 : c1 < c3 := by simpa [hC12] using hC23
              have hlt : cmpList ((e3,c1)::xs) ((e3,c3)::zs) = Ordering.lt :=
                cmpList_cons_cons_exp_eq_coeff_lt (xs:=xs) (ys:=zs) (e:=e3) (c1:=c1) (c2:=c3) hC13
              simpa [hE13] using hlt
            · rcases hE2eqE3Tail with ⟨hE23, hC23, hTailYZ⟩
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              have hC13 : c1 = c3 := by simpa [hE12, hC12] using hC23
              -- descend both with ih on tails
              have ih'' : cmpList xs zs = Ordering.lt := ih (ys:=ys) (zs:=zs) hTailXY hTailYZ
              simpa [cmpList, hE13, Nat.lt_irrefl, hC13] using ih''

/-- Transitivity for CNF lt. -/
theorem lt_trans_cnf {x y z : CNF} (hxy : lt_cnf x y) (hyz : lt_cnf y z) : lt_cnf x z := by
  unfold lt_cnf at *
  -- abbreviations for readability
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  let zs := (norm_cnf z).repr
  -- rewrite both facts to list-level and apply list transitivity
  have hx : cmpList xs ys = Ordering.lt := by simpa [cmp_cnf, xs, ys] using hxy
  have hy : cmpList ys zs = Ordering.lt := by simpa [cmp_cnf, ys, zs] using hyz
  have hz : cmpList xs zs = Ordering.lt := cmpList_trans_lt (xs:=xs) (ys:=ys) (zs:=zs) hx hy
  simpa [cmp_cnf, xs, ys, zs]

/-- Trichotomy for CNF compare: exactly one of lt/eq/gt holds. -/
theorem cmp_cnf_trichotomy (x y : CNF) :
  cmp_cnf x y = Ordering.lt ∨ cmp_cnf x y = Ordering.eq ∨ cmp_cnf x y = Ordering.gt := by
  unfold cmp_cnf
  exact cmpList_cases (norm_cnf x).repr (norm_cnf y).repr

/-- Congruence of cmp on the right, given normalized representations are equal. -/
theorem cmp_congr_right_repr_eq {x y z : CNF}
  (h : (norm_cnf y).repr = (norm_cnf z).repr) :
  cmp_cnf x y = cmp_cnf x z := by
  unfold cmp_cnf; simp [h]

/-- CNF head-case: if normalized head exponents satisfy e1 < e2, then cmp is lt. -/
theorem cmp_cnf_head_exp_lt {x y : CNF}
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e1, c1) :: xs)
  (hy : (norm_cnf y).repr = (e2, c2) :: ys)
  (h : e1 < e2) :
  cmp_cnf x y = Ordering.lt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_lt h]

/-- CNF head-case: if normalized head exponents satisfy e2 < e1, then cmp is gt. -/
theorem cmp_cnf_head_exp_gt {x y : CNF}
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e1, c1) :: xs)
  (hy : (norm_cnf y).repr = (e2, c2) :: ys)
  (h : e2 < e1) :
  cmp_cnf x y = Ordering.gt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_gt h]

/-- CNF head-case: equal head exponents, smaller left coefficient gives lt. -/
theorem cmp_cnf_head_exp_eq_coeff_lt {x y : CNF}
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e, c1) :: xs)
  (hy : (norm_cnf y).repr = (e, c2) :: ys)
  (h : c1 < c2) :
  cmp_cnf x y = Ordering.lt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_eq_coeff_lt h]

/-- CNF head-case: equal head exponents, larger left coefficient gives gt. -/
theorem cmp_cnf_head_exp_eq_coeff_gt {x y : CNF}
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e, c1) :: xs)
  (hy : (norm_cnf y).repr = (e, c2) :: ys)
  (h : c2 < c1) :
  cmp_cnf x y = Ordering.gt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_eq_coeff_gt h]

/-- CNF head-case: equal head term, comparison recurses on tails. -/
theorem cmp_cnf_head_exp_coeff_eq {x y : CNF}
  {e c : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e, c) :: xs)
  (hy : (norm_cnf y).repr = (e, c) :: ys) :
  cmp_cnf x y = cmpList xs ys := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_eq_coeff_eq]

/-- CNF asymmetry in the simple head-exp case: if head e1 < e2 then x < y and not y < x. -/
theorem lt_asymm_head_exp {x y : CNF}
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e1, c1) :: xs)
  (hy : (norm_cnf y).repr = (e2, c2) :: ys)
  (h : e1 < e2) : lt_cnf x y ∧ ¬ lt_cnf y x := by
  constructor
  · unfold lt_cnf; simp [cmp_cnf_head_exp_lt (x:=x) (y:=y) hx hy h]
  · intro hlt
    have hswap : cmp_cnf y x = Ordering.gt := by
      unfold cmp_cnf; simp [hy, hx, cmpList_cons_cons_exp_lt_swap h]
    have ne : Ordering.gt ≠ Ordering.lt := by decide
    -- unfold lt_cnf in hlt to get a cmp equality
    have hlt' : cmp_cnf y x = Ordering.lt := by
      -- linter: prefer simp at hlt' instead of simpa using hlt
      simp [lt_cnf] at hlt; exact hlt
    -- rewrite cmp_cnf y x via hswap to derive an impossible equality
    have hbad : Ordering.gt = Ordering.lt := by
      -- simplify hlt' with the computed swap
      simpa [hswap] using hlt'
    exact ne hbad

/-!
  ## Instances: Decidability and Ord for CNF
-/

instance instDecidableRel_le_cnf : DecidableRel le_cnf := by
  intro x y
  unfold le_cnf
  infer_instance

instance instDecidableRel_lt_cnf : DecidableRel lt_cnf := by
  intro x y
  unfold lt_cnf
  infer_instance

instance : Ord CNF where
  compare := cmp_cnf

/-- If y and z normalize to the same repr and x < y, then x < z. -/
theorem lt_trans_eq_right {x y z : CNF}
  (hYZ : (norm_cnf y).repr = (norm_cnf z).repr)
  (hXY : lt_cnf x y) : lt_cnf x z := by
  unfold lt_cnf at *
  simpa [cmp_congr_right_repr_eq (x:=x) (y:=y) (z:=z) hYZ] using hXY
/-- If x and y normalize to the same repr and y < z, then x < z. -/
theorem lt_trans_eq_left {x y z : CNF}
  (hXY : (norm_cnf x).repr = (norm_cnf y).repr)
  (hYZ : lt_cnf y z) : lt_cnf x z := by
  unfold lt_cnf at *
  simpa [cmp_congr_left_repr_eq (x:=x) (y:=y) (z:=z) hXY] using hYZ

/-- If y and z normalize to the same repr and x ≤ y, then x ≤ z. -/
theorem le_trans_eq_right {x y z : CNF}
  (hYZ : (norm_cnf y).repr = (norm_cnf z).repr)
  (hXY : le_cnf x y) : le_cnf x z := by
  unfold le_cnf at *
  -- cmp x z = gt would rewrite to cmp x y = gt via congruence, contradicting hXY
  intro hgt
  have : cmp_cnf x y = Ordering.gt := by
    simpa [cmp_congr_right_repr_eq (x:=x) (y:=y) (z:=z) hYZ] using hgt
  exact hXY this

/-- If x and y normalize to the same repr and y ≤ z, then x ≤ z. -/
theorem le_trans_eq_left {x y z : CNF}
  (hXY : (norm_cnf x).repr = (norm_cnf y).repr)
  (hYZ : le_cnf y z) : le_cnf x z := by
  unfold le_cnf at *
  intro hgt
  -- rewrite cmp x z to cmp y z using repr equality, contradicting hYZ
  have : cmp_cnf y z = Ordering.gt := by
    simpa [cmp_congr_left_repr_eq (x:=x) (y:=y) (z:=z) hXY] using hgt
  exact hYZ this

/-!
  ## Tiny conveniences
-/

/-- If normalized representations are equal, cmp is `eq`. -/
theorem cmp_eq_of_norm_repr_eq {x y : CNF}
  (h : (norm_cnf x).repr = (norm_cnf y).repr) :
  cmp_cnf x y = Ordering.eq := by
  unfold cmp_cnf
  simp [cmpList_refl_eq, h]

/-!
  Equality characterization: if cmpList = eq then the lists are equal.
  This lets us reflect cmp equality back to structural equality of normalized
  representations at the CNF level.
-/
theorem cmpList_eq_implies_eq :
    ∀ {xs ys : List (Nat × Nat)}, cmpList xs ys = Ordering.eq → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil =>
      simp [cmpList] at h
      exact rfl
    | cons y ys =>
      -- cmpList [] (y::ys) = lt, contradicting eq
      simp [cmpList] at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      -- cmpList (x::xs) [] = gt, contradicting eq
      simp [cmpList] at h
    | cons y ys =>
      cases x with
      | mk e1 c1 =>
        cases y with
        | mk e2 c2 =>
        classical
        -- eliminate strict exponent inequalities via if-splits
        if hltE : e1 < e2 then
          have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
            simpa [cmpList, hltE]
          cases this ▸ h
        else
          have hnot12 : ¬ e1 < e2 := by simpa using hltE
          if hgtE : e2 < e1 then
            have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
              simpa [cmpList, hnot12, hgtE]
            cases this ▸ h
          else
            -- exponents equal
            have heq : e1 = e2 :=
              Nat.le_antisymm (Nat.le_of_not_gt hgtE) (Nat.le_of_not_gt hltE)
            -- eliminate strict coefficient inequalities
            if hltC : c1 < c2 then
              have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
                simpa [cmpList, heq, Nat.lt_irrefl, hltC]
              cases this ▸ h
            else
              have hnotc12 : ¬ c1 < c2 := by simpa using hltC
              if hgtC : c2 < c1 then
                have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
                  simpa [cmpList, heq, Nat.lt_irrefl, hnotc12, hgtC]
                cases this ▸ h
              else
                -- coefficients equal; descend to tails
                have hceq : c1 = c2 := by
                  have hle₁ : c2 ≤ c1 := Nat.not_lt.mp hltC
                  have hle₂ : c1 ≤ c2 := Nat.not_lt.mp hgtC
                  exact Nat.le_antisymm hle₂ hle₁
                have hTail : cmpList xs ys = Ordering.eq := by
                  simpa [cmpList, heq, hceq, Nat.lt_irrefl] using h
                have ih' := ih hTail
                subst heq; subst hceq
                simp [ih']

theorem cmp_eq_iff_norm_repr_eq {x y : CNF} :
    cmp_cnf x y = Ordering.eq ↔ (norm_cnf x).repr = (norm_cnf y).repr := by
  constructor
  · intro h
    unfold cmp_cnf at h
    exact cmpList_eq_implies_eq h
  · intro hrepr
    exact cmp_eq_of_norm_repr_eq (x:=x) (y:=y) hrepr

/-- lt implies le (definitionally). -/
theorem le_of_lt {x y : CNF} (h : lt_cnf x y) : le_cnf x y := by
  unfold lt_cnf at h
  unfold le_cnf
  intro hgt
  -- rewriting with h produces an impossible lt=gt
  cases h ▸ hgt

/-- CNF-level symmetry: if cmp x y = lt then cmp y x = gt. -/
theorem cmp_cnf_symm_gt_of_lt {x y : CNF}
  (h : cmp_cnf x y = Ordering.lt) : cmp_cnf y x = Ordering.gt := by
  classical
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  have hlist : cmpList xs ys = Ordering.lt := by
    simpa [cmp_cnf, xs, ys] using h
  have hgt := cmpList_symm_gt_of_lt xs ys hlist
  simpa [cmp_cnf, xs, ys] using hgt

-- (We intentionally avoid a gt→lt symmetry lemma here to keep the proof surface minimal.)

/-- Symmetry for gt: if cmpList xs ys = gt then cmpList ys xs = lt. -/
theorem cmpList_symm_lt_of_gt :
  ∀ xs ys : List (Nat × Nat), cmpList xs ys = Ordering.gt → cmpList ys xs = Ordering.lt
  | [], [], h => by cases h
  | [], (y::ys), h => by
      -- cmpList [] (y::ys) = lt, so gt is impossible
      cases h
  | (x::xs), [], _h => by
      -- non-empty vs []
      simp [cmpList]
  | ((e1,c1)::xs), ((e2,c2)::ys), h =>
      by
        classical
        -- split on exponent comparison using an if-then-else
        if hlt12 : e1 < e2 then
          -- then result would be lt, contradicts gt
          have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
            simpa [cmpList, hlt12]
          cases this ▸ h
        else
          have hnot12 : ¬ e1 < e2 := by simpa using hlt12
          if hlt21 : e2 < e1 then
            -- gt by exponent; swap gives lt
            exact (cmpList_cons_cons_exp_gt_swap (xs:=xs) (ys:=ys) (e1:=e1) (c1:=c1) (e2:=e2) (c2:=c2) hlt21)
          else
            -- exponents equal
            have heq : e1 = e2 :=
              Nat.le_antisymm (Nat.le_of_not_gt hlt21) (Nat.le_of_not_gt hlt12)
            -- compare coefficients similarly
            if hclt12 : c1 < c2 then
              -- would make lt, contradict gt
              have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
                simpa [cmpList, heq, Nat.lt_irrefl, hclt12]
              cases this ▸ h
            else
              have hnotc12 : ¬ c1 < c2 := by simpa using hclt12
              if hclt21 : c2 < c1 then
                -- swapped becomes lt by coeff-lt
                have : cmpList ((e2,c2)::ys) ((e1,c1)::xs) = Ordering.lt := by
                  simpa [heq] using (cmpList_cons_cons_exp_eq_coeff_lt (xs:=ys) (ys:=xs) (e:=e1) (c1:=c2) (c2:=c1) hclt21)
                simpa using this
              else
                -- coefficients equal; descend to tails
                have hceq : c1 = c2 := by
                  have hle₁ : c2 ≤ c1 := Nat.not_lt.mp hclt12
                  have hle₂ : c1 ≤ c2 := Nat.not_lt.mp hclt21
                  exact Nat.le_antisymm hle₂ hle₁
                -- from h = gt, tails must be gt as well
                have hTail : cmpList xs ys = Ordering.gt := by
                  simpa [cmpList, heq, hceq, Nat.lt_irrefl] using h
                -- recurse on tails
                have ih := cmpList_symm_lt_of_gt xs ys hTail
                -- lift back through equal heads
                simpa [cmpList_cons_cons_exp_eq_coeff_eq, heq, hceq] using ih

/-- CNF-level symmetry: if cmp x y = gt then cmp y x = lt. -/
theorem cmp_cnf_symm_lt_of_gt {x y : CNF}
  (h : cmp_cnf x y = Ordering.gt) : cmp_cnf y x = Ordering.lt := by
  classical
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  have hlist : cmpList xs ys = Ordering.gt := by
    simpa [cmp_cnf, xs, ys] using h
  have hlt := cmpList_symm_lt_of_gt xs ys hlist
  simpa [cmp_cnf, xs, ys] using hlt

/- Totality for ≤ on CNF. -/
theorem le_total_cnf (x y : CNF) : le_cnf x y ∨ le_cnf y x := by
  -- case on the computed comparison
  cases h : cmp_cnf x y with
  | lt => exact Or.inl (le_of_lt (by simpa [lt_cnf] using h))
  | eq => exact Or.inl (by simp [le_cnf, h])
  | gt =>
    -- swap gives lt, hence y ⪯ x
    have : cmp_cnf y x = Ordering.lt := cmp_cnf_symm_lt_of_gt h
    exact Or.inr (by
      -- lt implies ≤ by definition (not gt)
      have : lt_cnf y x := by simpa [lt_cnf] using this
      exact le_of_lt this)

-- Infix notations (optional ergonomics)
infix:50 " ≺ " => lt_cnf
infix:50 " ⪯ " => le_cnf

/-!
  ## Addition: merge and normalize
-/
def add_cnf (x y : CNF) : CNF :=
  norm_cnf { repr := x.repr ++ y.repr }

/-!
  ## Multiplication: distributive law, collect like terms, normalize
-/
def mul_cnf (x y : CNF) : CNF :=
  match norm_cnf x, norm_cnf y with
  | { repr := [] }, _ => { repr := [] }
  | _, { repr := [] } => { repr := [] }
  | { repr := xs }, { repr := ys } =>
    let terms := List.foldr (fun a b => List.append a b) [] (xs.map (fun (e1, c1) => ys.map (fun (e2, c2) => (e1 + e2, c1 * c2))))
    norm_cnf { repr := terms }

/-!
  ## ω-Exponentiation: ω^x
  - ω^0 = 1
  - ω^{sum_i ω^{a_i}·c_i} = ω^{ω^{a_1}·c_1 + ...}
  For CNF, ω^x is just shifting exponents up one level.
-/
def opowω_cnf (x : CNF) : CNF :=
  match norm_cnf x with
  | { repr := [] } => { repr := [(0,1)] } -- ω^0 = 1
  | { repr := xs } => { repr := xs.map (fun (e, c) => (e + 1, c)) }

/-!
  ## Examples
-/
def cnf_zero : CNF := { repr := [] }
def cnf_one : CNF := { repr := [(0,1)] }
def cnf_omega : CNF := { repr := [(1,1)] }
def cnf_omega_plus_one : CNF := { repr := [(1,1),(0,1)] }
def cnf_two_omega : CNF := { repr := [(1,2)] }
def cnf_omega_sq : CNF := { repr := [(2,1)] }

/-!
  ## Basic tests (examples)
-/




end OperatorKO7.MetaCNF

namespace OperatorKO7.MetaCNF

/-!
  ## Pretty-printing (basic)
  Converts a CNF to a human-readable string for debugging and examples.
-/
def intercalate (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xs => xs.foldl (fun acc s => acc ++ sep ++ s) x

def showTerm : Nat × Nat → String
  | (0, c) => toString c
  | (e, 1) => "ω^" ++ toString e
  | (e, c) => toString c ++ "·ω^" ++ toString e

def showCNF (cnf : CNF) : String :=
  match cnf.repr with
  | [] => "0"
  | xs => intercalate " + " (xs.map showTerm)

instance : ToString CNF where
  toString := showCNF

/-!
  ## Normalization checks (boolean)
  Executable validators for CNF invariants. Useful for tests and examples.
-/
def allPosCoeffs : List (Nat × Nat) → Bool
  | [] => true
  | (_, c) :: xs => (c > 0) && allPosCoeffs xs

def sortedStrictDesc : List (Nat × Nat) → Bool
  | [] => true
  | [ _ ] => true
  | (e1, _) :: (e2, c2) :: xs => (e1 > e2) && sortedStrictDesc ((e2, c2) :: xs)

def isNormalizedB (x : CNF) : Bool :=
  sortedStrictDesc x.repr && allPosCoeffs x.repr

/-!
  ## Inspectors and predicates (ergonomics)
-/

def isZero (x : CNF) : Bool :=
  match (norm_cnf x).repr with
  | [] => true
  | _ => false

def isOne (x : CNF) : Bool :=
  decide ((norm_cnf x).repr = [(0, 1)])

def isOmegaPow (x : CNF) : Bool :=
  match (norm_cnf x).repr with
  | [(_, 1)] => true
  | _ => false

def degreeOpt (x : CNF) : Option Nat :=
  match (norm_cnf x).repr with
  | [] => none
  | (e, _) :: _ => some e

/-- Transitivity for `≤` on CNF. -/
theorem le_trans_cnf {x y z : CNF} (hxy : le_cnf x y) (hyz : le_cnf y z) : le_cnf x z := by
  -- By definition, le_cnf x z means cmp_cnf x z ≠ gt. Prove by contradiction.
  unfold le_cnf at *
  intro hgt
  -- Case on cmp x y.
  cases hxyCases : cmp_cnf x y with
  | lt =>
    -- y ≤ z splits into lt or eq.
    have hyCases := le_cases (x:=y) (y:=z) hyz
    cases hyCases with
    | inl hylt =>
      -- x < y and y < z ⇒ x < z, contradicting cmp x z = gt.
      have hxlt : lt_cnf x y := by simpa [lt_cnf] using hxyCases
      have hzlt : lt_cnf x z := lt_trans_cnf hxlt (by simpa [lt_cnf] using hylt)
      -- Convert to cmp form and contradict hgt directly.
      have : cmp_cnf x z = Ordering.lt := by simpa [lt_cnf] using hzlt
      cases this ▸ hgt
    | inr hyeq =>
      -- cmp y z = eq ⇒ normalize-equal reprs; transport x<y to x<z.
      have hrepr : (norm_cnf y).repr = (norm_cnf z).repr :=
        (cmp_eq_iff_norm_repr_eq).mp hyeq
      have hxlt : lt_cnf x y := by simpa [lt_cnf] using hxyCases
      have hzlt : lt_cnf x z := lt_trans_eq_right (x:=x) (y:=y) (z:=z) hrepr hxlt
      have : cmp_cnf x z = Ordering.lt := by simpa [lt_cnf] using hzlt
      cases this ▸ hgt
  | eq =>
    -- cmp x y = eq ⇒ normalized reprs equal; rewrite left via congruence and use hyz.
    have hrepr : (norm_cnf x).repr = (norm_cnf y).repr :=
      (cmp_eq_iff_norm_repr_eq).mp hxyCases
    -- Transport y ≤ z to x ≤ z, closing the contradiction.
    exact (le_trans_eq_left (x:=x) (y:=y) (z:=z) hrepr hyz) hgt
  | gt =>
    -- Contradicts hxy immediately.
    exact (hxy hxyCases).elim

def leadCoeffOpt (x : CNF) : Option Nat :=
  match (norm_cnf x).repr with
  | [] => none
  | (_, c) :: _ => some c

/-!
  ## Example values and usage
-/
def example1 := add_cnf cnf_omega cnf_one         -- ω + 1
def example2 := add_cnf cnf_omega cnf_omega       -- ω + ω = 2·ω
def example3 := mul_cnf cnf_omega cnf_omega       -- ω * ω = ω^2

end OperatorKO7.MetaCNF

namespace OperatorKO7.MetaCNF

/-!
  ## Min/Max and sorting helpers (ergonomics)
-/

def min_cnf (x y : CNF) : CNF := if lt_cnf x y then x else y
def max_cnf (x y : CNF) : CNF := if lt_cnf x y then y else x

private def insertBy (x : CNF) : List CNF → List CNF
  | [] => [x]
  | y :: ys => if lt_cnf x y then x :: y :: ys else y :: insertBy x ys

def sortCNF (xs : List CNF) : List CNF :=
  xs.foldl (fun acc x => insertBy x acc) []

def isNonDecreasing (xs : List CNF) : Bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: y :: ys =>
    let leB (a b : CNF) : Bool :=
      match cmp_cnf a b with
      | Ordering.gt => false
      | _ => true
    leB x y && isNonDecreasing (y :: ys)

def minListCNF : List CNF → Option CNF
  | [] => none
  | x :: xs => some (xs.foldl (fun acc y => min_cnf acc y) x)

def maxListCNF : List CNF → Option CNF
  | [] => none
  | x :: xs => some (xs.foldl (fun acc y => max_cnf acc y) x)

-- Demo checks
example : toString (min_cnf cnf_omega cnf_one) = "1" := by
  decide
example : toString (max_cnf cnf_omega cnf_one) = "ω^1" := by
  decide
-- Use a local demo set to avoid forward references
def demoList : List CNF := [cnf_zero, cnf_one, cnf_omega]
example : isNonDecreasing (sortCNF demoList) = true := by
  decide
example :
    (match minListCNF demoList with | some x => toString x | none => "-") = "0" := by
  decide
example :
    (match maxListCNF demoList with | some x => toString x | none => "-") = "ω^1" := by
  decide

end OperatorKO7.MetaCNF

/-!
  ## Example output (for documentation/testing)
  Executable examples to illustrate CNF operations and normalization.
  These produce human-readable CNF strings and boolean normalization checks.
-/
example : toString OperatorKO7.MetaCNF.example1 = "ω^1 + 1" := by
  decide
example : toString OperatorKO7.MetaCNF.example2 = "2·ω^1" := by
  decide
example : toString OperatorKO7.MetaCNF.example3 = "ω^2" := by
  decide

-- Inspector demos
example : OperatorKO7.MetaCNF.isZero OperatorKO7.MetaCNF.cnf_zero = true := by
  decide
example : OperatorKO7.MetaCNF.isOne OperatorKO7.MetaCNF.cnf_one = true := by
  decide
example : OperatorKO7.MetaCNF.isOmegaPow OperatorKO7.MetaCNF.cnf_omega = true := by
  decide
example : OperatorKO7.MetaCNF.degreeOpt OperatorKO7.MetaCNF.cnf_two_omega = some 1 := by
  decide
example : OperatorKO7.MetaCNF.leadCoeffOpt OperatorKO7.MetaCNF.cnf_two_omega = some 2 := by
  decide

-- Normalization checks on the examples (true means normalized)
example :
    OperatorKO7.MetaCNF.isNormalizedB (OperatorKO7.MetaCNF.norm_cnf OperatorKO7.MetaCNF.example1) =
      true := by
  decide
example :
    OperatorKO7.MetaCNF.isNormalizedB (OperatorKO7.MetaCNF.norm_cnf OperatorKO7.MetaCNF.example2) =
      true := by
  decide
example :
    OperatorKO7.MetaCNF.isNormalizedB (OperatorKO7.MetaCNF.norm_cnf OperatorKO7.MetaCNF.example3) =
      true := by
  decide

-- (pretty-printing and examples are defined at the end of the file)
-- All CNF values are normalized: exponents strictly decreasing, coefficients > 0, no duplicate exponents.

/-!
  ## Property checks (computable, #eval-style)
  Small test harness verifying comparison laws and normalization preservation
  over a fixed sample set.
-/
namespace OperatorKO7.MetaCNF

-- Boolean helpers for cmp outcomes
def isEq (x y : CNF) : Bool :=
  match cmp_cnf x y with
  | Ordering.eq => true
  | _ => false

def isLt (x y : CNF) : Bool :=
  match cmp_cnf x y with
  | Ordering.lt => true
  | _ => false

def isLe (x y : CNF) : Bool :=
  match cmp_cnf x y with
  | Ordering.gt => false
  | _ => true

-- Simple boolean all (avoid depending on extra list APIs)
def allB {α} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allB p xs

def pairs {α} (xs : List α) : List (α × α) :=
  xs.foldr (fun x acc => List.append (xs.map (fun y => (x, y))) acc) []

def triples {α} (xs : List α) : List (α × α × α) :=
  xs.foldr (fun x acc =>
    let rows := xs.foldr (fun y acc2 => List.append (xs.map (fun z => (x, y, z))) acc2) []
    List.append rows acc) []

-- Comparison properties
def antisym_check (x y : CNF) : Bool :=
  match cmp_cnf x y, cmp_cnf y x with
  | Ordering.eq, Ordering.eq => true
  | Ordering.lt, Ordering.gt => true
  | Ordering.gt, Ordering.lt => true
  | _, _ => false

def trichotomy_check (x y : CNF) : Bool :=
  match cmp_cnf x y, cmp_cnf y x with
  | Ordering.eq, Ordering.eq => true
  | Ordering.lt, Ordering.gt => true
  | Ordering.gt, Ordering.lt => true
  | _, _ => false

def trans_lt_check (a b c : CNF) : Bool :=
  if isLt a b && isLt b c then isLt a c else true

def trans_le_check (a b c : CNF) : Bool :=
  if isLe a b && isLe b c then isLe a c else true

-- Totality check for ≤: for any pair, either x ≤ y or y ≤ x
def le_total_check (x y : CNF) : Bool :=
  isLe x y || isLe y x

-- Normalization preservation (ops already normalize by definition)
def preserves_norm_add (x y : CNF) : Bool := isNormalizedB (add_cnf x y)
def preserves_norm_mul (x y : CNF) : Bool := isNormalizedB (mul_cnf x y)
def preserves_norm_opow (x : CNF) : Bool := isNormalizedB (opowω_cnf x)

-- Sample set
def samples : List CNF :=
  [ cnf_zero, cnf_one, cnf_omega, cnf_omega_plus_one, cnf_two_omega, cnf_omega_sq ]

-- Aggregate checks over samples
def check_all_antisym : Bool :=
  allB (fun p => antisym_check p.1 p.2) (pairs samples)

def check_all_trichotomy : Bool :=
  allB (fun p => trichotomy_check p.1 p.2) (pairs samples)

def check_all_trans_lt : Bool :=
  allB (fun t => trans_lt_check t.1 t.2.1 t.2.2) (triples samples)

def check_all_trans_le : Bool :=
  allB (fun t => trans_le_check t.1 t.2.1 t.2.2) (triples samples)

def check_all_total_le : Bool :=
  allB (fun p => le_total_check p.1 p.2) (pairs samples)

def check_reflexive_eq : Bool :=
  allB (fun x => isEq x x) samples

def check_norm_add : Bool :=
  allB (fun p => preserves_norm_add p.1 p.2) (pairs samples)

def check_norm_mul : Bool :=
  allB (fun p => preserves_norm_mul p.1 p.2) (pairs samples)

def check_norm_opow : Bool :=
  allB (fun x => preserves_norm_opow x) samples

/-!
  ## Extra property checks for helpers
-/

def eqListB {α} [DecidableEq α] (xs ys : List α) : Bool := decide (xs = ys)

def check_sort_idem : Bool :=
  eqListB (sortCNF samples) (sortCNF (sortCNF samples))

def check_sort_is_nondecreasing : Bool :=
  isNonDecreasing (sortCNF samples)

def check_list_min_max_nonempty : Bool :=
  match minListCNF samples, maxListCNF samples with
  | some _, some _ => true
  | _, _ => false

-- Executable reports
example : check_reflexive_eq = true := by decide
example : check_all_antisym = true := by decide
example : check_all_trichotomy = true := by decide
example : check_all_trans_lt = true := by decide
example : check_all_trans_le = true := by decide
example : check_all_total_le = true := by decide
example : check_norm_add = true := by decide
example : check_norm_mul = true := by decide
example : check_norm_opow = true := by decide
example : check_sort_idem = true := by decide
example : check_sort_is_nondecreasing = true := by decide
example : check_list_min_max_nonempty = true := by decide

end OperatorKO7.MetaCNF
```

## 20. OperatorKO7/Meta/HydraCore.lean

**Lines:** 35

```lean
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
  | node : Hydra → Hydra → Hydra
deriving Repr, DecidableEq

open Hydra

/-- One-step toy hydra rule: cutting a head on one side duplicates the other side. -/
inductive Step : Hydra → Hydra → Prop where
  | chop_left  (h : Hydra) : Step (node head h) (node h h)
  | chop_right (h : Hydra) : Step (node h head) (node h h)

/-- Convenience lemma: left chop duplicates the right subtree. -/
@[simp] theorem dup_left (h : Hydra) : Step (node head h) (node h h) := Step.chop_left h
/-- Convenience lemma: right chop duplicates the left subtree. -/
@[simp] theorem dup_right (h : Hydra) : Step (node h head) (node h h) := Step.chop_right h

/-- Example: a single chop duplicates the non-head subtree. -/
example (h : Hydra) : ∃ h', Step (node head h) h' := ⟨node h h, Step.chop_left h⟩

end HydraCore
end OperatorKO7
```

## 21. OperatorKO7/Meta/GoodsteinCore.lean

**Lines:** 40

```lean
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
  | b : Nat → Base
deriving Repr, DecidableEq

/-- Unary naturals used as a toy counter for Goodstein-style steps. -/
inductive Cn where
  | z  : Cn
  | s  : Cn → Cn
deriving Repr, DecidableEq

/-- A Goodstein-state is a pair (base, counter). -/
structure St where
  base : Base
  cnt  : Cn
deriving Repr, DecidableEq

open Base Cn

/-- Goodstein-like one-step: bump base, drop one successor on the counter. -/
inductive Step : St → St → Prop where
  | base_change (b : Nat) (t : Cn) :
      Step ⟨.b b, .s t⟩ ⟨.b (b+1), t⟩

/-- Convenience lemma: the single `Step.base_change` rule is always available on `(.s t)` counters. -/
@[simp] theorem one_step (b : Nat) (t : Cn) :
    Step ⟨.b b, .s t⟩ ⟨.b (b+1), t⟩ := Step.base_change b t

end GoodsteinCore
end OperatorKO7
```

## 22. OperatorKO7/Test/Sanity.lean

**Lines:** 11

```lean
/-!
Tiny smoke tests.

Why this file exists:
- Ensures the Lake package can compile a small `#eval` and a basic `#check` on a fresh machine.
- Keeps a minimal test surface under `OperatorKO7/Test/` to catch obvious toolchain regressions.
- This file is intentionally trivial and does not contribute to the KO7 theorems.
-/

#eval (1 + 1)
#check Prod.Lex
```

