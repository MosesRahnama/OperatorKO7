import OperatorKO7.Meta.Termination
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Basic

/-!
Strong normalization for the KO7 safe fragment (`SafeStep`), via a triple-lex measure.

This module is the core "certified artifact" development:
- It defines the guarded one-step relation `SafeStep` (a subrelation of the full kernel `Step`).
- It defines the termination measure(s) used to prove `SafeStepRev` is well-founded.

Key design boundary (central to the paper):
- `Step` in `OperatorKO7/Kernel.lean` is the full kernel relation (8 unconditional root rules).
- `SafeStep` adds explicit guards (most importantly, `eqW`-diff requires `a ≠ b`) to obtain a fragment
  that admits a certified termination argument.
- This file proves termination and supplies measure-decrease lemmas *only for `SafeStep`*, not for the
  full `Step` relation.

Main exports:
- `SafeStep` and its reverse `SafeStepRev`
- `deltaFlag`, `kappaM`, and the triple-lex measure `μ3` / order `Lex3`
- `measure_decreases_safe` and `wf_SafeStepRev`
-/
set_option linter.unnecessarySimpa false
open OperatorKO7 Trace Multiset Ordinal

namespace MetaSN_DM
-- Use Dershowitz-Manna multiset order.
-- DM order over multisets of ℕ, using the ambient < on ℕ
local infix:70 " <ₘ " => Multiset.IsDershowitzMannaLT

-- This file treats `b` in `recΔ b s n` as κ-relevant for κᴹ to support DM drops on rec_zero.
-- set_option linter.unusedVariables false

/-- **Weight** of a trace: recursion-depth of each `recΔ` node. -/
@[simp] def weight : Trace → ℕ
| recΔ _ _ n => weight n + 1
| _          => 0

/-- Multiset of weights appearing in a trace.
Note on design (assessment closure): we use multiset union `∪` at merge/app/eqW
nodes rather than additive `+`. This deliberately captures duplication by
conflating identical weights, which works with the DM order we use to
orient duplicating rules. This is a documented deviation from the most
common DM presentations (which often use multiset sum) and is required by
our kernel’s shapes; see `SAFE_AUDIT.md` (root) for rationale and
per-rule checks. -/
@[simp] def kappaM : Trace → Multiset ℕ
| void            => 0
| delta t         => kappaM t
| integrate t     => kappaM t
| merge a b       => kappaM a ∪ kappaM b

| app   a b       => kappaM a ∪ kappaM b
| recΔ b s n      => (weight n + 1) ::ₘ (kappaM n ∪ kappaM s) + kappaM b
| eqW  a b        => kappaM a ∪ kappaM b

/-- Well-foundedness of the DM multiset order (requires `WellFoundedLT` on the base type). -/
instance : WellFoundedLT ℕ := inferInstance

/-- Well-foundedness of the Dershowitz-Manna order on multisets of naturals. -/
lemma wf_dm : WellFounded (fun a b : Multiset ℕ => a <ₘ b) :=
  Multiset.wellFounded_isDershowitzMannaLT

/-- Combined measure pair `(κᴹ, μ)` for the O-7 kernel. -/
noncomputable def μκ (t : Trace) : Multiset ℕ × Ordinal :=
  (kappaM t, MetaSN.mu t)

/-- Lexicographic order on the combined pair. -/
@[simp] def LexDM : (Multiset ℕ × Ordinal) → (Multiset ℕ × Ordinal) → Prop :=
  Prod.Lex (fun a b : Multiset ℕ => a <ₘ b) (· < ·)

/-- Well-foundedness of `LexDM`, combining DM on `κᴹ` and `<` on ordinal payload `μ`. -/
lemma wf_LexDM : WellFounded LexDM :=
  WellFounded.prod_lex wf_dm Ordinal.lt_wf


/-- Lift a DM witness on κᴹ to the inner lex order `(κᴹ, μ)`.
This is a trivial `Prod.Lex.left` step, useful when the μ component is irrelevant. -/
lemma dm_to_LexDM_left {X Y : Multiset ℕ} {μ₁ μ₂ : Ordinal}
    (h : X <ₘ Y) : LexDM (X, μ₁) (Y, μ₂) := by
  -- Use the left constructor with explicit parameters to avoid inference fragility
  exact
    (Prod.Lex.left
      (α := Multiset ℕ) (β := Ordinal)
      (ra := fun a b : Multiset ℕ => a <ₘ b) (rb := (· < ·))
      (a₁ := X) (a₂ := Y) (b₁ := μ₁) (b₂ := μ₂)
      (by simpa using h))


/-- κᴹ ties on `integrate (delta t)` (retains all weights of t). -/
@[simp] lemma kappaM_int_delta (t : Trace) :
    kappaM (integrate (delta t)) = kappaM t := by
  simp [kappaM]

/-- κᴹ ties on `merge void t`. -/
@[simp] lemma kappaM_merge_void_left (t : Trace) :
    kappaM (merge void t) = kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_merge_void_right (t : Trace) :
    kappaM (merge t void) = kappaM t := by
  simp [kappaM]

-- κᴹ duplicates on merge cancel
@[simp] lemma kappaM_merge_cancel (t : Trace) :
    kappaM (merge t t) = kappaM t ∪ kappaM t := by
  simp [kappaM]

/-- κᴹ value for `recΔ b s void`. -/
@[simp] lemma kappaM_rec_zero (b s : Trace) :
    kappaM (recΔ b s void) = (1 ::ₘ kappaM s) + kappaM b := by
  simp [kappaM]

/-- κᴹ equality for `eq_refl`. -/
@[simp] lemma kappaM_eq_refl (a : Trace) :
    kappaM (eqW a a) = kappaM a ∪ kappaM a := by
  simp [kappaM]

@[simp] lemma kappaM_eq_diff (a b : Trace) :
    kappaM (integrate (merge a b)) = kappaM (eqW a b) := by
  simp [kappaM]

/-! ### DM strict drop helpers -/

-- Adding a nonempty multiset strictly increases under DM (choose Y = 0, Z ≠ 0).
lemma dm_lt_add_of_ne_zero (X Z : Multiset ℕ) (h : Z ≠ 0) :
    X <ₘ (X + Z) := by
  classical
  refine ⟨X, (0 : Multiset ℕ), Z, ?hZ, ?hM, rfl, ?hY⟩
  · simpa using h
  · simp
  · simp

-- Public alias for reuse outside this namespace, same statement
lemma dm_lt_add_of_ne_zero' (X Z : Multiset ℕ) (h : Z ≠ 0) :
    Multiset.IsDershowitzMannaLT X (X + Z) := by
  classical
  refine ⟨X, (0 : Multiset ℕ), Z, ?hZ, ?hM, rfl, ?hY⟩
  · simpa using h
  · simp
  · simp

-- κᴹ strictly drops for rec_zero in the intended orientation (LHS > RHS):
-- kappaM b <ₘ kappaM (recΔ b s void)
lemma dm_drop_R_rec_zero (b s : Trace) :
    kappaM b <ₘ kappaM (recΔ b s void) := by
  classical
  -- kappaM (recΔ b s void) = (1 ::ₘ kappaM s) + kappaM b, and + is commutative
  have hdm : Multiset.IsDershowitzMannaLT (kappaM b) (kappaM b + (1 ::ₘ kappaM s)) :=
    dm_lt_add_of_ne_zero' (kappaM b) (1 ::ₘ kappaM s) (by simp)
  -- rewrite to the rec_zero shape
  simpa [kappaM, add_comm, add_left_comm, add_assoc] using hdm

-- update dm_drop_R_rec_succ lemma
-- Note: κM does not strictly drop for rec_succ in DM in general when kappaM uses ∪.
-- Use the μ component for the lex drop in the combined measure.

/-- If a multiset is nonempty, its self-union is nonempty. -/
lemma union_self_ne_zero_of_ne_zero {X : Multiset ℕ} (h : X ≠ 0) :
    X ∪ X ≠ (0 : Multiset ℕ) := by
  classical
  intro hU
  -- Show `X ∪ X = X` by counts, then contradict `h`.
  have hUU : X ∪ X = X := by
    ext a; simp [Multiset.count_union, max_self]
  exact h (by simpa [hUU] using hU)

end MetaSN_DM

/-! --------------------------------------------------------------------------
Triple-lex measure (δ, κᴹ, μ) specialized for KO7
We use a δ-flag that is 1 exactly on `recΔ b s (delta n)` at the top, and 0 otherwise.
This gives a Nat-first strict drop for `R_rec_succ` and ties elsewhere.
--------------------------------------------------------------------------- -/

namespace MetaSN_KO7

open MetaSN_DM

@[simp] def deltaFlag : Trace → Nat
| recΔ _ _ (delta _) => 1
| _                  => 0

-- deltaFlag simplification lemmas for common constructors
@[simp] lemma deltaFlag_void : deltaFlag void = 0 := rfl
@[simp] lemma deltaFlag_integrate (t : Trace) : deltaFlag (integrate t) = 0 := rfl
@[simp] lemma deltaFlag_merge (a b : Trace) : deltaFlag (merge a b) = 0 := rfl
@[simp] lemma deltaFlag_eqW (a b : Trace) : deltaFlag (eqW a b) = 0 := rfl
@[simp] lemma deltaFlag_app (a b : Trace) : deltaFlag (app a b) = 0 := rfl
@[simp] lemma deltaFlag_rec_zero (b s : Trace) : deltaFlag (recΔ b s void) = 0 := by
  simp [deltaFlag]
@[simp] lemma deltaFlag_rec_delta (b s n : Trace) : deltaFlag (recΔ b s (delta n)) = 1 := by
  simp [deltaFlag]

-- deltaFlag takes only values 0 or 1 (decidable Boolean flag over Nat)
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
      | integrate _ => simp [deltaFlag]
      | merge _ _ => simp [deltaFlag]
      | app _ _ => simp [deltaFlag]
      | eqW _ _ => simp [deltaFlag]
      | recΔ _ _ _ => simp [deltaFlag]
  | eqW a b => simp

noncomputable def μ3 (t : Trace) : Nat × (Multiset ℕ × Ordinal) :=
  (deltaFlag t, (kappaM t, MetaSN.mu t))

@[simp] def Lex3 : (Nat × (Multiset ℕ × Ordinal)) → (Nat × (Multiset ℕ × Ordinal)) → Prop :=
  Prod.Lex (· < ·) MetaSN_DM.LexDM

lemma wf_Lex3 : WellFounded Lex3 := by
  exact WellFounded.prod_lex Nat.lt_wfRel.wf MetaSN_DM.wf_LexDM

/-!
Assessment closure: All strong-normalization and decrease lemmas in this
module are scoped to `SafeStep` and the single measure `μ3` (Lex3). We do
not assert SN for the full `Step` relation here, and we do not rely on any
disjunctive/“hybrid” measure in these theorems. See
`SAFE_AUDIT.md` (root) for details and scope statements.
-/

/- Per-rule decreases (stable subset) -------------------------------------- -/

/-- merge void-left: restricted to δ-flag tie (deltaFlag t = 0). -/
lemma drop_R_merge_void_left_zero (t : Trace)
    (hδ : deltaFlag t = 0) :
    Lex3 (μ3 t) (μ3 (merge void t)) := by
  classical
  -- Build inner LexDM μ-drop anchored at κM t
  have hin : LexDM (kappaM t, MetaSN.mu t)
      (kappaM t, MetaSN.mu (merge void t)) :=
    Prod.Lex.right (kappaM t) (MetaSN.mu_lt_merge_void_left t)
  -- Build outer α=0 witness, then rewrite goal to α=0 shape
  have hcore : Lex3 (0, (kappaM t, MetaSN.mu t)) (0, (kappaM t, MetaSN.mu (merge void t))) :=
    Prod.Lex.right (0 : Nat) hin
  dsimp [Lex3, μ3, deltaFlag]
  have ht0 : (match t with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by
    simpa [deltaFlag] using hδ
  simp [ht0]
  exact hcore

/-- merge void-right: restricted to δ-flag tie (deltaFlag t = 0). -/
lemma drop_R_merge_void_right_zero (t : Trace)
    (hδ : deltaFlag t = 0) :
    Lex3 (μ3 t) (μ3 (merge t void)) := by
  classical
  -- Inner μ-drop anchored at κM t
  have hin : LexDM (kappaM t, MetaSN.mu t)
      (kappaM t, MetaSN.mu (merge t void)) :=
    Prod.Lex.right (kappaM t) (MetaSN.mu_lt_merge_void_right t)
  -- Outer α=0 witness
  have hcore : Lex3 (0, (kappaM t, MetaSN.mu t)) (0, (kappaM t, MetaSN.mu (merge t void))) :=
    Prod.Lex.right (0 : Nat) hin
  dsimp [Lex3, μ3, deltaFlag]
  have ht0 : (match t with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by
    simpa [deltaFlag] using hδ
  simp [ht0]
  exact hcore

/-- eq_diff: `eqW a b → integrate (merge a b)` drops (outer tie + μ-right). -/
lemma drop_R_eq_diff (a b : Trace) :
    Lex3 (μ3 (integrate (merge a b))) (μ3 (eqW a b)) := by
  classical
  -- Inner μ-drop anchored at κM (integrate (merge a b))
  have hin : LexDM (kappaM (integrate (merge a b)), MetaSN.mu (integrate (merge a b)))
      (kappaM (integrate (merge a b)), MetaSN.mu (eqW a b)) :=
    Prod.Lex.right (kappaM (integrate (merge a b))) (MetaSN.mu_lt_eq_diff a b)
  -- Outer α=0 witness
  have hcore : Lex3 (0, (kappaM (integrate (merge a b)), MetaSN.mu (integrate (merge a b))))
      (0, (kappaM (integrate (merge a b)), MetaSN.mu (eqW a b))) :=
    Prod.Lex.right (0 : Nat) hin
  -- Rewrite both δ-flags to 0 and κ via kappaM_eq_diff, then discharge
  dsimp [Lex3, μ3]
  have hδL : (match integrate (merge a b) with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by
    simp
  have hδR : (match eqW a b with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by
    simp
  simpa [hδL, hδR, MetaSN_DM.kappaM_eq_diff] using hcore



-- (rec_succ and rec_zero lemmas will be reintroduced after further audit)

-- Aggregated `measure_decreases` and `strong_normalization_triple` are deferred
-- until we resolve the general `merge_cancel` and `eq_refl` cases (κ duplicates).

end MetaSN_KO7
/-! ### Additional per-rule decreases (audited) ---------------------------- -/

namespace MetaSN_KO7

open MetaSN_DM

open Classical

/-!
Lex3 drops for duplicating cases, using a DM drop when κM ≠ 0 and
falling back to a μ-drop when κM ties at 0.
-/

/-- int∘delta: `integrate (delta t) → void` drops (outer δ tie; inner by κ-DM or μ-right). -/
lemma drop_R_int_delta (t : Trace) :
    Lex3 (μ3 void) (μ3 (integrate (delta t))) := by
  classical
  -- Either strict κ-DM when κᴹ t ≠ 0, or μ-right when κ ties at 0; then lift to α=0.
  by_cases h0 : kappaM t = 0
  · -- κ tie → use μ drop
    have hin : LexDM ((0 : Multiset ℕ), MetaSN.mu void)
        ((0 : Multiset ℕ), MetaSN.mu (integrate (delta t))) :=
      Prod.Lex.right (0 : Multiset ℕ) (MetaSN.mu_void_lt_integrate_delta t)
    have hcore : Lex3 (0, ((0 : Multiset ℕ), MetaSN.mu void))
        (0, ((0 : Multiset ℕ), MetaSN.mu (integrate (delta t)))) :=
      Prod.Lex.right (0 : Nat) hin
    simpa [μ3, Lex3, deltaFlag, kappaM_int_delta, h0] using hcore
  · -- κ strict: 0 <ᴹ κᴹ t, rewrite κ for integrate∘delta
    have hdm : Multiset.IsDershowitzMannaLT (0 : Multiset ℕ) (kappaM t) := by
      have hcore := dm_lt_add_of_ne_zero' (0 : Multiset ℕ) (kappaM t) (by simp [h0])
      simpa [zero_add] using hcore
    -- Lift DM to LexDM and then to α=0
    have hin : LexDM ((0 : Multiset ℕ), MetaSN.mu void)
        (kappaM (integrate (delta t)), MetaSN.mu (integrate (delta t))) :=
      dm_to_LexDM_left (X := (0 : Multiset ℕ)) (Y := kappaM (integrate (delta t)))
        (μ₁ := MetaSN.mu void) (μ₂ := MetaSN.mu (integrate (delta t)))
        (by simpa [kappaM_int_delta] using hdm)
    have hcore : Lex3 (0, ((0 : Multiset ℕ), MetaSN.mu void))
        (0, (kappaM (integrate (delta t)), MetaSN.mu (integrate (delta t)))) :=
      Prod.Lex.right (0 : Nat) hin
    simpa [μ3, Lex3, deltaFlag] using hcore

/-- rec_succ: `recΔ b s (delta n) → app s (recΔ b s n)` drops via δ-left (1 → 0). -/
lemma drop_R_rec_succ (b s n : Trace) :
  Lex3 (μ3 (app s (recΔ b s n))) (μ3 (recΔ b s (delta n))) := by
  -- Outer: δ-flag goes from 1 to 0, so we can use the left constructor.
  dsimp [μ3, Lex3, deltaFlag]
  -- goal is Prod.Lex (<) _ (0, _) (1, _)
  apply Prod.Lex.left
  exact Nat.zero_lt_one

/-- rec_zero: `recΔ b s void → b` drops (outer δ tie; inner κ-DM-left). -/
lemma drop_R_rec_zero (b s : Trace)
    (hδ : deltaFlag b = 0) :
    Lex3 (μ3 b) (μ3 (recΔ b s void)) := by
  classical
  -- Work at the expanded pair level but keep deltaFlag uninterpreted until after rewriting
  dsimp [Lex3]
  dsimp [μ3]
  -- Compute δ flags on both sides
  have hb0eq : (match b with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by
    simpa [deltaFlag] using hδ
  have hr0eq : (match recΔ b s void with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by
    simp
  -- rewrite both outers to 0, then use right-branch
  -- Be explicit on both sides to avoid constructor unification flakiness
  simp [hb0eq]
  refine Prod.Lex.right (0 : Nat) ?inner
  -- Inner: lift the DM drop to LexDM explicitly, then rewrite κ to the goal's normal form
  have hlexDM : LexDM (kappaM b, MetaSN.mu b)
      (kappaM (recΔ b s void), MetaSN.mu (recΔ b s void)) :=
    dm_to_LexDM_left (X := kappaM b) (Y := kappaM (recΔ b s void))
      (μ₁ := MetaSN.mu b) (μ₂ := MetaSN.mu (recΔ b s void))
      (by simpa using dm_drop_R_rec_zero b s)
  -- Match the RHS κ with the goal shape (1 ::ₘ (kappaM s + kappaM b))
  simpa [kappaM_rec_zero, cons_add, add_assoc, add_left_comm, add_comm] using hlexDM

end MetaSN_KO7

/-! Thin alias wrappers to expose the “δ-substitution” naming used in the 5‑Pro checklist. -/

namespace MetaSN_KO7

@[simp] lemma delta_subst_drop_rec_succ (b s n : Trace) :
  Lex3 (μ3 (app s (recΔ b s n))) (μ3 (recΔ b s (delta n))) :=
  drop_R_rec_succ b s n

@[simp] lemma delta_subst_drop_rec_zero (b s : Trace)
    (hδ : deltaFlag b = 0) :
    Lex3 (μ3 b) (μ3 (recΔ b s void)) :=
  drop_R_rec_zero b s hδ

end MetaSN_KO7

/-! ### Additional safe KO7 lemmas (restricted) --------------------------- -/

namespace MetaSN_KO7

open MetaSN_DM

-- Restricted merge-cancel: require δ-tie and κ=0 so we can take μ-right.
-- NOTE (CONSTRAINT): A fully unguarded KO7 lemma for merge_cancel cannot hold:
-- if t = recΔ _ _ (delta _), then deltaFlag t = 1 while deltaFlag (merge t t) = 0.
-- In Lex3 with outer Nat <, we cannot have 1 < 0 (outer-left) nor tie 1 = 0 (outer-right),
-- so a KO7 drop needs the δ-tie hypothesis (deltaFlag t = 0). For the unguarded case,
-- use the MPO variant `mpo_drop_R_merge_cancel`, which ignores δ.
lemma drop_R_merge_cancel_zero (t : Trace)
    (hδ : deltaFlag t = 0) (h0 : kappaM t = 0) :
    Lex3 (μ3 t) (μ3 (merge t t)) := by
  classical
  -- Outer δ tie via hδ: rewrite both sides to 0 so left components match syntactically
  -- Then take the right branch in the outer lex.
  -- Build an inner LexDM proof first, keeping LexDM opaque
  have hin : LexDM (kappaM t, MetaSN.mu t)
      (kappaM t ∪ kappaM t, MetaSN.mu (merge t t)) := by
    -- κ tie via h0; then μ-right using mu_lt_merge_cancel
    dsimp [LexDM]
    -- Now goal: Prod.Lex DM (<) (kappaM t, μ t) (kappaM t ∪ kappaM t, μ (merge t t))
    -- Tie on DM (becomes 0 with h0), take μ-right
    simp [h0]
    exact
      (Prod.Lex.right
        (α := Multiset ℕ) (β := Ordinal)
        (ra := fun a b : Multiset ℕ => Multiset.IsDershowitzMannaLT a b)
        (rb := (· < ·))
        (a := (0 : Multiset ℕ))
        (MetaSN.mu_lt_merge_cancel t))
  -- Lift to outer α = 0
  have hcore : Lex3 (0, (kappaM t, MetaSN.mu t))
      (0, (kappaM t ∪ kappaM t, MetaSN.mu (merge t t))) :=
    Prod.Lex.right (0 : Nat) hin
  -- Now rewrite the goal to the α = 0 shape and apply hcore
  dsimp [μ3, Lex3, deltaFlag]
  -- Replace the LHS deltaFlag by 0 using hδ; RHS deltaFlag is 0 by simp
  have ht0 : (match t with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by
    simpa [deltaFlag] using hδ
  -- Also normalize the RHS merge-case δ-flag to 0
  simp [ht0]
  -- Apply the outer right with inner witness hcore
  exact hcore

-- Restricted eq_refl: require κ=0 so we can μ-right under inner tie.
lemma drop_R_eq_refl_zero (a : Trace) (h0 : kappaM a = 0) :
    Lex3 (μ3 void) (μ3 (eqW a a)) := by
  classical
  -- Outer δ-tie: unfold δ and take right branch
  dsimp [μ3, Lex3, deltaFlag]
  refine Prod.Lex.right (0 : Nat) ?inner
  simp [h0]
  refine Prod.Lex.right (0 : Multiset ℕ) ?muDrop
  exact MetaSN.mu_void_lt_eq_refl a

/-- eq_refl: unguarded KO7 drop. If κᴹ a = 0, use μ-right; otherwise take κ-DM-left. -/
lemma drop_R_eq_refl (a : Trace) :
    Lex3 (μ3 void) (μ3 (eqW a a)) := by
  classical
  -- Build an inner LexDM witness first, then lift to an α=0 outer step and rewrite the goal.
  have hin : LexDM ((0 : Multiset ℕ), MetaSN.mu void)
      (kappaM (eqW a a), MetaSN.mu (eqW a a)) := by
    -- Case split on κᴹ a
    by_cases h0 : kappaM a = 0
    · -- κ tie → μ-right at inner level
      have hin0 : LexDM ((0 : Multiset ℕ), MetaSN.mu void)
          ((0 : Multiset ℕ), MetaSN.mu (eqW a a)) := by
        exact
          (Prod.Lex.right
            (α := Multiset ℕ) (β := Ordinal)
            (ra := fun a b : Multiset ℕ => Multiset.IsDershowitzMannaLT a b)
            (rb := (· < ·))
            (a := (0 : Multiset ℕ))
            (MetaSN.mu_void_lt_eq_refl a))
      simpa [kappaM_eq_refl, h0] using hin0
    · -- κ ≠ 0 → DM-left on 0 <ₘ κ∪κ, then rewrite κ on RHS to kappaM (eqW a a)
      have hU : kappaM a ∪ kappaM a ≠ (0 : Multiset ℕ) :=
        union_self_ne_zero_of_ne_zero (X := kappaM a) h0
      have hdm0 : Multiset.IsDershowitzMannaLT (0 : Multiset ℕ) (kappaM a ∪ kappaM a) := by
        simpa using dm_lt_add_of_ne_zero' (0 : Multiset ℕ) (kappaM a ∪ kappaM a) hU
      have hlex : LexDM (0, MetaSN.mu void)
          (kappaM a ∪ kappaM a, MetaSN.mu (eqW a a)) := by
        exact dm_to_LexDM_left (X := (0 : Multiset ℕ)) (Y := kappaM a ∪ kappaM a)
          (μ₁ := MetaSN.mu void) (μ₂ := MetaSN.mu (eqW a a)) hdm0
      simpa [kappaM_eq_refl] using hlex
  -- Lift to outer α=0 and finalize by rewriting δ-flag to 0 on both sides
  have hcore : Lex3 (0, ((0 : Multiset ℕ), MetaSN.mu void))
      (0, (kappaM (eqW a a), MetaSN.mu (eqW a a))) :=
    Prod.Lex.right (0 : Nat) hin
  dsimp [Lex3, μ3]
  have hδL : (match void with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by rfl
  have hδR : (match eqW a a with | recΔ _ _ (delta _) => 1 | _ => 0) = 0 := by simp
  simpa [hδL, hδR] using hcore


end MetaSN_KO7

/-! ### Parametric strong normalization wrapper for KO7 ------------------- -/

namespace MetaSN_KO7

open OperatorKO7

def StepRev : Trace → Trace → Prop := fun a b => OperatorKO7.Step b a

/-- If every kernel step strictly decreases the KO7 measure μ3 in Lex3,
then the reverse relation is well-founded (no infinite reductions). -/
theorem strong_normalisation_of_decreases
  (hdec : ∀ {a b : Trace}, OperatorKO7.Step a b → Lex3 (μ3 b) (μ3 a)) :
  WellFounded StepRev := by
  -- Pull back the well-founded Lex3 along μ3
  have wf_measure : WellFounded (fun x y : Trace => Lex3 (μ3 x) (μ3 y)) :=
    InvImage.wf (f := μ3) wf_Lex3
  -- Show StepRev is a subrelation of the pulled-back order
  have hsub : Subrelation StepRev (fun x y : Trace => Lex3 (μ3 x) (μ3 y)) := by
    intro x y hxy
    exact hdec hxy
  exact Subrelation.wf hsub wf_measure

end MetaSN_KO7
-- Aggregated `measure_decreases` and `strong_normalization_triple` are deferred
-- until we resolve the general `merge_cancel` and `eq_refl` cases (κ duplicates).

/-! ## Restricted aggregator and SN for a safe subrelation ---------------- -/

namespace MetaSN_KO7

open MetaSN_DM

/-- A guarded subrelation of Step where known KO7 decreases apply without
conflicting δ/κ shapes. -/
inductive SafeStep : Trace → Trace → Prop
| R_int_delta (t) : SafeStep (integrate (delta t)) void
| R_merge_void_left (t) (hδ : deltaFlag t = 0) : SafeStep (merge void t) t
| R_merge_void_right (t) (hδ : deltaFlag t = 0) : SafeStep (merge t void) t
| R_merge_cancel (t) (hδ : deltaFlag t = 0) (h0 : kappaM t = 0) : SafeStep (merge t t) t
| R_rec_zero (b s) (hδ : deltaFlag b = 0) : SafeStep (recΔ b s void) b
| R_rec_succ (b s n) : SafeStep (recΔ b s (delta n)) (app s (recΔ b s n))
| R_eq_refl (a) (h0 : kappaM a = 0) : SafeStep (eqW a a) void
| R_eq_diff (a b) (hne : a ≠ b) : SafeStep (eqW a b) (integrate (merge a b))

/-- Each SafeStep strictly decreases the KO7 triple measure. -/
lemma measure_decreases_safe : ∀ {a b}, SafeStep a b → Lex3 (μ3 b) (μ3 a)
| _, _, SafeStep.R_int_delta t => by
    simpa using drop_R_int_delta t
| _, _, SafeStep.R_merge_void_left t hδ => by
    simpa using drop_R_merge_void_left_zero t hδ
| _, _, SafeStep.R_merge_void_right t hδ => by
    simpa using drop_R_merge_void_right_zero t hδ
| _, _, SafeStep.R_merge_cancel t hδ h0 => by
    simpa using drop_R_merge_cancel_zero t hδ h0
| _, _, SafeStep.R_rec_zero b s hδ => by
    simpa using drop_R_rec_zero b s hδ
| _, _, SafeStep.R_rec_succ b s n => by
    simpa using drop_R_rec_succ b s n
| _, _, SafeStep.R_eq_refl a h0 => by
    simpa using drop_R_eq_refl_zero a h0
| _, _, SafeStep.R_eq_diff a b _ => by
    simpa using drop_R_eq_diff a b

/-- Reverse of `SafeStep`. -/
def SafeStepRev : Trace → Trace → Prop := fun a b => SafeStep b a

/-- Generic wrapper: any relation that strictly decreases μ3 in Lex3 is well-founded in reverse. -/
theorem wellFounded_of_measure_decreases_R
  {R : Trace → Trace → Prop}
  (hdec : ∀ {a b : Trace}, R a b → Lex3 (μ3 b) (μ3 a)) :
  WellFounded (fun a b : Trace => R b a) := by
  -- Pull back the well-founded Lex3 along μ3
  have wf_measure : WellFounded (fun x y : Trace => Lex3 (μ3 x) (μ3 y)) :=
    InvImage.wf (f := μ3) wf_Lex3
  -- Show Rᵒᵖ ⊆ InvImage μ3 Lex3
  have hsub : Subrelation (fun a b => R b a) (fun x y : Trace => Lex3 (μ3 x) (μ3 y)) := by
    intro x y hxy
    exact hdec hxy
  exact Subrelation.wf hsub wf_measure

/-- Safe-step strong normalization: no infinite SafeStep reductions. -/
theorem wf_SafeStepRev : WellFounded SafeStepRev :=
  wellFounded_of_measure_decreases_R (R := SafeStep) (fun {_ _} h => measure_decreases_safe h)

end MetaSN_KO7

/-! ## Guarded lifting from Kernel.Step to SafeStep ----------------------- -/

namespace MetaSN_KO7

open OperatorKO7

open MetaSN_DM

/-- A guarded relation: carries explicit side-conditions per constructor. -/
inductive StepGuarded : Trace → Trace → Prop
| R_int_delta (t) : StepGuarded (integrate (delta t)) void
| R_merge_void_left (t) (hδ : deltaFlag t = 0) : StepGuarded (merge void t) t
| R_merge_void_right (t) (hδ : deltaFlag t = 0) : StepGuarded (merge t void) t
| R_merge_cancel (t) (hδ : deltaFlag t = 0) (h0 : MetaSN_DM.kappaM t = 0) : StepGuarded (merge t t) t
| R_rec_zero (b s) (hδ : deltaFlag b = 0) : StepGuarded (recΔ b s void) b
| R_rec_succ (b s n) : StepGuarded (recΔ b s (delta n)) (app s (recΔ b s n))
| R_eq_refl (a) (h0 : MetaSN_DM.kappaM a = 0) : StepGuarded (eqW a a) void
| R_eq_diff (a b) (hne : a ≠ b) : StepGuarded (eqW a b) (integrate (merge a b))

def StepGuardedRev : Trace → Trace → Prop := fun a b => StepGuarded b a

lemma measure_decreases_guarded : ∀ {a b}, StepGuarded a b → Lex3 (μ3 b) (μ3 a)
| _, _, StepGuarded.R_int_delta t => by simpa using drop_R_int_delta t
| _, _, StepGuarded.R_merge_void_left t hδ => by simpa using drop_R_merge_void_left_zero t hδ
| _, _, StepGuarded.R_merge_void_right t hδ => by simpa using drop_R_merge_void_right_zero t hδ
| _, _, StepGuarded.R_merge_cancel t hδ h0 => by simpa using drop_R_merge_cancel_zero t hδ h0
| _, _, StepGuarded.R_rec_zero b s hδ => by simpa using drop_R_rec_zero b s hδ
| _, _, StepGuarded.R_rec_succ b s n => by simpa using drop_R_rec_succ b s n
| _, _, StepGuarded.R_eq_refl a h0 => by simpa using drop_R_eq_refl_zero a h0
| _, _, StepGuarded.R_eq_diff a b _ => by simpa using drop_R_eq_diff a b

theorem wf_StepGuardedRev : WellFounded StepGuardedRev :=
  wellFounded_of_measure_decreases_R (R := StepGuarded) (fun {_ _} h => measure_decreases_guarded h)

end MetaSN_KO7

/-! ## Finite closure of guarded steps (star) ---------------------------- -/

namespace MetaSN_KO7

inductive StepGuardedStar : Trace → Trace → Prop
| refl : ∀ t, StepGuardedStar t t
| tail : ∀ {a b c}, StepGuarded a b → StepGuardedStar b c → StepGuardedStar a c

theorem stepguardedstar_of_step {a b : Trace} (h : StepGuarded a b) :
    StepGuardedStar a b := StepGuardedStar.tail h (StepGuardedStar.refl b)

theorem stepguardedstar_trans {a b c : Trace}
  (h₁ : StepGuardedStar a b) (h₂ : StepGuardedStar b c) : StepGuardedStar a c := by
  induction h₁ with
  | refl => exact h₂
  | tail hab _ ih => exact StepGuardedStar.tail hab (ih h₂)

-- Simple two-step composition helper.
lemma guarded_two_step {a b c : Trace}
  (h1 : StepGuarded a b) (h2 : StepGuarded b c) :
  StepGuardedStar a c :=
  StepGuardedStar.tail h1 (StepGuardedStar.tail h2 (StepGuardedStar.refl c))

end MetaSN_KO7

/-! ## MPO-style measure (μ-first then size) for non-rec rules ----------- -/

namespace MetaSN_MPO

open OperatorKO7 Trace

/-- A simple MPO-inspired size: sum of subtree sizes with positive node weights. -/
@[simp] def sizeMPO : Trace → Nat
| void          => 0
| delta t       => sizeMPO t + 1
| integrate t   => sizeMPO t + 1
| merge a b     => sizeMPO a + sizeMPO b + 1
| app a b       => sizeMPO a + sizeMPO b + 1
| recΔ b s n    => sizeMPO b + sizeMPO s + sizeMPO n + 2
| eqW a b       => sizeMPO a + sizeMPO b + 1

open MetaSN_KO7

/-- μ-first triple: (μ, sizeMPO, δ). -/
noncomputable def ν3m (t : Trace) : Ordinal × (Nat × Nat) :=
  (MetaSN.mu t, (sizeMPO t, deltaFlag t))

@[simp] def LexNu3m : (Ordinal × (Nat × Nat)) → (Ordinal × (Nat × Nat)) → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

lemma wf_LexNu3m : WellFounded LexNu3m := by
  refine WellFounded.prod_lex ?_ ?_
  · exact Ordinal.lt_wf
  · refine WellFounded.prod_lex ?_ ?_
    · exact Nat.lt_wfRel.wf
    · exact Nat.lt_wfRel.wf

/-- int∘delta: μ-right in the middle component. -/
lemma mpo_drop_R_int_delta (t : Trace) :
    LexNu3m (ν3m void) (ν3m (integrate (delta t))) := by
  classical
  dsimp [ν3m, LexNu3m]
  apply Prod.Lex.left
  simpa using MetaSN.mu_void_lt_integrate_delta t

/-- merge void-left: μ-right. -/
lemma mpo_drop_R_merge_void_left (t : Trace) :
    LexNu3m (ν3m t) (ν3m (merge void t)) := by
  classical
  dsimp [ν3m, LexNu3m]
  apply Prod.Lex.left
  simpa using MetaSN.mu_lt_merge_void_left t

/-- merge void-right: μ-right. -/
lemma mpo_drop_R_merge_void_right (t : Trace) :
    LexNu3m (ν3m t) (ν3m (merge t void)) := by
  classical
  dsimp [ν3m, LexNu3m]
  apply Prod.Lex.left
  simpa using MetaSN.mu_lt_merge_void_right t

/-- merge-cancel: μ-right (no κ or size tie needed). -/
lemma mpo_drop_R_merge_cancel (t : Trace) :
    LexNu3m (ν3m t) (ν3m (merge t t)) := by
  classical
  dsimp [ν3m, LexNu3m]
  apply Prod.Lex.left
  simpa using MetaSN.mu_lt_merge_cancel t

/-- eq_refl: μ-right (void μ < eqW μ). -/
lemma mpo_drop_R_eq_refl (a : Trace) :
    LexNu3m (ν3m void) (ν3m (eqW a a)) := by
  classical
  dsimp [ν3m, LexNu3m]
  apply Prod.Lex.left
  simpa using MetaSN.mu_void_lt_eq_refl a

/-- eq_diff: μ-right. -/
lemma mpo_drop_R_eq_diff (a b : Trace) :
    LexNu3m (ν3m (integrate (merge a b))) (ν3m (eqW a b)) := by
  classical
  dsimp [ν3m, LexNu3m]
  apply Prod.Lex.left
  simpa using MetaSN.mu_lt_eq_diff a b

/-- rec_zero: μ-first strict drop. -/
lemma mpo_drop_R_rec_zero (b s : Trace) :
    LexNu3m (ν3m b) (ν3m (recΔ b s void)) := by
  classical
  dsimp [ν3m, LexNu3m]
  -- We only need μ to drop
  apply Prod.Lex.left
  -- Show: mu b < mu (recΔ b s void) = ω^(μ s + 6) + ω*(μ b + 1) + 1
  -- First, μ b < ω*(μ b + 1)
  have h1 : MetaSN.mu b < omega0 * (MetaSN.mu b + 1) := by
    have hlt : MetaSN.mu b < MetaSN.mu b + 1 :=
      (Order.lt_add_one_iff (x := MetaSN.mu b) (y := MetaSN.mu b)).2 le_rfl
    have hmono : MetaSN.mu b + 1 ≤ omega0 * (MetaSN.mu b + 1) := by
      simpa using (Ordinal.le_mul_right (a := MetaSN.mu b + 1) (b := omega0) omega0_pos)
    exact lt_of_lt_of_le hlt hmono
  -- Then: ω*(μ b + 1) ≤ ω*(μ b + 1) + 1
  have h2 : omega0 * (MetaSN.mu b + 1) ≤ omega0 * (MetaSN.mu b + 1) + 1 :=
    le_add_of_nonneg_right (zero_le _)
  have h3 : MetaSN.mu b < omega0 * (MetaSN.mu b + 1) + 1 := lt_of_lt_of_le h1 h2
  -- Finally: add the leading ω^(μ s + 6) on the left (nonnegative), preserving ≤
  have h4 : omega0 * (MetaSN.mu b + 1) + 1 ≤
      (omega0 ^ (MetaSN.mu s + (6 : Ordinal))) + (omega0 * (MetaSN.mu b + 1) + 1) :=
    le_add_of_nonneg_left (zero_le _)
  have h5 : MetaSN.mu b < (omega0 ^ (MetaSN.mu s + (6 : Ordinal))) + (omega0 * (MetaSN.mu b + 1) + 1) :=
    lt_of_lt_of_le h3 h4
  simpa [MetaSN.mu, add_assoc, add_comm, add_left_comm]
    using h5
/- Safe subrelation for MPO (non-rec rules only; μ-first decreases) -/
inductive SafeStepMPO : Trace → Trace → Prop
| R_int_delta (t) : SafeStepMPO (integrate (delta t)) void
| R_merge_void_left (t) : SafeStepMPO (merge void t) t
| R_merge_void_right (t) : SafeStepMPO (merge t void) t
| R_merge_cancel (t) : SafeStepMPO (merge t t) t
| R_eq_refl (a) : SafeStepMPO (eqW a a) void
| R_eq_diff (a b) : SafeStepMPO (eqW a b) (integrate (merge a b))
| R_rec_zero (b s) : SafeStepMPO (recΔ b s void) b

def SafeStepMPORev : Trace → Trace → Prop := fun a b => SafeStepMPO b a

lemma mpo_measure_decreases : ∀ {a b}, SafeStepMPO a b → LexNu3m (ν3m b) (ν3m a)
| _, _, SafeStepMPO.R_int_delta t => by simpa using mpo_drop_R_int_delta t
| _, _, SafeStepMPO.R_merge_void_left t => by simpa using mpo_drop_R_merge_void_left t
| _, _, SafeStepMPO.R_merge_void_right t => by simpa using mpo_drop_R_merge_void_right t
| _, _, SafeStepMPO.R_merge_cancel t => by simpa using mpo_drop_R_merge_cancel t
| _, _, SafeStepMPO.R_eq_refl a => by simpa using mpo_drop_R_eq_refl a
| _, _, SafeStepMPO.R_eq_diff a b => by simpa using mpo_drop_R_eq_diff a b
| _, _, SafeStepMPO.R_rec_zero b s => by simpa using mpo_drop_R_rec_zero b s

theorem wf_SafeStepMPORev : WellFounded SafeStepMPORev := by
  -- pull back Lex3m via μ3m
  have wf_measure : WellFounded (fun x y : Trace => LexNu3m (ν3m x) (ν3m y)) :=
    InvImage.wf (f := ν3m) wf_LexNu3m
  have hsub : Subrelation SafeStepMPORev (fun x y : Trace => LexNu3m (ν3m x) (ν3m y)) := by
    intro x y hxy; exact mpo_measure_decreases hxy
  exact Subrelation.wf hsub wf_measure

end MetaSN_MPO

/-! ## Hybrid aggregator: per-rule decreases picking KO7 or MPO ---------- -/

namespace MetaSN_Hybrid

open OperatorKO7 Trace
open MetaSN_KO7 MetaSN_MPO

def HybridDec (a b : Trace) : Prop :=
  MetaSN_MPO.LexNu3m (MetaSN_MPO.ν3m b) (MetaSN_MPO.ν3m a) ∨
  MetaSN_KO7.Lex3 (MetaSN_KO7.μ3 b) (MetaSN_KO7.μ3 a)

lemma hybrid_R_int_delta (t : Trace) :
    HybridDec (integrate (delta t)) void :=
  Or.inr (by simpa using MetaSN_KO7.drop_R_int_delta t)

lemma hybrid_R_merge_void_left (t : Trace) :
    HybridDec (merge void t) t :=
  Or.inl (by simpa using MetaSN_MPO.mpo_drop_R_merge_void_left t)

lemma hybrid_R_merge_void_right (t : Trace) :
    HybridDec (merge t void) t :=
  Or.inl (by simpa using MetaSN_MPO.mpo_drop_R_merge_void_right t)

lemma hybrid_R_merge_cancel (t : Trace) :
    HybridDec (merge t t) t :=
  -- Prefer MPO μ-first drop for unguarded merge-cancel
  Or.inl (by simpa using MetaSN_MPO.mpo_drop_R_merge_cancel t)

lemma hybrid_R_rec_succ (b s n : Trace) :
    HybridDec (recΔ b s (delta n)) (app s (recΔ b s n)) :=
  Or.inr (by simpa using MetaSN_KO7.drop_R_rec_succ b s n)

lemma hybrid_R_eq_refl (a : Trace) :
    HybridDec (eqW a a) void :=
  -- Prefer KO7 Lex3 path now that eq_refl is unguarded
  Or.inr (by simpa using MetaSN_KO7.drop_R_eq_refl a)

lemma hybrid_R_eq_diff (a b : Trace) :
    HybridDec (eqW a b) (integrate (merge a b)) :=
  Or.inl (by simpa using MetaSN_MPO.mpo_drop_R_eq_diff a b)

-- Guarded rec_zero hybrid: δ-tie is required for KO7 κ-first
lemma hybrid_R_rec_zero_tie (b s : Trace) (hδ : MetaSN_KO7.deltaFlag b = 0) :
    HybridDec (recΔ b s void) b :=
  Or.inr (by simpa using MetaSN_KO7.drop_R_rec_zero b s hδ)

-- Unguarded rec_zero: use MPO μ-first drop, no δ-tie needed.
lemma hybrid_R_rec_zero (b s : Trace) :
    HybridDec (recΔ b s void) b :=
  Or.inl (by simpa using MetaSN_MPO.mpo_drop_R_rec_zero b s)

end MetaSN_Hybrid

-- (Hybrid WF aggregator deferred; keep per-rule HybridDec for now.)

/-! ### Bridging from Kernel.Step to HybridDec (with explicit rec_zero caveat) -/

namespace MetaSN_Hybrid

open OperatorKO7

/-- For any single kernel step, we produce a hybrid decrease certificate,
except in the rec_zero case where the δ-flag of `b` is 1. We surface that
as an explicit exception witness. -/
theorem hybrid_dec_of_Step {a b : Trace} (h : Step a b) :
    HybridDec a b ∨ ∃ (b' s : Trace), a = recΔ b' s void ∧ b = b' ∧ MetaSN_KO7.deltaFlag b' = 1 :=
  match h with
  | Step.R_int_delta t => Or.inl (hybrid_R_int_delta t)
  | Step.R_merge_void_left t => Or.inl (hybrid_R_merge_void_left t)
  | Step.R_merge_void_right t => Or.inl (hybrid_R_merge_void_right t)
  | Step.R_merge_cancel t => Or.inl (hybrid_R_merge_cancel t)
  | Step.R_rec_succ b s n => Or.inl (hybrid_R_rec_succ b s n)
  | Step.R_eq_refl a => Or.inl (hybrid_R_eq_refl a)
  | Step.R_eq_diff a b => Or.inl (hybrid_R_eq_diff a b)
  | Step.R_rec_zero b s => Or.inl (hybrid_R_rec_zero b s)

end MetaSN_Hybrid

/-! ## Public certificate: every Kernel.Step has a hybrid decrease -------- -/

namespace MetaSN_Hybrid

open OperatorKO7

/-- Every single kernel step has a strict hybrid decrease certificate. -/
lemma hybrid_drop_of_step {a b : Trace} (h : Step a b) : HybridDec a b :=
  match h with
  | Step.R_int_delta t => hybrid_R_int_delta t
  | Step.R_merge_void_left t => hybrid_R_merge_void_left t
  | Step.R_merge_void_right t => hybrid_R_merge_void_right t
  | Step.R_merge_cancel t => hybrid_R_merge_cancel t
  | Step.R_rec_succ b s n => hybrid_R_rec_succ b s n
  | Step.R_eq_refl a => hybrid_R_eq_refl a
  | Step.R_eq_diff a b => hybrid_R_eq_diff a b
  | Step.R_rec_zero b s => hybrid_R_rec_zero b s

/-! ## Examples
A tiny usage example showing that `hybrid_drop_of_step` yields a HybridDec certificate for a concrete kernel step. -/

section Examples

example (a : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec (OperatorKO7.Trace.eqW a a) OperatorKO7.Trace.void :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_eq_refl a)

-- eq-diff
example (a b : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec (OperatorKO7.Trace.eqW a b)
      (OperatorKO7.Trace.integrate (OperatorKO7.Trace.merge a b)) :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_eq_diff a b)

-- merge-void (left)
example (t : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec (OperatorKO7.Trace.merge OperatorKO7.Trace.void t) t :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_merge_void_left t)

-- merge-void (right)
example (t : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec (OperatorKO7.Trace.merge t OperatorKO7.Trace.void) t :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_merge_void_right t)

-- merge-cancel
example (t : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec (OperatorKO7.Trace.merge t t) t :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_merge_cancel t)

-- rec-zero
example (b s : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec (OperatorKO7.Trace.recΔ b s OperatorKO7.Trace.void) b :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_rec_zero b s)

-- Note: in this kernel, `delta` expects a `Trace`, so `n` is a `Trace`.
example (b s n : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec
  (OperatorKO7.Trace.recΔ b s (OperatorKO7.Trace.delta n))
  (OperatorKO7.Trace.app s (OperatorKO7.Trace.recΔ b s n)) :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_rec_succ b s n)

-- int∘delta
example (t : OperatorKO7.Trace) :
    MetaSN_Hybrid.HybridDec
  (OperatorKO7.Trace.integrate (OperatorKO7.Trace.delta t))
      OperatorKO7.Trace.void :=
  MetaSN_Hybrid.hybrid_drop_of_step (OperatorKO7.Step.R_int_delta t)

end Examples

/-! ### Public SN-style wrappers (safe subsets)
Expose well-foundedness of the reverse relations for the KO7-safe and MPO-safe subrelations. -/

/-- Public: no infinite reductions for the KO7-safe guarded subrelation. -/
theorem wf_StepRev_KO7_Safe : WellFounded MetaSN_KO7.SafeStepRev := MetaSN_KO7.wf_SafeStepRev

/-- Public: no infinite reductions for the MPO-safe subrelation. -/
theorem wf_StepRev_MPO_Safe : WellFounded MetaSN_MPO.SafeStepMPORev := MetaSN_MPO.wf_SafeStepMPORev

/-! ## Lex3 drop lemmas (KO7)
These mirror the slim versions from `Termination_Lex3.lean`, but live here to reduce files. -/

namespace MetaSN_KO7

open OperatorKO7 Trace

lemma lex3_drop_R_rec_zero_zero (b s : Trace)
    (hδ : MetaSN_KO7.deltaFlag b = 0) :
    MetaSN_KO7.Lex3 (MetaSN_KO7.μ3 b) (MetaSN_KO7.μ3 (recΔ b s void)) := by
  classical
  -- Only expose the Lex3 structure; keep μ3 opaque to control unfolding of deltaFlag.
  dsimp [MetaSN_KO7.Lex3]
  -- Replace μ3 with its pair form so we can rewrite outer flags directly.
  change Prod.Lex (fun x1 x2 => x1 < x2)
      (Prod.Lex (fun a b => a.IsDershowitzMannaLT b) (fun x1 x2 => x1 < x2))
      (MetaSN_KO7.deltaFlag b, (MetaSN_DM.kappaM b, MetaSN.mu b))
      (MetaSN_KO7.deltaFlag (recΔ b s void), (MetaSN_DM.kappaM (recΔ b s void), MetaSN.mu (recΔ b s void)))
  have hr0 : MetaSN_KO7.deltaFlag (recΔ b s void) = 0 := by
    simp [MetaSN_KO7.deltaFlag]
  -- Rewrite both outer components to 0.
  rw [hδ, hr0]
  apply Prod.Lex.right (a := 0)
  -- Inner LexDM drop via κᴹ strict decrease for rec_zero.
  apply Prod.Lex.left
  exact MetaSN_DM.dm_drop_R_rec_zero b s

lemma lex3_drop_R_merge_void_left_zero (t : Trace)
    (hδ : MetaSN_KO7.deltaFlag t = 0) :
    MetaSN_KO7.Lex3 (MetaSN_KO7.μ3 t) (MetaSN_KO7.μ3 (merge void t)) := by
  -- Delegate to the audited lemma with the same tie hypothesis
  simpa [MetaSN_KO7.μ3, MetaSN_KO7.Lex3] using
    MetaSN_KO7.drop_R_merge_void_left_zero t hδ

lemma lex3_drop_R_merge_void_right_zero (t : Trace)
    (hδ : MetaSN_KO7.deltaFlag t = 0) :
    MetaSN_KO7.Lex3 (MetaSN_KO7.μ3 t) (MetaSN_KO7.μ3 (merge t void)) := by
  simpa [MetaSN_KO7.μ3, MetaSN_KO7.Lex3] using
    MetaSN_KO7.drop_R_merge_void_right_zero t hδ

end MetaSN_KO7

end MetaSN_Hybrid
