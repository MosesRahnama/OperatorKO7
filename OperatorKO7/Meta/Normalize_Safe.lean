import OperatorKO7.Kernel
import OperatorKO7.Meta.Termination_KO7
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

/-- Accessibility for `SafeStepRev` as a derived corollary of `wf_SafeStepRev`. -/
theorem acc_SafeStepRev (t : Trace) : Acc SafeStepRev t :=
  wf_SafeStepRev.apply t

/-- A well-founded pullback of the KO7 Lex3 order along μ3. -/
def Rμ3 (x y : Trace) : Prop := Lex3 (μ3 x) (μ3 y)

/-- Well-foundedness of `Rμ3`, inherited from `wf_Lex3` via `InvImage`. -/
lemma wf_Rμ3 : WellFounded Rμ3 :=
  InvImage.wf (f := μ3) wf_Lex3

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
          have hdrop : Rμ3 u t := measure_decreases_safe hu
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
  exact ⟨u, hs, measure_decreases_safe hs⟩

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
