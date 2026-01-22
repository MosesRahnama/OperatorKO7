import OperatorKO7.Kernel
import OperatorKO7.Meta.Termination_KO7
import OperatorKO7.Meta.Normalize_Safe

/-!
Newman's lemma for the KO7 safe fragment.

Purpose:
- Packages the standard argument: termination (well-foundedness) + local joinability implies
  confluence (Church-Rosser) for the reflexive-transitive closure.

Scope boundary:
- This file is parameterized by a local-join hypothesis `locAll : ∀ a, LocalJoinAt a`.
- Termination for `SafeStep` is supplied by `wf_SafeStepRev` (from `Meta/Termination_KO7.lean`).
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

end MetaSN_KO7
