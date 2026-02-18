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
