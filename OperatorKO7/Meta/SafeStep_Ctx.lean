import OperatorKO7.Kernel
import OperatorKO7.Meta.Termination_KO7
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
