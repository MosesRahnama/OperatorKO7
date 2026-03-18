import OperatorKO7.Meta.ContextClosed_SN
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.SafeStep_Ctx

/-!
# Newman Layer for `SafeStepCtx`

This file factors the open `SafeStepCtx` confluence problem into the standard two
pieces:
- strong normalization, already proved in `ContextClosed_SN.lean`
- local joinability for the one-step contextual relation

We do not discharge the global local-join hypothesis here. The point is to make
the remaining proof obligation explicit and machine-check the exact Newman layer
it would feed into.
-/

open Classical
open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Local joinability at a fixed source for the one-step contextual safe relation. -/
def LocalJoinCtxAt (a : Trace) : Prop :=
  ∀ {b c}, SafeStepCtx a b → SafeStepCtx a c → ∃ d, SafeStepCtxStar b d ∧ SafeStepCtxStar c d

/-- Confluence for the reflexive-transitive closure of `SafeStepCtx`. -/
def ConfluentSafeCtx : Prop :=
  ∀ a b c, SafeStepCtxStar a b → SafeStepCtxStar a c → ∃ d, SafeStepCtxStar b d ∧ SafeStepCtxStar c d

/-- `SafeStepCtx`-normal forms. -/
def NormalFormSafeCtx (t : Trace) : Prop := ¬ ∃ u, SafeStepCtx t u

private theorem union_eq_zero_left {X Y : Multiset Nat} (h : X ∪ Y = 0) : X = 0 := by
  ext a
  have hc : max (X.count a) (Y.count a) = 0 := by
    simpa [Multiset.count_union] using congrArg (fun m => m.count a) h
  exact (Nat.max_eq_zero_iff.mp hc).1

private theorem union_eq_zero_right {X Y : Multiset Nat} (h : X ∪ Y = 0) : Y = 0 := by
  ext a
  have hc : max (X.count a) (Y.count a) = 0 := by
    simpa [Multiset.count_union] using congrArg (fun m => m.count a) h
  exact (Nat.max_eq_zero_iff.mp hc).2

private theorem ctx_nf_exists_of_acc :
    ∀ t : Trace, Acc SafeStepCtxRev t → ∃ n, SafeStepCtxStar t n ∧ NormalFormSafeCtx n := by
  intro t ht
  induction ht with
  | intro x hx ih =>
      by_cases hstep : ∃ y, SafeStepCtx x y
      · rcases hstep with ⟨y, hxy⟩
        rcases ih y hxy with ⟨n, hyn, hnf⟩
        exact ⟨n, SafeStepCtxStar.tail hxy hyn, hnf⟩
      · exact ⟨x, SafeStepCtxStar.refl x, hstep⟩

/-- Every term admits a `SafeStepCtx` normal form. -/
theorem ctx_nf_exists (t : Trace) : ∃ n, SafeStepCtxStar t n ∧ NormalFormSafeCtx n :=
  ctx_nf_exists_of_acc t (acc_ctx_all t)

/-- Any `SafeStepCtx`-normal form has `deltaFlag = 0`. -/
theorem ctx_nf_deltaFlag_zero {t : Trace} (hnf : NormalFormSafeCtx t) : deltaFlag t = 0 := by
  cases t with
  | void => simp [deltaFlag]
  | delta u => simp [deltaFlag]
  | integrate u => simp [deltaFlag]
  | merge a b => simp [deltaFlag]
  | app a b => simp [deltaFlag]
  | eqW a b => simp [deltaFlag]
  | recΔ b s n =>
      cases n with
      | void => simp [deltaFlag]
      | delta n =>
          exfalso
          apply hnf
          refine ⟨app s (recΔ b s n), SafeStepCtx.root (SafeStep.R_rec_succ b s n)⟩
      | integrate u => simp [deltaFlag]
      | merge a b => simp [deltaFlag]
      | app a b => simp [deltaFlag]
      | recΔ b s n => simp [deltaFlag]
      | eqW a b => simp [deltaFlag]

/-- A contextual safe step preserves the zero-`kappaM` property. -/
theorem ctx_step_preserves_kappa_zero {a b : Trace}
    (h : SafeStepCtx a b) (hk : MetaSN_DM.kappaM a = 0) :
    MetaSN_DM.kappaM b = 0 := by
  induction h with
  | root hs =>
      cases hs with
      | R_int_delta t =>
          simp [MetaSN_DM.kappaM] at hk ⊢
      | R_merge_void_left t hδ =>
          simp at hk ⊢; exact hk
      | R_merge_void_right t hδ =>
          simp at hk ⊢; exact hk
      | R_merge_cancel t hδ h0 =>
          exact h0
      | R_rec_zero b s hδ =>
          simp [MetaSN_DM.kappaM] at hk
      | R_rec_succ b s n =>
          simp [MetaSN_DM.kappaM] at hk
      | R_eq_refl a h0 =>
          simp [MetaSN_DM.kappaM]
      | R_eq_diff a b hne =>
          simp at hk ⊢; exact hk
  | integrate h ih =>
      simp [MetaSN_DM.kappaM] at hk ⊢; exact ih hk
  | mergeL h ih =>
      have ha : MetaSN_DM.kappaM _ = 0 := union_eq_zero_left (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      have ha' := ih ha
      have hb : MetaSN_DM.kappaM _ = 0 := union_eq_zero_right (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      simp [MetaSN_DM.kappaM, ha', hb]
  | mergeR h ih =>
      have ha : MetaSN_DM.kappaM _ = 0 := union_eq_zero_left (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      have hb : MetaSN_DM.kappaM _ = 0 := union_eq_zero_right (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      have hb' := ih hb
      simp [MetaSN_DM.kappaM, ha, hb']
  | appL h ih =>
      have ha : MetaSN_DM.kappaM _ = 0 := union_eq_zero_left (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      have ha' := ih ha
      have hb : MetaSN_DM.kappaM _ = 0 := union_eq_zero_right (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      simp [MetaSN_DM.kappaM, ha', hb]
  | appR h ih =>
      have ha : MetaSN_DM.kappaM _ = 0 := union_eq_zero_left (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      have hb : MetaSN_DM.kappaM _ = 0 := union_eq_zero_right (by simp [MetaSN_DM.kappaM] at hk; exact hk)
      have hb' := ih hb
      simp [MetaSN_DM.kappaM, ha, hb']
  | recB h _ =>
      simp [MetaSN_DM.kappaM] at hk
  | recS h _ =>
      simp [MetaSN_DM.kappaM] at hk
  | recN h _ =>
      simp [MetaSN_DM.kappaM] at hk

/-- Zero-`kappaM` is preserved along contextual multi-step reduction. -/
theorem ctxstar_preserves_kappa_zero {a b : Trace}
    (h : SafeStepCtxStar a b) (hk : MetaSN_DM.kappaM a = 0) :
    MetaSN_DM.kappaM b = 0 := by
  induction h with
  | refl t =>
      exact hk
  | tail hab hbc ih =>
      exact ih (ctx_step_preserves_kappa_zero hab hk)

private theorem ctx_shadow_merge_void_left (t : Trace) :
    ∃ d, SafeStepCtxStar t d ∧ SafeStepCtxStar (merge void t) d := by
  rcases ctx_nf_exists t with ⟨n, htn, hnf⟩
  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
  refine ⟨n, htn, ?_⟩
  exact ctxstar_trans (ctxstar_mergeR htn)
    (ctxstar_of_root (SafeStep.R_merge_void_left n hδn))

private theorem ctx_shadow_merge_void_right (t : Trace) :
    ∃ d, SafeStepCtxStar t d ∧ SafeStepCtxStar (merge t void) d := by
  rcases ctx_nf_exists t with ⟨n, htn, hnf⟩
  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
  refine ⟨n, htn, ?_⟩
  exact ctxstar_trans (ctxstar_mergeL htn)
    (ctxstar_of_root (SafeStep.R_merge_void_right n hδn))

private theorem ctx_shadow_merge_diag_of_kappa_zero (t : Trace)
    (hk : MetaSN_DM.kappaM t = 0) :
    ∃ d, SafeStepCtxStar t d ∧ SafeStepCtxStar (merge t t) d := by
  rcases ctx_nf_exists t with ⟨n, htn, hnf⟩
  have hk_n : MetaSN_DM.kappaM n = 0 := ctxstar_preserves_kappa_zero htn hk
  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
  refine ⟨n, htn, ?_⟩
  exact ctxstar_trans (ctxstar_mergeLR htn htn)
    (ctxstar_of_root (SafeStep.R_merge_cancel n hδn hk_n))

private theorem ctx_shadow_rec_zero (b s : Trace) :
    ∃ d, SafeStepCtxStar b d ∧ SafeStepCtxStar (recΔ b s void) d := by
  rcases ctx_nf_exists b with ⟨n, hbn, hnf⟩
  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
  refine ⟨n, hbn, ?_⟩
  exact ctxstar_trans (ctxstar_recB hbn)
    (ctxstar_of_root (SafeStep.R_rec_zero n s hδn))

private theorem ctxstar_destruct {a c : Trace} (h : SafeStepCtxStar a c) :
    a = c ∨ ∃ b, SafeStepCtx a b ∧ SafeStepCtxStar b c := by
  cases h with
  | refl t => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

private theorem join_ctxstar_at
    (locAll : ∀ a, LocalJoinCtxAt a) :
    ∀ x, Acc SafeStepCtxRev x →
      ∀ {y z : Trace}, SafeStepCtxStar x y → SafeStepCtxStar x z →
        ∃ d, SafeStepCtxStar y d ∧ SafeStepCtxStar z d := by
  intro x hx
  induction hx with
  | intro x _ ih =>
      intro y z hxy hxz
      have HY := ctxstar_destruct hxy
      have HZ := ctxstar_destruct hxz
      cases HY with
      | inl hEq =>
          cases hEq
          exact ⟨z, hxz, SafeStepCtxStar.refl z⟩
      | inr hy =>
          rcases hy with ⟨b1, hxb1, hb1y⟩
          cases HZ with
          | inl hEq2 =>
              cases hEq2
              exact ⟨y, SafeStepCtxStar.refl y, SafeStepCtxStar.tail hxb1 hb1y⟩
          | inr hz =>
              rcases hz with ⟨c1, hxc1, hc1z⟩
              rcases locAll x hxb1 hxc1 with ⟨e, hb1e, hc1e⟩
              rcases ih c1 hxc1 hc1e hc1z with ⟨d₁, hed₁, hzd₁⟩
              have hb1d₁ : SafeStepCtxStar b1 d₁ := ctxstar_trans hb1e hed₁
              rcases ih b1 hxb1 hb1y hb1d₁ with ⟨d, hyd, hd₁d⟩
              exact ⟨d, hyd, ctxstar_trans hzd₁ hd₁d⟩

/-- Global local-joinability for the contextual safe fragment. -/
theorem localJoinAll_safeCtx : ∀ a, LocalJoinCtxAt a := by
  intro a
  induction a with
  | void =>
      intro b c hb hc
      cases hb with
      | root hs => cases hs
  | delta t =>
      intro b c hb hc
      cases hb with
      | root hs => cases hs
  | integrate t iht =>
      intro b c hb hc
      cases hb with
      | root hs1 =>
          cases hc with
          | root hs2 =>
              exact (localJoin_ctx_of_localJoin (integrate t) (localJoin_all_safe (integrate t))) hs1 hs2
          | integrate h2 =>
              cases hs1 with
              | R_int_delta t' => cases h2 with | root hs => cases hs
      | integrate h1 =>
          cases hc with
          | root hs2 =>
              cases hs2 with
              | R_int_delta t' => cases h1 with | root hs => cases hs
          | integrate h2 =>
              rcases iht h1 h2 with ⟨d, h1d, h2d⟩
              exact ⟨integrate d, ctxstar_integrate h1d, ctxstar_integrate h2d⟩
  | merge x y ihx ihy =>
      intro b c hb hc
      cases hb with
      | root hs1 =>
          cases hc with
          | root hs2 =>
              exact (localJoin_ctx_of_localJoin (merge x y) (localJoin_all_safe (merge x y))) hs1 hs2
          | mergeL h2 =>
              cases hs1 with
              | R_merge_void_left t hδ =>
                  cases h2 with
                  | root hs => cases hs
              | R_merge_void_right t hδ =>
                  rcases ctx_shadow_merge_void_right _ with ⟨d, htd, hmd⟩
                  exact ⟨d, SafeStepCtxStar.tail h2 htd, hmd⟩
              | R_merge_cancel _ hδ h0 =>
                  rcases ctx_nf_exists _ with ⟨n, ht'n, hnf⟩
                  have hk_t' : MetaSN_DM.kappaM _ = 0 := ctx_step_preserves_kappa_zero h2 h0
                  have hk_n : MetaSN_DM.kappaM n = 0 := ctxstar_preserves_kappa_zero ht'n hk_t'
                  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
                  have hroot_n := SafeStepCtxStar.tail h2 ht'n
                  refine ⟨n, hroot_n, ?_⟩
                  exact ctxstar_trans
                    (ctxstar_trans (ctxstar_mergeL ht'n) (ctxstar_mergeR hroot_n))
                    (ctxstar_of_root (SafeStep.R_merge_cancel n hδn hk_n))
          | mergeR h2 =>
              cases hs1 with
              | R_merge_void_left t hδ =>
                  rcases ctx_shadow_merge_void_left _ with ⟨d, htd, hmd⟩
                  exact ⟨d, SafeStepCtxStar.tail h2 htd, hmd⟩
              | R_merge_void_right t hδ =>
                  cases h2 with
                  | root hs => cases hs
              | R_merge_cancel _ hδ h0 =>
                  rcases ctx_nf_exists _ with ⟨n, ht'n, hnf⟩
                  have hk_t' : MetaSN_DM.kappaM _ = 0 := ctx_step_preserves_kappa_zero h2 h0
                  have hk_n : MetaSN_DM.kappaM n = 0 := ctxstar_preserves_kappa_zero ht'n hk_t'
                  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
                  have hroot_n := SafeStepCtxStar.tail h2 ht'n
                  refine ⟨n, hroot_n, ?_⟩
                  exact ctxstar_trans
                    (ctxstar_trans (ctxstar_mergeR ht'n) (ctxstar_mergeL hroot_n))
                    (ctxstar_of_root (SafeStep.R_merge_cancel n hδn hk_n))
      | mergeL h1 =>
          cases hc with
          | root hs2 =>
              cases hs2 with
              | R_merge_void_left t hδ =>
                  cases h1 with
                  | root hs => cases hs
              | R_merge_void_right t hδ =>
                  rcases ctx_shadow_merge_void_right _ with ⟨d, htd, hmd⟩
                  exact ⟨d, hmd, SafeStepCtxStar.tail h1 htd⟩
              | R_merge_cancel _ hδ h0 =>
                  rcases ctx_nf_exists _ with ⟨n, ht'n, hnf⟩
                  have hk_t' : MetaSN_DM.kappaM _ = 0 := ctx_step_preserves_kappa_zero h1 h0
                  have hk_n : MetaSN_DM.kappaM n = 0 := ctxstar_preserves_kappa_zero ht'n hk_t'
                  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
                  have hroot_n := SafeStepCtxStar.tail h1 ht'n
                  refine ⟨n, ?_, hroot_n⟩
                  exact ctxstar_trans
                    (ctxstar_trans (ctxstar_mergeL ht'n) (ctxstar_mergeR hroot_n))
                    (ctxstar_of_root (SafeStep.R_merge_cancel n hδn hk_n))
          | mergeL h2 =>
              rcases ihx h1 h2 with ⟨d, h1d, h2d⟩
              exact ⟨merge d y, ctxstar_mergeL h1d, ctxstar_mergeL h2d⟩
          | mergeR h2 =>
              exact ⟨merge _ _, SafeStepCtxStar.tail (SafeStepCtx.mergeR h2) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.mergeL h1) (SafeStepCtxStar.refl _)⟩
      | mergeR h1 =>
          cases hc with
          | root hs2 =>
              cases hs2 with
              | R_merge_void_left t hδ =>
                  rcases ctx_shadow_merge_void_left _ with ⟨d, htd, hmd⟩
                  exact ⟨d, hmd, SafeStepCtxStar.tail h1 htd⟩
              | R_merge_void_right t hδ =>
                  cases h1 with
                  | root hs => cases hs
              | R_merge_cancel _ hδ h0 =>
                  rcases ctx_nf_exists _ with ⟨n, ht'n, hnf⟩
                  have hk_t' : MetaSN_DM.kappaM _ = 0 := ctx_step_preserves_kappa_zero h1 h0
                  have hk_n : MetaSN_DM.kappaM n = 0 := ctxstar_preserves_kappa_zero ht'n hk_t'
                  have hδn : deltaFlag n = 0 := ctx_nf_deltaFlag_zero hnf
                  have hroot_n := SafeStepCtxStar.tail h1 ht'n
                  refine ⟨n, ?_, hroot_n⟩
                  exact ctxstar_trans
                    (ctxstar_trans (ctxstar_mergeR ht'n) (ctxstar_mergeL hroot_n))
                    (ctxstar_of_root (SafeStep.R_merge_cancel n hδn hk_n))
          | mergeL h2 =>
              exact ⟨merge _ _, SafeStepCtxStar.tail (SafeStepCtx.mergeL h2) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.mergeR h1) (SafeStepCtxStar.refl _)⟩
          | mergeR h2 =>
              rcases ihy h1 h2 with ⟨d, h1d, h2d⟩
              exact ⟨merge x d, ctxstar_mergeR h1d, ctxstar_mergeR h2d⟩
  | app x y ihx ihy =>
      intro b c hb hc
      cases hb with
      | root hs =>
          cases hs
      | appL h1 =>
          cases hc with
          | root hs =>
              cases hs
          | appL h2 =>
              rcases ihx h1 h2 with ⟨d, h1d, h2d⟩
              exact ⟨app d y, ctxstar_appL h1d, ctxstar_appL h2d⟩
          | appR h2 =>
              exact ⟨app _ _, SafeStepCtxStar.tail (SafeStepCtx.appR h2) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.appL h1) (SafeStepCtxStar.refl _)⟩
      | appR h1 =>
          cases hc with
          | root hs =>
              cases hs
          | appL h2 =>
              exact ⟨app _ _, SafeStepCtxStar.tail (SafeStepCtx.appL h2) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.appR h1) (SafeStepCtxStar.refl _)⟩
          | appR h2 =>
              rcases ihy h1 h2 with ⟨d, h1d, h2d⟩
              exact ⟨app x d, ctxstar_appR h1d, ctxstar_appR h2d⟩
  | recΔ b s n ihb ihs ihn =>
      intro u v hu hv
      cases hu with
      | root hs1 =>
          cases hv with
          | root hs2 =>
              exact (localJoin_ctx_of_localJoin (recΔ b s n) (localJoin_all_safe (recΔ b s n))) hs1 hs2
          | recB hb =>
              cases hs1 with
              | R_rec_zero b s hδ =>
                  rcases ctx_nf_exists _ with ⟨d, hbd, hnf⟩
                  have hδd : deltaFlag d = 0 := ctx_nf_deltaFlag_zero hnf
                  exact ⟨d, SafeStepCtxStar.tail hb hbd,
                    ctxstar_trans (ctxstar_recB hbd)
                      (ctxstar_of_root (SafeStep.R_rec_zero d s hδd))⟩
              | R_rec_succ b s n =>
                  exact ⟨app s (recΔ _ s n),
                    SafeStepCtxStar.tail (SafeStepCtx.appR (SafeStepCtx.recB hb)) (SafeStepCtxStar.refl _),
                    ctxstar_of_root (SafeStep.R_rec_succ _ s n)⟩
          | recS hs' =>
              cases hs1 with
              | R_rec_zero b s hδ =>
                  exact ⟨b, SafeStepCtxStar.refl _,
                    ctxstar_of_root (SafeStep.R_rec_zero b _ hδ)⟩
              | R_rec_succ b s n =>
                  exact ⟨_,
                    ctxstar_trans
                      (SafeStepCtxStar.tail (SafeStepCtx.appL hs') (SafeStepCtxStar.refl _))
                      (SafeStepCtxStar.tail (SafeStepCtx.appR (SafeStepCtx.recS hs')) (SafeStepCtxStar.refl _)),
                    ctxstar_of_root (SafeStep.R_rec_succ _ _ _)⟩
          | recN hn =>
              cases hs1 with
              | R_rec_zero b s hδ =>
                  cases hn with
                  | root hs => cases hs
              | R_rec_succ b s n =>
                  cases hn with
                  | root hs => cases hs
      | recB hb =>
          cases hv with
          | root hs2 =>
              cases hs2 with
              | R_rec_zero b s hδ =>
                  rcases ctx_nf_exists _ with ⟨d, hbd, hnf⟩
                  have hδd : deltaFlag d = 0 := ctx_nf_deltaFlag_zero hnf
                  exact ⟨d,
                    ctxstar_trans (ctxstar_recB hbd)
                      (ctxstar_of_root (SafeStep.R_rec_zero d s hδd)),
                    SafeStepCtxStar.tail hb hbd⟩
              | R_rec_succ b s n =>
                  exact ⟨app s (recΔ _ s n),
                    ctxstar_of_root (SafeStep.R_rec_succ _ s n),
                    SafeStepCtxStar.tail (SafeStepCtx.appR (SafeStepCtx.recB hb)) (SafeStepCtxStar.refl _)⟩
          | recB hb' =>
              rcases ihb hb hb' with ⟨d, h₁, h₂⟩
              exact ⟨recΔ d s n, ctxstar_recB h₁, ctxstar_recB h₂⟩
          | recS hs' =>
              exact ⟨recΔ _ _ n,
                SafeStepCtxStar.tail (SafeStepCtx.recS hs') (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.recB hb) (SafeStepCtxStar.refl _)⟩
          | recN hn =>
              exact ⟨recΔ _ s _, SafeStepCtxStar.tail (SafeStepCtx.recN hn) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.recB hb) (SafeStepCtxStar.refl _)⟩
      | recS hs' =>
          cases hv with
          | root hs2 =>
              cases hs2 with
              | R_rec_zero b s hδ =>
                  exact ⟨b, ctxstar_of_root (SafeStep.R_rec_zero b _ hδ), SafeStepCtxStar.refl _⟩
              | R_rec_succ b s n =>
                  exact ⟨_,
                    ctxstar_of_root (SafeStep.R_rec_succ _ _ _),
                    ctxstar_trans
                      (SafeStepCtxStar.tail (SafeStepCtx.appL hs') (SafeStepCtxStar.refl _))
                      (SafeStepCtxStar.tail (SafeStepCtx.appR (SafeStepCtx.recS hs')) (SafeStepCtxStar.refl _))⟩
          | recB hb =>
              exact ⟨recΔ _ _ n,
                SafeStepCtxStar.tail (SafeStepCtx.recB hb) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.recS hs') (SafeStepCtxStar.refl _)⟩
          | recS hs'' =>
              rcases ihs hs' hs'' with ⟨d, h₁, h₂⟩
              exact ⟨recΔ b d n, ctxstar_recS h₁, ctxstar_recS h₂⟩
          | recN hn =>
              exact ⟨recΔ b _ _, SafeStepCtxStar.tail (SafeStepCtx.recN hn) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.recS hs') (SafeStepCtxStar.refl _)⟩
      | recN hn =>
          cases hv with
          | root hs2 =>
              cases hs2 with
              | R_rec_zero b s hδ =>
                  cases hn with
                  | root hs => cases hs
              | R_rec_succ b s n =>
                  cases hn with
                  | root hs => cases hs
          | recB hb =>
              exact ⟨recΔ _ s _, SafeStepCtxStar.tail (SafeStepCtx.recB hb) (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.recN hn) (SafeStepCtxStar.refl _)⟩
          | recS hs' =>
              exact ⟨recΔ b _ _, SafeStepCtxStar.tail (SafeStepCtx.recS hs') (SafeStepCtxStar.refl _),
                SafeStepCtxStar.tail (SafeStepCtx.recN hn) (SafeStepCtxStar.refl _)⟩
          | recN hn' =>
              rcases ihn hn hn' with ⟨d, h₁, h₂⟩
              exact ⟨recΔ b s d, ctxstar_recN h₁, ctxstar_recN h₂⟩
  | eqW x y =>
      intro b c hb hc
      cases hb with
      | root hs1 =>
          cases hc with
          | root hs2 =>
              exact (localJoin_ctx_of_localJoin (eqW x y) (localJoin_all_safe (eqW x y))) hs1 hs2

/-- The contextual safe fragment is locally joinable everywhere. -/
theorem localJoinAll_ctx : ∀ a, LocalJoinCtxAt a :=
  localJoinAll_safeCtx

/-- Newman's lemma specialized to `SafeStepCtx`. -/
theorem newman_safeCtx (locAll : ∀ a, LocalJoinCtxAt a) : ConfluentSafeCtx := by
  intro a b c hab hac
  exact join_ctxstar_at locAll a (acc_ctx_all a) hab hac

/-- Global confluence from local join everywhere for `SafeStepCtx`. -/
theorem confluentSafeCtx_of_localJoinAt
    (locAll : ∀ a, LocalJoinCtxAt a) : ConfluentSafeCtx :=
  newman_safeCtx locAll

/-- Confluence implies local joinability for the one-step contextual relation. -/
theorem localJoinCtx_of_confluent
    (hconf : ConfluentSafeCtx) : ∀ a, LocalJoinCtxAt a := by
  intro a b c hb hc
  exact hconf a b c
    (SafeStepCtxStar.tail hb (SafeStepCtxStar.refl _))
    (SafeStepCtxStar.tail hc (SafeStepCtxStar.refl _))

/-- Exact obstruction theorem for `SafeStepCtx`:
because strong normalization is already available, confluence is equivalent to
the remaining global local-join obligation. -/
theorem confluentSafeCtx_iff_localJoinAll :
    ConfluentSafeCtx ↔ ∀ a, LocalJoinCtxAt a := by
  constructor
  · exact localJoinCtx_of_confluent
  · exact confluentSafeCtx_of_localJoinAt

/-- Unconditional confluence of the partial context closure `SafeStepCtx`. -/
theorem confluentSafeCtx : ConfluentSafeCtx :=
  newman_safeCtx localJoinAll_ctx

end MetaSN_KO7
