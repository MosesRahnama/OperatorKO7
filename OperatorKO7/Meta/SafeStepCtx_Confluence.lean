import OperatorKO7.Meta.ContextClosed_SN
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

end MetaSN_KO7
