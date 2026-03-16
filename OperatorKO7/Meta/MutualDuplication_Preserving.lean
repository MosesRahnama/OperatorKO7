import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.DependencyPairs_Fragment

/-!
# Multiplicity-Preserving SCC Synchronization

This module isolates a genuinely different SCC mechanism from the existing bounded
composite-duplication theorem. Here each individual root rule preserves an explicit
payload-counting interface exactly. The obstruction appears only after synchronizing the
two latent payload channels and following one full SCC cycle, which exposes two visible
wrapper-carried copies of the same payload.

The current result is additive only. It is intentionally stated as a synchronized-exposure
theorem rather than as an affine extension of the older coefficient-growth argument.
-/

namespace OperatorKO7.MutualDuplicationPreserving

open OperatorKO7.DependencyPairsFragment

/-- Syntax for a small two-node SCC with two latent payload channels. -/
inductive SyncTerm : Type
| base : SyncTerm
| payload : SyncTerm
| left : SyncTerm → SyncTerm
| right : SyncTerm → SyncTerm
| wrap : SyncTerm → SyncTerm → SyncTerm
| recurA : SyncTerm → SyncTerm → SyncTerm → SyncTerm
| recurB : SyncTerm → SyncTerm → SyncTerm
deriving DecidableEq, Repr

open SyncTerm

/-- Count the tracked payload multiplicity.

This is the explicit counting interface used in the theorem: the latent left/right tags
preserve the underlying payload count, while the passive context parameter is ignored. -/
@[simp] def payloadCount : SyncTerm → Nat
  | base => 0
  | payload => 1
  | left t => payloadCount t
  | right t => payloadCount t
  | wrap x y => payloadCount x + payloadCount y
  | recurA _ p q => payloadCount p + payloadCount q
  | recurB _ q => payloadCount q

/-- Count payload that has become visible as a wrapper-left argument. -/
@[simp] def visiblePayloadCount : SyncTerm → Nat
  | wrap x y => payloadCount x + visiblePayloadCount y
  | _ => 0

/-- Synchronized source family: both latent channels carry the same payload. -/
def syncSource (ctx payloadTerm : SyncTerm) : SyncTerm :=
  recurA ctx (left payloadTerm) (right payloadTerm)

/-- Composite target after one full SCC cycle on synchronized inputs. -/
def syncTarget (ctx payloadTerm : SyncTerm) : SyncTerm :=
  wrap payloadTerm (wrap payloadTerm (recurA ctx base base))

/-- Root rules of the preserving SCC. Each rule preserves `payloadCount` exactly. -/
inductive Step : SyncTerm → SyncTerm → Prop
| R_A : ∀ ctx p q, Step (recurA ctx (left p) (right q)) (wrap p (recurB ctx (right q)))
| R_B : ∀ ctx q, Step (recurB ctx (right q)) (wrap q (recurA ctx base base))

/-- Minimal context closure needed to realize one full SCC cycle. -/
inductive StepCtx : SyncTerm → SyncTerm → Prop
| root : ∀ {a b}, Step a b → StepCtx a b
| wrap_right : ∀ s {a b}, StepCtx a b → StepCtx (wrap s a) (wrap s b)

/-- Orientation of the induced SCC context relation. -/
def GlobalOrientsCtx (m : SyncTerm → Nat) : Prop :=
  ∀ {a b : SyncTerm}, StepCtx a b → m b < m a

/-- Every individual SCC rule preserves the tracked payload multiplicity exactly. -/
theorem step_preserves_payloadCount :
    ∀ {a b : SyncTerm}, Step a b → payloadCount a = payloadCount b := by
  intro a b h
  cases h <;> simp [payloadCount]

/-- The minimal context closure also preserves payload multiplicity. -/
theorem stepCtx_preserves_payloadCount :
    ∀ {a b : SyncTerm}, StepCtx a b → payloadCount a = payloadCount b := by
  intro a b h
  induction h with
  | root hstep =>
      exact step_preserves_payloadCount hstep
  | wrap_right s h ih =>
      simp [ih, payloadCount]

/-- One full SCC cycle on synchronized inputs. -/
theorem synchronized_cycle_realized (ctx payloadTerm : SyncTerm) :
    ∃ u,
      StepCtx (syncSource ctx payloadTerm) u ∧
      StepCtx u (syncTarget ctx payloadTerm) := by
  refine ⟨wrap payloadTerm (recurB ctx (right payloadTerm)), ?_, ?_⟩
  · exact StepCtx.root (Step.R_A ctx payloadTerm payloadTerm)
  · exact StepCtx.wrap_right payloadTerm (StepCtx.root (Step.R_B ctx payloadTerm))

/-- Synchronized sources have no visible wrapper-carried payload before the cycle. -/
@[simp] theorem visible_syncSource (ctx payloadTerm : SyncTerm) :
    visiblePayloadCount (syncSource ctx payloadTerm) = 0 := by
  simp [syncSource]

/-- After one full cycle, both synchronized payload channels have become visible. -/
theorem visible_syncTarget (ctx payloadTerm : SyncTerm) :
    visiblePayloadCount (syncTarget ctx payloadTerm) = 2 * payloadCount payloadTerm := by
  simp [syncTarget, two_mul]

/-- On synchronized nonempty payloads, one SCC cycle strictly increases visible payload. -/
theorem synchronized_cycle_exposes_payload (ctx payloadTerm : SyncTerm)
    (hpayload : 0 < payloadCount payloadTerm) :
    visiblePayloadCount (syncSource ctx payloadTerm) <
      visiblePayloadCount (syncTarget ctx payloadTerm) := by
  rw [visible_syncSource, visible_syncTarget]
  have htwo : 0 < 2 * payloadCount payloadTerm := by
    have htwo' : 0 < 2 := by decide
    exact Nat.mul_pos htwo' hpayload
  simpa using htwo

/-- Additive direct measures on the preserving SCC syntax.

The latent channel tags are evaluation-transparent: they are bookkeeping devices for the
payload-count interface, not new weight-bearing constructors. -/
structure AdditiveMeasure where
  eval : SyncTerm → Nat
  w_base : Nat
  w_payload : Nat
  w_wrap : Nat
  w_recurA : Nat
  w_recurB : Nat
  eval_base : eval base = w_base
  eval_payload : eval payload = w_payload
  eval_left : ∀ t, eval (left t) = eval t
  eval_right : ∀ t, eval (right t) = eval t
  eval_wrap : ∀ x y, eval (wrap x y) = w_wrap + eval x + eval y
  eval_recurA :
    ∀ ctx p q, eval (recurA ctx p q) = w_recurA + eval ctx + eval p + eval q
  eval_recurB :
    ∀ ctx q, eval (recurB ctx q) = w_recurB + eval ctx + eval q
  h_wrap_pos : 1 ≤ w_wrap

/-- The synchronized composite target is always strictly larger than the synchronized
source for additive direct measures on this preserving SCC syntax. -/
theorem syncTarget_eval_gt (M : AdditiveMeasure) (ctx payloadTerm : SyncTerm) :
    M.eval (syncSource ctx payloadTerm) < M.eval (syncTarget ctx payloadTerm) := by
  have hsrc :
      M.eval (syncSource ctx payloadTerm) =
        M.w_recurA + M.eval ctx + M.eval payloadTerm + M.eval payloadTerm := by
    simp [syncSource, M.eval_recurA, M.eval_left, M.eval_right]
  have htgt :
      M.eval (syncTarget ctx payloadTerm) =
        M.w_wrap + M.eval payloadTerm +
          (M.w_wrap + M.eval payloadTerm + (M.w_recurA + M.eval ctx + M.w_base + M.w_base)) := by
    simp [syncTarget, M.eval_wrap, M.eval_recurA, M.eval_base]
  rw [hsrc, htgt]
  have hwrap := M.h_wrap_pos
  omega

/-- No additive direct measure can orient the synchronized composite uniformly. -/
theorem no_additive_orients_synchronized_cycle (M : AdditiveMeasure) :
    ¬ (∀ (ctx payloadTerm : SyncTerm),
      M.eval (syncTarget ctx payloadTerm) < M.eval (syncSource ctx payloadTerm)) := by
  intro h
  have hspec := h base payload
  have hgt := syncTarget_eval_gt M base payload
  exact Nat.lt_asymm hspec hgt

/-- Consequently no additive direct measure globally orients the induced minimal context
relation generated by the preserving SCC. -/
theorem no_global_orients_ctx_additive (M : AdditiveMeasure) :
    ¬ GlobalOrientsCtx M.eval := by
  intro h
  rcases synchronized_cycle_realized base payload with ⟨u, h₁, h₂⟩
  have horient : DependencyPairsFragment.GlobalOrients StepCtx M.eval (· < ·) := by
    intro a b hstep
    exact h hstep
  have hpath :
      Relation.TransGen StepCtx (syncSource base payload) (syncTarget base payload) :=
    Relation.TransGen.tail (Relation.TransGen.single h₁) h₂
  have hcomp : M.eval (syncTarget base payload) < M.eval (syncSource base payload) := by
    exact
      DependencyPairsFragment.transGen_drop
        (R := StepCtx) (m := M.eval) horient hpath
  have hgt : M.eval (syncSource base payload) < M.eval (syncTarget base payload) := by
    exact syncTarget_eval_gt M base payload
  exact Nat.lt_asymm hcomp hgt

/-! ## Affine barrier for the preserving SCC

The affine extension reveals a genuine structural difference from both the additive preserving
case and the affine bounded-composite case (in `MutualDuplication_General.lean`).

**Key finding:** The affine barrier holds for the preserving SCC when the wrapper's
payload coefficient exceeds the recursor's, i.e., `wrap_left * (1 + wrap_right) > recurA_p + recurA_q`.
When this condition fails, affine measures with large recursor coefficients CAN orient the
synchronized cycle. This precisely delineates the affine boundary for SCC-synchronized
duplication: the barrier is conditional on wrapper-dominance over the recursor payload coefficients.

The additive case avoids this issue because all coefficients are 1, so the wrapper's
contribution (two extra `w_wrap` constants) always dominates. -/

/-- Affine constructor-local measures on the preserving SCC syntax.

The latent channel tags remain evaluation-transparent. The wrapper and recursor
constructors now carry scaling coefficients. -/
structure AffineMeasure where
  eval : SyncTerm → Nat
  c_base : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recurA_const : Nat
  recurA_ctx : Nat
  recurA_p : Nat
  recurA_q : Nat
  recurB_const : Nat
  recurB_ctx : Nat
  recurB_q : Nat
  eval_base : eval base = c_base
  eval_left : ∀ t, eval (left t) = eval t
  eval_right : ∀ t, eval (right t) = eval t
  eval_wrap : ∀ x y, eval (wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recurA :
    ∀ ctx p q, eval (recurA ctx p q) = recurA_const + recurA_ctx * eval ctx + recurA_p * eval p + recurA_q * eval q
  eval_recurB :
    ∀ ctx q, eval (recurB ctx q) = recurB_const + recurB_ctx * eval ctx + recurB_q * eval q
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Source evaluation at `(base, p)` under an affine measure. -/
theorem syncSource_affine_eval (M : AffineMeasure) (p : SyncTerm) :
    M.eval (syncSource base p) =
      M.recurA_const + M.recurA_ctx * M.c_base +
        (M.recurA_p + M.recurA_q) * M.eval p := by
  simp [syncSource, M.eval_recurA, M.eval_left, M.eval_right, M.eval_base,
    Nat.add_mul, Nat.add_assoc]

/-- Target evaluation at `(base, p)` under an affine measure. -/
theorem syncTarget_affine_eval (M : AffineMeasure) (p : SyncTerm) :
    M.eval (syncTarget base p) =
      M.wrap_const + M.wrap_left * M.eval p +
        M.wrap_right * (M.wrap_const + M.wrap_left * M.eval p +
          M.wrap_right * (M.recurA_const + M.recurA_ctx * M.c_base +
            (M.recurA_p + M.recurA_q) * M.c_base)) := by
  simp [syncTarget, M.eval_wrap, M.eval_recurA, M.eval_base,
    Nat.add_mul, Nat.add_assoc]

/-- The wrapper-dominance condition: the target's coefficient of `eval(p)` exceeds the source's.

In the target, `eval(p)` appears with coefficient `wrap_left + wrap_right * wrap_left`
(once from the outer `wrap`, once from the inner `wrap`).
In the source, it appears with coefficient `recurA_p + recurA_q`.

When this condition holds, pumping `eval(p)` forces the target to exceed the source. -/
def WrapperDominance (M : AffineMeasure) : Prop :=
  M.recurA_p + M.recurA_q < M.wrap_left + M.wrap_right * M.wrap_left

/-- Under wrapper dominance and an unbounded pump, no affine measure can orient
the synchronized composite. -/
theorem no_affine_orients_synchronized_cycle_of_wrapper_dominance
    (M : AffineMeasure)
    (hdom : WrapperDominance M)
    (hunbounded : ∀ k : Nat, ∃ t : SyncTerm, M.eval t ≥ k) :
    ¬ (∀ (ctx payloadTerm : SyncTerm),
      M.eval (syncTarget ctx payloadTerm) < M.eval (syncSource ctx payloadTerm)) := by
  intro h
  obtain ⟨p, hp⟩ := hunbounded (M.recurA_const + M.recurA_ctx * M.c_base + 1)
  have hspec := h base p
  simp only [syncSource, syncTarget, M.eval_wrap, M.eval_recurA,
    M.eval_left, M.eval_right, M.eval_base] at hspec
  unfold WrapperDominance at hdom
  have h_inner : M.wrap_left * M.eval p ≤
      M.wrap_const + M.wrap_left * M.eval p +
        M.wrap_right * (M.recurA_const + M.recurA_ctx * M.c_base +
          M.recurA_p * M.c_base + M.recurA_q * M.c_base) := by omega
  have h_scaled := Nat.mul_le_mul_left M.wrap_right h_inner
  have h_tgt_lb : M.wrap_const + M.wrap_left * M.eval p +
      M.wrap_right * (M.wrap_const + M.wrap_left * M.eval p +
        M.wrap_right * (M.recurA_const + M.recurA_ctx * M.c_base +
          M.recurA_p * M.c_base + M.recurA_q * M.c_base)) ≥
      M.wrap_left * M.eval p + M.wrap_right * M.wrap_left * M.eval p := by
    rw [← Nat.mul_assoc] at h_scaled; omega
  have h_coeff : (M.recurA_p + M.recurA_q + 1) * M.eval p ≤
      M.wrap_left * M.eval p + M.wrap_right * M.wrap_left * M.eval p := by
    have hfactor : (M.wrap_left + M.wrap_right * M.wrap_left) * M.eval p =
        M.wrap_left * M.eval p + M.wrap_right * M.wrap_left * M.eval p := by ring
    rw [← hfactor]
    exact Nat.mul_le_mul_right (M.eval p) hdom
  have h_src_lt : M.recurA_const + M.recurA_ctx * M.c_base +
      M.recurA_p * M.eval p + M.recurA_q * M.eval p <
      (M.recurA_p + M.recurA_q + 1) * M.eval p := by
    have : (M.recurA_p + M.recurA_q + 1) * M.eval p =
        M.recurA_p * M.eval p + M.recurA_q * M.eval p + M.eval p := by ring
    omega
  omega

end OperatorKO7.MutualDuplicationPreserving
