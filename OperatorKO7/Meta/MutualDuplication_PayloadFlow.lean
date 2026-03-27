import Mathlib
import OperatorKO7.Meta.DependencyPairs_Fragment

/-!
# Abstract Payload-Flow Barrier

This module isolates the common proof pattern behind the synchronized preserving SCC
results. The syntax-specific packet model is abstracted to:

- an abstract latent packet constructor `packet n p`,
- a visible wrapper constructor `wrap`,
- a recursor-like carrier `recur`,
- and a certified one-cycle path from `syncSource` to `syncTarget`.

The resulting theorems are still concrete enough to recover additive and affine SCC
barriers, but no longer depend on the explicit packet syntax used by the current
finite-cycle implementations.
-/

namespace OperatorKO7.MutualDuplicationPayloadFlow

open OperatorKO7.DependencyPairsFragment

/-- Generic left-nested wrapper iteration. -/
def wrapNest {T : Type} (wrap : T → T → T) (p : T) : Nat → T → T
  | 0, t => t
  | n + 1, t => wrapNest wrap p n (wrap p t)

/-- Minimal syntax interface for a synchronized payload-flow cycle. -/
structure PacketModel (T : Type) where
  empty : T
  wrap : T → T → T
  recur : T → T → T
  packet : Nat → T → T

/-- Source state carrying a latent synchronized packet of `copies` payloads. -/
def syncSource {T : Type} (M : PacketModel T) (copies : Nat) (ctx payload : T) : T :=
  M.recur ctx (M.packet copies payload)

/-- Target state after one full synchronized exposure cycle. -/
def syncTarget {T : Type} (M : PacketModel T) (copies : Nat) (ctx payload : T) : T :=
  wrapNest M.wrap payload copies (M.recur ctx M.empty)

/-- One-cycle witness for the induced minimal contextual relation. -/
structure CycleWitness {T : Type} (M : PacketModel T) (copies : Nat) where
  StepCtx : T → T → Prop
  cycle_realized :
    ∀ ctx payload,
      Relation.TransGen StepCtx
        (syncSource M copies ctx payload)
        (syncTarget M copies ctx payload)

/-- Orientation of the induced contextual relation. -/
def GlobalOrientsCtx {T : Type} {M : PacketModel T} {copies : Nat}
    (W : CycleWitness M copies) (m : T → Nat) : Prop :=
  ∀ {a b : T}, W.StepCtx a b → m b < m a

/-- Additive direct measures for the abstract payload-flow interface. -/
structure AdditiveMeasure {T : Type} (M : PacketModel T) where
  eval : T → Nat
  w_empty : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_empty : eval M.empty = w_empty
  eval_wrap : ∀ x y, eval (M.wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ ctx packet, eval (M.recur ctx packet) = w_recur + eval ctx + eval packet
  eval_packet : ∀ n p, eval (M.packet n p) = n * eval p + w_empty
  h_wrap_pos : 1 ≤ w_wrap

lemma eval_wrapNest {T : Type} {M : PacketModel T} (A : AdditiveMeasure M) (p : T) :
    ∀ n t, A.eval (wrapNest M.wrap p n t) = n * A.w_wrap + n * A.eval p + A.eval t
  | 0, t => by simp [wrapNest]
  | n + 1, t => by
      rw [wrapNest, eval_wrapNest A p n (M.wrap p t), A.eval_wrap]
      ring

theorem syncTarget_eval_gt {T : Type} {M : PacketModel T}
    (A : AdditiveMeasure M) {copies : Nat} (hcopies : 1 ≤ copies) (ctx payload : T) :
    A.eval (syncSource M copies ctx payload) < A.eval (syncTarget M copies ctx payload) := by
  have hsrc :
      A.eval (syncSource M copies ctx payload) =
        A.w_recur + A.eval ctx + (copies * A.eval payload + A.w_empty) := by
    simp [syncSource, A.eval_recur, A.eval_packet]
  have htgt :
      A.eval (syncTarget M copies ctx payload) =
        copies * A.w_wrap + copies * A.eval payload +
          (A.w_recur + A.eval ctx + A.w_empty) := by
    simp [syncTarget, eval_wrapNest, A.eval_recur, A.eval_empty]
  rw [hsrc, htgt]
  have hwrap : 1 ≤ copies * A.w_wrap := by
    exact Nat.mul_le_mul hcopies A.h_wrap_pos
  omega

theorem no_global_orients_ctx_additive {T : Type} {M : PacketModel T} {copies : Nat}
    (W : CycleWitness M copies) (A : AdditiveMeasure M) (hcopies : 1 ≤ copies) :
    ¬ GlobalOrientsCtx W A.eval := by
  intro h
  have horient : DependencyPairsFragment.GlobalOrients W.StepCtx A.eval (· < ·) := by
    intro a b hstep
    exact h hstep
  have hpath :
      Relation.TransGen W.StepCtx
        (syncSource M copies M.empty M.empty)
        (syncTarget M copies M.empty M.empty) := by
    exact W.cycle_realized M.empty M.empty
  have hcomp :
      A.eval (syncTarget M copies M.empty M.empty) <
        A.eval (syncSource M copies M.empty M.empty) := by
    exact DependencyPairsFragment.transGen_drop (R := W.StepCtx) (m := A.eval) horient hpath
  have hgt :
      A.eval (syncSource M copies M.empty M.empty) <
        A.eval (syncTarget M copies M.empty M.empty) := by
    exact syncTarget_eval_gt A hcopies M.empty M.empty
  exact Nat.lt_asymm hcomp hgt

/-- Affine constructor-local measures on the abstract payload-flow interface. -/
structure AffineMeasure {T : Type} (M : PacketModel T) where
  eval : T → Nat
  c_empty : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_ctx : Nat
  recur_packet : Nat
  eval_empty : eval M.empty = c_empty
  eval_wrap :
    ∀ x y, eval (M.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ ctx packet,
      eval (M.recur ctx packet) = recur_const + recur_ctx * eval ctx + recur_packet * eval packet
  eval_packet : ∀ n p, eval (M.packet n p) = n * eval p + c_empty
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

def AffineMeasure.wrapRightIter {T : Type} {M : PacketModel T}
    (A : AffineMeasure M) : Nat → Nat
  | 0 => 1
  | n + 1 => A.wrapRightIter n * A.wrap_right

def AffineMeasure.wrapConstIter {T : Type} {M : PacketModel T}
    (A : AffineMeasure M) : Nat → Nat
  | 0 => 0
  | n + 1 => A.wrapConstIter n + A.wrapRightIter n * A.wrap_const

def AffineMeasure.wrapLeftIter {T : Type} {M : PacketModel T}
    (A : AffineMeasure M) : Nat → Nat
  | 0 => 0
  | n + 1 => A.wrapLeftIter n + A.wrapRightIter n * A.wrap_left

lemma eval_wrapNest_affine {T : Type} {M : PacketModel T} (A : AffineMeasure M) (p : T) :
    ∀ n t,
      A.eval (wrapNest M.wrap p n t) =
        A.wrapConstIter n + A.wrapLeftIter n * A.eval p + A.wrapRightIter n * A.eval t
  | 0, t => by
      simp [wrapNest, AffineMeasure.wrapConstIter, AffineMeasure.wrapLeftIter,
        AffineMeasure.wrapRightIter]
  | n + 1, t => by
      rw [wrapNest, eval_wrapNest_affine A p n (M.wrap p t), A.eval_wrap]
      simp [AffineMeasure.wrapConstIter, AffineMeasure.wrapLeftIter, AffineMeasure.wrapRightIter,
        Nat.mul_add, Nat.add_mul]
      ring

lemma wrapRightIter_pos {T : Type} {M : PacketModel T} (A : AffineMeasure M) :
    ∀ n, 1 ≤ A.wrapRightIter n
  | 0 => by simp [AffineMeasure.wrapRightIter]
  | n + 1 => by
      simp [AffineMeasure.wrapRightIter]
      exact Nat.mul_le_mul (wrapRightIter_pos A n) A.h_wrap_right_pos

lemma wrapLeftIter_pos {T : Type} {M : PacketModel T} (A : AffineMeasure M) :
    ∀ n, 0 < n → 1 ≤ A.wrapLeftIter n
  | 0, h => by cases Nat.not_lt_zero _ h
  | n + 1, _ => by
      have hterm : 1 ≤ A.wrapRightIter n * A.wrap_left := by
        exact Nat.mul_le_mul (wrapRightIter_pos A n) A.h_wrap_left_pos
      have hsum : 1 ≤ A.wrapLeftIter n + A.wrapRightIter n * A.wrap_left := by
        exact le_trans hterm (Nat.le_add_left _ _)
      simpa [AffineMeasure.wrapLeftIter] using hsum

def WrapperDominance {T : Type} {M : PacketModel T}
    (A : AffineMeasure M) (copies : Nat) : Prop :=
  copies * A.recur_packet < A.wrapLeftIter copies

theorem syncTarget_affine_eval_gt_of_wrapper_dominance
    {T : Type} {M : PacketModel T} {copies : Nat}
    (A : AffineMeasure M) (hdom : WrapperDominance A copies)
    (hunbounded : ∀ q : Nat, ∃ t : T, q ≤ A.eval t) (ctx : T) :
    ∃ payload,
      A.eval (syncSource M copies ctx payload) < A.eval (syncTarget M copies ctx payload) := by
  obtain ⟨payload, hpayload⟩ := hunbounded 1
  refine ⟨payload, ?_⟩
  have hsrc :
      A.eval (syncSource M copies ctx payload) =
        A.recur_const + A.recur_ctx * A.eval ctx +
          A.recur_packet * (copies * A.eval payload + A.c_empty) := by
    simp [syncSource, A.eval_recur, A.eval_packet]
  have htgt :
      A.eval (syncTarget M copies ctx payload) =
        A.wrapConstIter copies + A.wrapLeftIter copies * A.eval payload +
          A.wrapRightIter copies *
            (A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty) := by
    simp [syncTarget, eval_wrapNest_affine, A.eval_recur, A.eval_empty]
  rw [hsrc, htgt]
  unfold WrapperDominance at hdom
  have hcoeff : copies * A.recur_packet + 1 ≤ A.wrapLeftIter copies := by
    omega
  have hmul :
      (copies * A.recur_packet + 1) * A.eval payload ≤
        A.wrapLeftIter copies * A.eval payload := by
    exact Nat.mul_le_mul_right (A.eval payload) hcoeff
  have hpayloadPos : 1 ≤ A.eval payload := hpayload
  have hsrc_lt :
      A.recur_packet * (copies * A.eval payload + A.c_empty) <
        (copies * A.recur_packet + 1) * A.eval payload + A.recur_packet * A.c_empty := by
    have : (copies * A.recur_packet + 1) * A.eval payload + A.recur_packet * A.c_empty =
        A.recur_packet * (copies * A.eval payload + A.c_empty) + A.eval payload := by
      ring
    rw [this]
    exact Nat.lt_add_of_pos_right hpayloadPos
  have hconst :
      A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty ≤
        A.wrapConstIter copies + A.wrapRightIter copies *
          (A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty) := by
    have hpow : 1 ≤ A.wrapRightIter copies := wrapRightIter_pos A copies
    have hmul' :
        A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty ≤
          A.wrapRightIter copies *
            (A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty) := by
      calc
        A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty
            = 1 * (A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty) := by ring
        _ ≤ A.wrapRightIter copies *
              (A.recur_const + A.recur_ctx * A.eval ctx + A.recur_packet * A.c_empty) := by
              exact Nat.mul_le_mul_right _ hpow
    exact le_trans hmul' (Nat.le_add_left _ _)
  omega

theorem no_global_orients_ctx_affine_of_wrapper_dominance
    {T : Type} {M : PacketModel T} {copies : Nat}
    (W : CycleWitness M copies) (A : AffineMeasure M)
    (hdom : WrapperDominance A copies)
    (hunbounded : ∀ q : Nat, ∃ t : T, q ≤ A.eval t) :
    ¬ GlobalOrientsCtx W A.eval := by
  intro h
  obtain ⟨payload, hgt⟩ :=
    syncTarget_affine_eval_gt_of_wrapper_dominance A hdom hunbounded M.empty
  have horient : DependencyPairsFragment.GlobalOrients W.StepCtx A.eval (· < ·) := by
    intro a b hstep
    exact h hstep
  have hpath :
      Relation.TransGen W.StepCtx
        (syncSource M copies M.empty payload)
        (syncTarget M copies M.empty payload) := by
    exact W.cycle_realized M.empty payload
  have hcomp :
      A.eval (syncTarget M copies M.empty payload) <
        A.eval (syncSource M copies M.empty payload) := by
    exact DependencyPairsFragment.transGen_drop (R := W.StepCtx) (m := A.eval) horient hpath
  exact Nat.lt_asymm hcomp hgt

/-- Transparent packet-bookkeeping measures on the abstract payload-flow interface. -/
structure TransparentMeasure {T : Type} (M : PacketModel T) where
  eval : T → Nat
  c_empty : Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat
  eval_empty : eval M.empty = c_empty
  eval_wrap : ∀ x y, eval (M.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ ctx packet, eval (M.recur ctx packet) = c_recur (eval ctx) (eval packet)
  eval_packet : ∀ n p, eval (M.packet n p) = c_empty
  wrap_subterm2 : ∀ x y, c_wrap x y > y

lemma eval_wrapNest_gt {T : Type} {M : PacketModel T} (A : TransparentMeasure M) (p : T) :
    ∀ n t, 0 < n → A.eval t < A.eval (wrapNest M.wrap p n t)
  | 0, t, h => by
      cases Nat.not_lt_zero _ h
  | 1, t, _ => by
      simpa [wrapNest, A.eval_wrap] using A.wrap_subterm2 (A.eval p) (A.eval t)
  | n + 2, t, _ => by
      have hbase : A.eval t < A.eval (M.wrap p t) := by
        rw [A.eval_wrap]
        exact A.wrap_subterm2 (A.eval p) (A.eval t)
      have htail :
          A.eval (M.wrap p t) < A.eval (wrapNest M.wrap p (n + 1) (M.wrap p t)) := by
        exact eval_wrapNest_gt A p (n + 1) (M.wrap p t) (Nat.succ_pos _)
      rw [wrapNest]
      exact Nat.lt_trans hbase htail

theorem syncTarget_eval_gt_transparent
    {T : Type} {M : PacketModel T} {copies : Nat}
    (A : TransparentMeasure M) (hcopies : 0 < copies) (ctx payload : T) :
    A.eval (syncSource M copies ctx payload) < A.eval (syncTarget M copies ctx payload) := by
  rw [syncTarget, syncSource, A.eval_recur, A.eval_packet]
  have hwrap :
      A.eval (M.recur ctx M.empty) < A.eval (wrapNest M.wrap payload copies (M.recur ctx M.empty)) := by
    exact eval_wrapNest_gt A payload copies (M.recur ctx M.empty) hcopies
  simpa [A.eval_recur, A.eval_empty] using hwrap

theorem no_global_orients_ctx_transparent
    {T : Type} {M : PacketModel T} {copies : Nat}
    (W : CycleWitness M copies) (A : TransparentMeasure M) (hcopies : 0 < copies) :
    ¬ GlobalOrientsCtx W A.eval := by
  intro h
  have horient : DependencyPairsFragment.GlobalOrients W.StepCtx A.eval (· < ·) := by
    intro a b hstep
    exact h hstep
  have hpath :
      Relation.TransGen W.StepCtx
        (syncSource M copies M.empty M.empty)
        (syncTarget M copies M.empty M.empty) := by
    exact W.cycle_realized M.empty M.empty
  have hcomp :
      A.eval (syncTarget M copies M.empty M.empty) <
        A.eval (syncSource M copies M.empty M.empty) := by
    exact DependencyPairsFragment.transGen_drop (R := W.StepCtx) (m := A.eval) horient hpath
  have hgt :
      A.eval (syncSource M copies M.empty M.empty) <
        A.eval (syncTarget M copies M.empty M.empty) := by
    exact syncTarget_eval_gt_transparent A hcopies M.empty M.empty
  exact Nat.lt_asymm hcomp hgt

theorem no_global_orients_ctx_of_scalar_projection_transparent
    {T α : Type} {M : PacketModel T} {copies : Nat}
    (W : CycleWitness M copies)
    (μ : T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A : TransparentMeasure M)
    (hπ : ∀ t : T, π (μ t) = A.eval t)
    (hcopies : 0 < copies) :
    ¬ DependencyPairsFragment.GlobalOrients W.StepCtx μ R := by
  intro h
  have hscalar : GlobalOrientsCtx W A.eval := by
    intro a b hstep
    have hlt : π (μ b) < π (μ a) := hproj (h hstep)
    simpa [hπ a, hπ b] using hlt
  exact no_global_orients_ctx_transparent W A hcopies hscalar

end OperatorKO7.MutualDuplicationPayloadFlow
