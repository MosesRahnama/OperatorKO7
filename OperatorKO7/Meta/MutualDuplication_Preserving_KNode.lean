import Mathlib
import OperatorKO7.Meta.DependencyPairs_Fragment

/-!
# Finite k-Node Multiplicity-Preserving Synchronized SCCs

This module generalizes the preserving synchronized SCC barrier from the two-node
worked construction to a finite cyclic `k + 1`-node family.

The mechanism is intentionally explicit. A recursor at node `i` carries a packet of
latent payload channels tagged by the cycle index. One root step exposes the current
payload under a visible wrapper and forwards the remaining latent packet to node
`i + 1`. Payload multiplicity is preserved exactly at every step.

The file proves the additive branch and a conditional affine extension under a
generalized wrapper-dominance hypothesis.
-/

namespace OperatorKO7.MutualDuplicationPreservingKNode

open OperatorKO7.DependencyPairsFragment

/-- Syntax for a finite cyclic preserving SCC with explicit latent packets. -/
inductive SyncTerm (k : Nat) : Type
| base : SyncTerm k
| payload : SyncTerm k
| empty : SyncTerm k
| slot : Fin (k + 1) → SyncTerm k → SyncTerm k
| cons : SyncTerm k → SyncTerm k → SyncTerm k
| wrap : SyncTerm k → SyncTerm k → SyncTerm k
| recur : Fin (k + 1) → SyncTerm k → SyncTerm k → SyncTerm k
deriving DecidableEq, Repr

namespace SyncTerm

variable {k : Nat}

open SyncTerm

/-- Advance the cycle index modulo `k + 1`. -/
def advance (i : Fin (k + 1)) (n : Nat) : Fin (k + 1) where
  val := (i.1 + n) % (k + 1)
  isLt := Nat.mod_lt _ (Nat.succ_pos _)

lemma advance_zero (i : Fin (k + 1)) : advance i 0 = i := by
  ext
  simp [advance]

lemma advance_add (i : Fin (k + 1)) (m n : Nat) :
    advance (advance i m) n = advance i (m + n) := by
  ext
  simp [advance, Nat.add_assoc, Nat.mod_add_mod]

lemma advance_cycleLen (i : Fin (k + 1)) : advance i (k + 1) = i := by
  ext
  simp [advance]

/-- Repeatedly wrap the same payload on the left. -/
def wrapNest (p : SyncTerm k) : Nat → SyncTerm k → SyncTerm k
  | 0, t => t
  | n + 1, t => wrapNest p n (wrap p t)

/-- Synchronized latent packet of length `n`, starting at node `i`. -/
def syncPacket (i : Fin (k + 1)) : Nat → SyncTerm k → SyncTerm k
  | 0, _ => empty
  | n + 1, p => cons (slot i p) (syncPacket (advance i 1) n p)

/-- Synchronized source for one full cycle starting at node `i`. -/
def syncSource (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k) : SyncTerm k :=
  recur i ctx (syncPacket i (k + 1) payloadTerm)

/-- Composite target after one full synchronized cycle. -/
def syncTarget (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k) : SyncTerm k :=
  wrapNest payloadTerm (k + 1) (recur i ctx empty)

/-- Count the tracked payload multiplicity. -/
@[simp] def payloadCount : SyncTerm k → Nat
  | base => 0
  | payload => 1
  | empty => 0
  | slot _ t => payloadCount t
  | cons x xs => payloadCount x + payloadCount xs
  | wrap x y => payloadCount x + payloadCount y
  | recur _ _ packet => payloadCount packet

/-- Count payload that has become visible as a wrapper-left argument. -/
@[simp] def visiblePayloadCount : SyncTerm k → Nat
  | wrap x y => payloadCount x + visiblePayloadCount y
  | _ => 0

lemma payloadCount_syncPacket (i : Fin (k + 1)) :
    ∀ n, ∀ p : SyncTerm k, payloadCount (syncPacket i n p) = n * payloadCount p
  | 0, p => by simp [syncPacket]
  | n + 1, p => by
      simp [syncPacket, payloadCount_syncPacket (advance i 1) n p]
      ring

lemma visible_syncSource (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k) :
    visiblePayloadCount (syncSource i ctx payloadTerm) = 0 := by
  simp [syncSource]

lemma visible_wrapNest (p : SyncTerm k) :
    ∀ n t, visiblePayloadCount (wrapNest p n t) = n * payloadCount p + visiblePayloadCount t
  | 0, t => by simp [wrapNest]
  | n + 1, t => by
      simp [wrapNest, visible_wrapNest p n (wrap p t)]
      ring

lemma visible_syncTarget (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k) :
    visiblePayloadCount (syncTarget i ctx payloadTerm) = (k + 1) * payloadCount payloadTerm := by
  simp [syncTarget, visible_wrapNest]

theorem synchronized_cycle_exposes_payload (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k)
    (hpayload : 0 < payloadCount payloadTerm) :
    visiblePayloadCount (syncSource i ctx payloadTerm) <
      visiblePayloadCount (syncTarget i ctx payloadTerm) := by
  rw [visible_syncSource, visible_syncTarget]
  have hnodes : 0 < k + 1 := Nat.succ_pos _
  exact Nat.mul_pos hnodes hpayload

/-- Root rules of the preserving SCC. One step exposes the current latent channel and
forwards the remaining synchronized packet to the next node. -/
inductive Step : SyncTerm k → SyncTerm k → Prop
| expose :
    ∀ (i : Fin (k + 1)) ctx p rest,
      Step (recur i ctx (cons (slot i p) rest)) (wrap p (recur (advance i 1) ctx rest))

/-- Minimal context closure needed to realize one full SCC cycle. -/
inductive StepCtx : SyncTerm k → SyncTerm k → Prop
| root : ∀ {a b}, Step a b → StepCtx a b
| wrap_right : ∀ s {a b}, StepCtx a b → StepCtx (wrap s a) (wrap s b)

/-- Orientation of the induced SCC context relation. -/
def GlobalOrientsCtx (m : SyncTerm k → Nat) : Prop :=
  ∀ {a b : SyncTerm k}, StepCtx a b → m b < m a

theorem step_preserves_payloadCount :
    ∀ {a b : SyncTerm k}, Step a b → payloadCount a = payloadCount b := by
  intro a b h
  cases h
  simp [payloadCount]

theorem stepCtx_preserves_payloadCount :
    ∀ {a b : SyncTerm k}, StepCtx a b → payloadCount a = payloadCount b := by
  intro a b h
  induction h with
  | root hstep =>
      exact step_preserves_payloadCount hstep
  | wrap_right s h ih =>
      simp [ih]

lemma StepCtx.wrapNest_right (p : SyncTerm k) :
    ∀ n {a b : SyncTerm k}, StepCtx a b → StepCtx (wrapNest p n a) (wrapNest p n b)
  | 0, a, b, h => h
  | n + 1, a, b, h => by
      simpa [wrapNest] using
        StepCtx.wrapNest_right p n (StepCtx.wrap_right p h)

/-- Residual phase after `r` synchronized exposures. -/
def phase (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k) (r : Nat) : SyncTerm k :=
  wrapNest payloadTerm r
    (recur (advance i r) ctx (syncPacket (advance i r) ((k + 1) - r) payloadTerm))

lemma phase_step (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k) {r : Nat}
    (hr : r < k + 1) :
    StepCtx (phase i ctx payloadTerm r) (phase i ctx payloadTerm (r + 1)) := by
  have hroot :
      StepCtx
        (recur (advance i r) ctx
          (cons (slot (advance i r) payloadTerm)
            (syncPacket (advance (advance i r) 1) (((k + 1) - r) - 1) payloadTerm)))
        (wrap payloadTerm
          (recur (advance (advance i r) 1) ctx
            (syncPacket (advance (advance i r) 1) (((k + 1) - r) - 1) payloadTerm))) := by
    exact StepCtx.root (Step.expose (advance i r) ctx payloadTerm
      (syncPacket (advance (advance i r) 1) (((k + 1) - r) - 1) payloadTerm))
  have hlift := StepCtx.wrapNest_right payloadTerm r hroot
  have hcount : (k + 1) - r = Nat.succ (((k + 1) - r) - 1) := by
    omega
  have hnext : advance (advance i r) 1 = advance i (r + 1) := by
    simpa [Nat.add_assoc] using advance_add i r 1
  have htail : ((k + 1) - r) - 1 = (k + 1) - (r + 1) := by
    omega
  change
    StepCtx
      (wrapNest payloadTerm r
        (recur (advance i r) ctx
          (syncPacket (advance i r) ((k + 1) - r) payloadTerm)))
      (phase i ctx payloadTerm (r + 1))
  rw [hcount, syncPacket]
  simpa [phase, wrapNest, hnext, htail] using hlift

theorem synchronized_cycle_realized (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k) :
    Relation.TransGen StepCtx (syncSource i ctx payloadTerm) (syncTarget i ctx payloadTerm) := by
  have hpath :
      ∀ m, m ≤ k →
        Relation.TransGen StepCtx (phase i ctx payloadTerm 0) (phase i ctx payloadTerm (m + 1)) := by
    intro m hm
    induction m with
    | zero =>
        exact Relation.TransGen.single (phase_step i ctx payloadTerm (r := 0) (by omega))
    | succ m ih =>
        have hprefix :
            Relation.TransGen StepCtx (phase i ctx payloadTerm 0) (phase i ctx payloadTerm (m + 1)) := by
          exact ih (by omega)
        have hstep : StepCtx (phase i ctx payloadTerm (m + 1)) (phase i ctx payloadTerm (m + 2)) := by
          exact phase_step i ctx payloadTerm (r := m + 1) (by omega)
        exact Relation.TransGen.trans hprefix (Relation.TransGen.single hstep)
  simpa [syncSource, syncTarget, phase, advance_zero, advance_cycleLen] using
    hpath k (Nat.le_refl _)

/-- Additive direct measures on the preserving SCC syntax. Slots are transparent and the
packet constructor is pure aggregation. -/
structure AdditiveMeasure where
  eval : SyncTerm k → Nat
  w_base : Nat
  w_payload : Nat
  w_empty : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval base = w_base
  eval_payload : eval payload = w_payload
  eval_empty : eval empty = w_empty
  eval_slot : ∀ i t, eval (slot i t) = eval t
  eval_cons : ∀ x xs, eval (cons x xs) = eval x + eval xs
  eval_wrap : ∀ x y, eval (wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ i ctx packet, eval (recur i ctx packet) = w_recur + eval ctx + eval packet
  h_wrap_pos : 1 ≤ w_wrap

lemma eval_syncPacket (M : AdditiveMeasure (k := k)) (i : Fin (k + 1)) :
    ∀ n, ∀ p : SyncTerm k, M.eval (syncPacket i n p) = n * M.eval p + M.w_empty
  | 0, p => by simp [syncPacket, M.eval_empty]
  | n + 1, p => by
      rw [syncPacket, M.eval_cons, M.eval_slot, eval_syncPacket M (advance i 1) n p]
      ring

lemma eval_wrapNest (M : AdditiveMeasure (k := k)) (p : SyncTerm k) :
    ∀ n t, M.eval (wrapNest p n t) = n * M.w_wrap + n * M.eval p + M.eval t
  | 0, t => by simp [wrapNest]
  | n + 1, t => by
      rw [wrapNest, eval_wrapNest M p n (wrap p t), M.eval_wrap]
      ring

theorem syncTarget_eval_gt (M : AdditiveMeasure (k := k)) (i : Fin (k + 1))
    (ctx payloadTerm : SyncTerm k) :
    M.eval (syncSource i ctx payloadTerm) < M.eval (syncTarget i ctx payloadTerm) := by
  have hsrc :
      M.eval (syncSource i ctx payloadTerm) =
        M.w_recur + M.eval ctx + ((k + 1) * M.eval payloadTerm + M.w_empty) := by
    simp [syncSource, M.eval_recur, eval_syncPacket]
  have htgt :
      M.eval (syncTarget i ctx payloadTerm) =
        (k + 1) * M.w_wrap + (k + 1) * M.eval payloadTerm +
          (M.w_recur + M.eval ctx + M.w_empty) := by
    simp [syncTarget, eval_wrapNest, M.eval_recur, M.eval_empty]
  rw [hsrc, htgt]
  have hnodes : 1 ≤ k + 1 := by omega
  have hwrap : 1 ≤ (k + 1) * M.w_wrap := by
    exact Nat.mul_le_mul hnodes M.h_wrap_pos
  omega

theorem no_additive_orients_synchronized_cycle (M : AdditiveMeasure (k := k)) :
    ¬ (∀ (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k),
      M.eval (syncTarget i ctx payloadTerm) < M.eval (syncSource i ctx payloadTerm)) := by
  intro h
  have hspec := h (0 : Fin (k + 1)) base payload
  have hgt := syncTarget_eval_gt M (0 : Fin (k + 1)) base payload
  exact Nat.lt_asymm hspec hgt

theorem no_global_orients_ctx_additive (M : AdditiveMeasure (k := k)) :
    ¬ GlobalOrientsCtx M.eval := by
  intro h
  have horient : DependencyPairsFragment.GlobalOrients StepCtx M.eval (· < ·) := by
    intro a b hstep
    exact h hstep
  have hpath :
      Relation.TransGen StepCtx
        (syncSource (0 : Fin (k + 1)) base payload)
        (syncTarget (0 : Fin (k + 1)) base payload) :=
    synchronized_cycle_realized (0 : Fin (k + 1)) base payload
  have hcomp :
      M.eval (syncTarget (0 : Fin (k + 1)) base payload) <
        M.eval (syncSource (0 : Fin (k + 1)) base payload) := by
    exact DependencyPairsFragment.transGen_drop (R := StepCtx) (m := M.eval) horient hpath
  have hgt :
      M.eval (syncSource (0 : Fin (k + 1)) base payload) <
        M.eval (syncTarget (0 : Fin (k + 1)) base payload) := by
    exact syncTarget_eval_gt M (0 : Fin (k + 1)) base payload
  exact Nat.lt_asymm hcomp hgt

/-! ## Conditional affine extension -/

/-- Affine constructor-local measures on the preserving finite-cycle syntax.

The packet constructors remain additive/transparent bookkeeping, while `wrap` and
`recur` carry the scaling coefficients.
-/
structure AffineMeasure where
  eval : SyncTerm k → Nat
  c_base : Nat
  c_payload : Nat
  c_empty : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_ctx : Nat
  recur_packet : Nat
  eval_base : eval base = c_base
  eval_payload : eval payload = c_payload
  eval_empty : eval empty = c_empty
  eval_slot : ∀ i t, eval (slot i t) = eval t
  eval_cons : ∀ x xs, eval (cons x xs) = eval x + eval xs
  eval_wrap : ∀ x y, eval (wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ i ctx packet,
      eval (recur i ctx packet) = recur_const + recur_ctx * eval ctx + recur_packet * eval packet
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

def AffineMeasure.wrapRightIter (M : AffineMeasure (k := k)) : Nat → Nat
  | 0 => 1
  | n + 1 => M.wrapRightIter n * M.wrap_right

def AffineMeasure.wrapConstIter (M : AffineMeasure (k := k)) : Nat → Nat
  | 0 => 0
  | n + 1 => M.wrapConstIter n + M.wrapRightIter n * M.wrap_const

def AffineMeasure.wrapLeftIter (M : AffineMeasure (k := k)) : Nat → Nat
  | 0 => 0
  | n + 1 => M.wrapLeftIter n + M.wrapRightIter n * M.wrap_left

lemma eval_syncPacket_affine (M : AffineMeasure (k := k)) (i : Fin (k + 1)) :
    ∀ n, ∀ p : SyncTerm k, M.eval (syncPacket i n p) = n * M.eval p + M.c_empty
  | 0, p => by simp [syncPacket, M.eval_empty]
  | n + 1, p => by
      rw [syncPacket, M.eval_cons, M.eval_slot, eval_syncPacket_affine M (advance i 1) n p]
      ring

lemma eval_wrapNest_affine (M : AffineMeasure (k := k)) (p : SyncTerm k) :
    ∀ n t,
      M.eval (wrapNest p n t) =
        M.wrapConstIter n + M.wrapLeftIter n * M.eval p + M.wrapRightIter n * M.eval t
  | 0, t => by
      simp [wrapNest, AffineMeasure.wrapConstIter, AffineMeasure.wrapLeftIter,
        AffineMeasure.wrapRightIter]
  | n + 1, t => by
      rw [wrapNest, eval_wrapNest_affine M p n (wrap p t), M.eval_wrap]
      simp [AffineMeasure.wrapConstIter, AffineMeasure.wrapLeftIter, AffineMeasure.wrapRightIter,
        Nat.mul_add, Nat.add_mul]
      ring

lemma wrapRightIter_pos (M : AffineMeasure (k := k)) : ∀ n, 1 ≤ M.wrapRightIter n
  | 0 => by simp [AffineMeasure.wrapRightIter]
  | n + 1 => by
      simp [AffineMeasure.wrapRightIter]
      exact Nat.mul_le_mul (wrapRightIter_pos M n) M.h_wrap_right_pos

lemma wrapLeftIter_pos (M : AffineMeasure (k := k)) :
    ∀ n, 0 < n → 1 ≤ M.wrapLeftIter n
  | 0, h => by cases Nat.not_lt_zero _ h
  | n + 1, _ => by
      have hterm : 1 ≤ M.wrapRightIter n * M.wrap_left := by
        exact Nat.mul_le_mul (wrapRightIter_pos M n) M.h_wrap_left_pos
      have hsum : 1 ≤ M.wrapLeftIter n + M.wrapRightIter n * M.wrap_left := by
        exact le_trans hterm (Nat.le_add_left _ _)
      simpa [AffineMeasure.wrapLeftIter] using hsum

def WrapperDominance (M : AffineMeasure (k := k)) : Prop :=
  (k + 1) * M.recur_packet < M.wrapLeftIter (k + 1)

theorem syncTarget_affine_eval_gt_of_wrapper_dominance
    (M : AffineMeasure (k := k)) (i : Fin (k + 1))
    (hdom : WrapperDominance M)
    (hunbounded : ∀ q : Nat, ∃ t : SyncTerm k, q ≤ M.eval t)
    (ctx : SyncTerm k) :
    ∃ payloadTerm,
      M.eval (syncSource i ctx payloadTerm) < M.eval (syncTarget i ctx payloadTerm) := by
  obtain ⟨payloadTerm, hpayload⟩ := hunbounded 1
  refine ⟨payloadTerm, ?_⟩
  have hsrc :
      M.eval (syncSource i ctx payloadTerm) =
        M.recur_const + M.recur_ctx * M.eval ctx +
          M.recur_packet * ((k + 1) * M.eval payloadTerm + M.c_empty) := by
    simp [syncSource, M.eval_recur, eval_syncPacket_affine]
  have htgt :
      M.eval (syncTarget i ctx payloadTerm) =
        M.wrapConstIter (k + 1) + M.wrapLeftIter (k + 1) * M.eval payloadTerm +
          M.wrapRightIter (k + 1) *
            (M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty) := by
    simp [syncTarget, eval_wrapNest_affine, M.eval_recur, M.eval_empty]
  rw [hsrc, htgt]
  unfold WrapperDominance at hdom
  have hcoeff : (k + 1) * M.recur_packet + 1 ≤ M.wrapLeftIter (k + 1) := by
    omega
  have hmul :
      ((k + 1) * M.recur_packet + 1) * M.eval payloadTerm ≤
        M.wrapLeftIter (k + 1) * M.eval payloadTerm := by
    exact Nat.mul_le_mul_right (M.eval payloadTerm) hcoeff
  have hpayloadPos : 1 ≤ M.eval payloadTerm := hpayload
  have hsrc_lt :
      M.recur_packet * ((k + 1) * M.eval payloadTerm + M.c_empty) <
        ((k + 1) * M.recur_packet + 1) * M.eval payloadTerm + M.recur_packet * M.c_empty := by
    have : ((k + 1) * M.recur_packet + 1) * M.eval payloadTerm + M.recur_packet * M.c_empty =
        M.recur_packet * ((k + 1) * M.eval payloadTerm + M.c_empty) + M.eval payloadTerm := by
      ring
    rw [this]
    exact Nat.lt_add_of_pos_right hpayloadPos
  have hconst :
      M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty ≤
        M.wrapConstIter (k + 1) + M.wrapRightIter (k + 1) *
          (M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty) := by
    have hpow : 1 ≤ M.wrapRightIter (k + 1) := wrapRightIter_pos M (k + 1)
    have hmul' :
        M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty ≤
          M.wrapRightIter (k + 1) *
            (M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty) := by
      calc
        M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty
            = 1 * (M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty) := by ring
        _ ≤ M.wrapRightIter (k + 1) *
              (M.recur_const + M.recur_ctx * M.eval ctx + M.recur_packet * M.c_empty) := by
              exact Nat.mul_le_mul_right _ hpow
    exact le_trans hmul' (Nat.le_add_left _ _)
  omega

theorem no_affine_orients_synchronized_cycle_of_wrapper_dominance
    (M : AffineMeasure (k := k))
    (hdom : WrapperDominance M)
    (hunbounded : ∀ q : Nat, ∃ t : SyncTerm k, q ≤ M.eval t) :
    ¬ (∀ (i : Fin (k + 1)) (ctx payloadTerm : SyncTerm k),
      M.eval (syncTarget i ctx payloadTerm) < M.eval (syncSource i ctx payloadTerm)) := by
  intro h
  obtain ⟨payloadTerm, hgt⟩ :=
    syncTarget_affine_eval_gt_of_wrapper_dominance
      M (0 : Fin (k + 1)) hdom hunbounded base
  have hspec := h (0 : Fin (k + 1)) base payloadTerm
  exact Nat.lt_asymm hspec hgt

theorem no_global_orients_ctx_affine_of_wrapper_dominance
    (M : AffineMeasure (k := k))
    (hdom : WrapperDominance M)
    (hunbounded : ∀ q : Nat, ∃ t : SyncTerm k, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx M.eval := by
  intro h
  obtain ⟨payloadTerm, hgt⟩ :=
    syncTarget_affine_eval_gt_of_wrapper_dominance
      M (0 : Fin (k + 1)) hdom hunbounded base
  have horient : DependencyPairsFragment.GlobalOrients StepCtx M.eval (· < ·) := by
    intro a b hstep
    exact h hstep
  have hpath :
      Relation.TransGen StepCtx
        (syncSource (0 : Fin (k + 1)) base payloadTerm)
        (syncTarget (0 : Fin (k + 1)) base payloadTerm) :=
    synchronized_cycle_realized (0 : Fin (k + 1)) base payloadTerm
  have hcomp :
      M.eval (syncTarget (0 : Fin (k + 1)) base payloadTerm) <
        M.eval (syncSource (0 : Fin (k + 1)) base payloadTerm) := by
    exact DependencyPairsFragment.transGen_drop (R := StepCtx) (m := M.eval) horient hpath
  exact Nat.lt_asymm hcomp hgt

end SyncTerm

end OperatorKO7.MutualDuplicationPreservingKNode
