import OperatorKO7.Meta.MutualDuplication_Preserving_KNode
import OperatorKO7.Meta.MatrixBarrierFunctional

/-!
# Packet-Transparent Preserving SCC Extension

This module adds a narrow Tier-2 style corollary for the finite synchronized-packet
preserving SCCs. The latent packet constructors are treated as evaluation-transparent
bookkeeping, so one full synchronized cycle is still blocked by the visible wrapper
exposure.
-/

namespace OperatorKO7.MutualDuplicationPreservingTransparent

open OperatorKO7.DependencyPairsFragment

namespace PreservingKNode

variable {k : Nat}

/-- Local alias for the preserving finite-cycle syntax. -/
abbrev KTerm (k : Nat) := OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm k

open OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm
  (base payload empty slot cons wrap recur advance syncPacket syncSource syncTarget wrapNest
   synchronized_cycle_realized StepCtx GlobalOrientsCtx)

/-- Transparent compositional measures that ignore the packet bookkeeping layer. -/
structure PacketTransparentMeasure where
  eval : KTerm k → Nat
  c_base : Nat
  c_payload : Nat
  c_empty : Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat
  eval_base : eval base = c_base
  eval_payload : eval payload = c_payload
  eval_empty : eval empty = c_empty
  eval_slot : ∀ i t, eval (slot i t) = eval t
  eval_cons : ∀ x xs, eval (cons x xs) = eval xs
  eval_wrap : ∀ x y, eval (wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ i ctx packet, eval (recur i ctx packet) = c_recur (eval ctx) (eval packet)
  wrap_subterm2 : ∀ x y, c_wrap x y > y

lemma eval_syncPacket_eq_empty (CM : PacketTransparentMeasure (k := k)) (i : Fin (k + 1)) :
    ∀ n, ∀ p : KTerm k, CM.eval (syncPacket i n p) = CM.c_empty
  | 0, p => by simp [syncPacket, CM.eval_empty]
  | n + 1, p => by
      rw [syncPacket, CM.eval_cons, eval_syncPacket_eq_empty CM (advance i 1) n p]

lemma syncSource_eval_eq_empty_packet (CM : PacketTransparentMeasure (k := k))
    (i : Fin (k + 1)) (ctx payloadTerm : KTerm k) :
    CM.eval (syncSource i ctx payloadTerm) = CM.c_recur (CM.eval ctx) CM.c_empty := by
  rw [syncSource, CM.eval_recur, eval_syncPacket_eq_empty CM i (k + 1) payloadTerm]

lemma wrapNest_strict_mono_right (CM : PacketTransparentMeasure (k := k)) (p : KTerm k) :
    ∀ n t, 0 < n → CM.eval t < CM.eval (wrapNest p n t)
  | 0, t, h => by
      cases Nat.not_lt_zero _ h
  | 1, t, _ => by
      simpa [wrapNest, CM.eval_wrap] using
        CM.wrap_subterm2 (CM.eval p) (CM.eval t)
  | n + 2, t, _ => by
      have hbase : CM.eval t < CM.eval (wrap p t) := by
        rw [CM.eval_wrap]
        exact CM.wrap_subterm2 (CM.eval p) (CM.eval t)
      have htail :
          CM.eval (wrap p t) < CM.eval (wrapNest p (n + 1) (wrap p t)) := by
        exact wrapNest_strict_mono_right CM p (n + 1) (wrap p t) (Nat.succ_pos _)
      rw [wrapNest]
      exact Nat.lt_trans hbase htail

theorem syncTarget_eval_gt_packetTransparent (CM : PacketTransparentMeasure (k := k))
    (i : Fin (k + 1)) (ctx payloadTerm : KTerm k) :
    CM.eval (syncSource i ctx payloadTerm) < CM.eval (syncTarget i ctx payloadTerm) := by
  rw [syncTarget]
  rw [syncSource_eval_eq_empty_packet CM i ctx payloadTerm]
  have hwrap :
      CM.eval (recur i ctx empty) < CM.eval (wrapNest payloadTerm (k + 1) (recur i ctx empty)) := by
    exact wrapNest_strict_mono_right CM payloadTerm (k + 1) (recur i ctx empty) (Nat.succ_pos _)
  simpa [CM.eval_recur, CM.eval_empty] using hwrap

theorem no_compositional_orients_synchronized_cycle_packetTransparent
    (CM : PacketTransparentMeasure (k := k)) :
    ¬ (∀ (i : Fin (k + 1)) (ctx payloadTerm : KTerm k),
      CM.eval (syncTarget i ctx payloadTerm) < CM.eval (syncSource i ctx payloadTerm)) := by
  intro h
  have hspec := h (0 : Fin (k + 1)) base payload
  have hgt := syncTarget_eval_gt_packetTransparent CM (0 : Fin (k + 1)) base payload
  exact Nat.lt_asymm hspec hgt

theorem no_global_orients_ctx_packetTransparent
    (CM : PacketTransparentMeasure (k := k)) :
    ¬ GlobalOrientsCtx (k := k) CM.eval := by
  intro h
  have horient :
      DependencyPairsFragment.GlobalOrients StepCtx CM.eval (· < ·) := by
    intro a b hstep
    exact h hstep
  have hpath :
      Relation.TransGen StepCtx
        (syncSource (0 : Fin (k + 1)) base payload)
        (syncTarget (0 : Fin (k + 1)) base payload) :=
    synchronized_cycle_realized (0 : Fin (k + 1)) base payload
  have hcomp :
      CM.eval (syncTarget (0 : Fin (k + 1)) base payload) <
        CM.eval (syncSource (0 : Fin (k + 1)) base payload) := by
    exact DependencyPairsFragment.transGen_drop (R := StepCtx) (m := CM.eval) horient hpath
  have hgt :
      CM.eval (syncSource (0 : Fin (k + 1)) base payload) <
        CM.eval (syncTarget (0 : Fin (k + 1)) base payload) := by
    exact syncTarget_eval_gt_packetTransparent CM (0 : Fin (k + 1)) base payload
  exact Nat.lt_asymm hcomp hgt

/-- Generic scalar-projection lift for the packet-transparent preserving SCC barrier. -/
theorem no_global_orients_ctx_of_scalar_projection
    {α : Type} (μ : KTerm k → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (CM : PacketTransparentMeasure (k := k))
    (hπ : ∀ t : KTerm k, π (μ t) = CM.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients StepCtx μ R := by
  intro h
  have hscalar : GlobalOrientsCtx (k := k) CM.eval := by
    intro a b hstep
    have hlt : π (μ b) < π (μ a) := hproj (h hstep)
    simpa [hπ a, hπ b] using hlt
  exact no_global_orients_ctx_packetTransparent CM hscalar

/-- Weighted componentwise matrix-style extension of the packet-transparent preserving SCC barrier. -/
theorem no_global_orients_ctx_matrixFunctional_of_projected_packetTransparent
    {d : Nat} (μ : KTerm k → Fin d → Nat) (weight : Fin d → Nat)
    (hsupport : ∃ i : Fin d, 1 ≤ weight i)
    (CM : PacketTransparentMeasure (k := k))
    (hπ :
      ∀ t : KTerm k,
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.weightedSum weight (μ t) = CM.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients
        StepCtx μ (fun u v => OperatorKO7.StepDuplicating.StepDuplicatingSchema.VecLt u v) := by
  exact
    no_global_orients_ctx_of_scalar_projection
      (μ := μ)
      (R := fun u v => OperatorKO7.StepDuplicating.StepDuplicatingSchema.VecLt u v)
      (π := fun v => OperatorKO7.StepDuplicating.StepDuplicatingSchema.weightedSum weight v)
      (hproj := fun h =>
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.weightedSum_lt_of_vecLt
          hsupport h)
      (CM := CM)
      (hπ := hπ)

end PreservingKNode

end OperatorKO7.MutualDuplicationPreservingTransparent
