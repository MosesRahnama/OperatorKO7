import OperatorKO7.Meta.MutualDuplication_PayloadFlow
import OperatorKO7.Meta.MutualDuplication_Preserving_KNode
import OperatorKO7.Meta.MutualDuplication_Preserving_Transparent

/-!
# Abstract Payload-Flow Instantiation for Finite Preserving Cycles

This module shows that the finite synchronized-packet preserving SCC development factors
through the abstract payload-flow metatheorems. The explicit packet syntax remains the
concrete witness, but the additive and affine global barriers are now recovered from a
smaller abstract cycle interface.
-/

namespace OperatorKO7.MutualDuplicationPreservingAbstract

open OperatorKO7.DependencyPairsFragment
open OperatorKO7.MutualDuplicationPayloadFlow
open OperatorKO7.MutualDuplicationPreservingKNode

namespace SyncTerm

variable {k : Nat}

open OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm

/-- The finite preserving syntax at a fixed cycle index as an abstract packet model. -/
def packetModel (i : Fin (k + 1)) :
    PacketModel (OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm k) where
  empty := empty
  wrap := wrap
  recur := recur i
  packet := syncPacket i

lemma payloadFlow_wrapNest_eq (p : OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm k) :
    ∀ n t,
      OperatorKO7.MutualDuplicationPayloadFlow.wrapNest wrap p n t =
        OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.wrapNest p n t
  | 0, t => by rfl
  | n + 1, t => by
      simp [OperatorKO7.MutualDuplicationPayloadFlow.wrapNest,
        OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.wrapNest,
        payloadFlow_wrapNest_eq p n (wrap p t)]

/-- The exact one-cycle path for the finite preserving system in abstract form. -/
def cycleWitness (i : Fin (k + 1)) :
    CycleWitness (packetModel (k := k) i) (k + 1) where
  StepCtx := StepCtx
  cycle_realized := by
    intro ctx p
    simpa [packetModel,
      OperatorKO7.MutualDuplicationPayloadFlow.syncSource,
      OperatorKO7.MutualDuplicationPayloadFlow.syncTarget,
      OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.syncSource,
      OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.syncTarget,
      payloadFlow_wrapNest_eq] using
      synchronized_cycle_realized i ctx p

/-- The explicit additive preserving measure as an abstract payload-flow measure. -/
def AdditiveMeasure.toPayloadFlow (M : AdditiveMeasure (k := k)) (i : Fin (k + 1)) :
    MutualDuplicationPayloadFlow.AdditiveMeasure (packetModel (k := k) i) where
  eval := M.eval
  w_empty := M.w_empty
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_empty := M.eval_empty
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  eval_packet := eval_syncPacket M i
  h_wrap_pos := M.h_wrap_pos

/-- The explicit affine preserving measure as an abstract payload-flow measure. -/
def AffineMeasure.toPayloadFlow (M : AffineMeasure (k := k)) (i : Fin (k + 1)) :
    MutualDuplicationPayloadFlow.AffineMeasure (packetModel (k := k) i) where
  eval := M.eval
  c_empty := M.c_empty
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_ctx := M.recur_ctx
  recur_packet := M.recur_packet
  eval_empty := M.eval_empty
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  eval_packet := eval_syncPacket_affine M i
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

lemma toPayloadFlow_wrapRightIter (M : AffineMeasure (k := k)) (i : Fin (k + 1)) :
    ∀ n,
      (AffineMeasure.toPayloadFlow M i).wrapRightIter n =
        OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.AffineMeasure.wrapRightIter M n
  | 0 => by rfl
  | n + 1 => by
      rw [MutualDuplicationPayloadFlow.AffineMeasure.wrapRightIter,
        OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.AffineMeasure.wrapRightIter,
        toPayloadFlow_wrapRightIter M i n]
      rfl

lemma toPayloadFlow_wrapLeftIter (M : AffineMeasure (k := k)) (i : Fin (k + 1)) :
    ∀ n,
      (AffineMeasure.toPayloadFlow M i).wrapLeftIter n =
        OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.AffineMeasure.wrapLeftIter M n
  | 0 => by rfl
  | n + 1 => by
      rw [MutualDuplicationPayloadFlow.AffineMeasure.wrapLeftIter,
        OperatorKO7.MutualDuplicationPreservingKNode.SyncTerm.AffineMeasure.wrapLeftIter,
        toPayloadFlow_wrapLeftIter M i n, toPayloadFlow_wrapRightIter M i n]
      rfl

/-- The concrete packet-transparent measure as an abstract payload-flow transparent measure. -/
def PacketTransparentMeasure.toPayloadFlow
    (M :
      OperatorKO7.MutualDuplicationPreservingTransparent.PreservingKNode.PacketTransparentMeasure
        (k := k))
    (i : Fin (k + 1)) :
    MutualDuplicationPayloadFlow.TransparentMeasure (packetModel (k := k) i) where
  eval := M.eval
  c_empty := M.c_empty
  c_wrap := M.c_wrap
  c_recur := M.c_recur
  eval_empty := M.eval_empty
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  eval_packet :=
    OperatorKO7.MutualDuplicationPreservingTransparent.PreservingKNode.eval_syncPacket_eq_empty M i
  wrap_subterm2 := M.wrap_subterm2

/-- The additive finite-cycle preserving barrier factors through the abstract payload-flow
metatheorem. -/
theorem no_global_orients_ctx_additive_via_payloadFlow
    (M : AdditiveMeasure (k := k)) :
    ¬ GlobalOrientsCtx M.eval := by
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_additive
      (W := cycleWitness (k := k) (0 : Fin (k + 1)))
      (A := AdditiveMeasure.toPayloadFlow M (0 : Fin (k + 1)))
      (hcopies := by omega)

/-- The affine finite-cycle preserving barrier also factors through the abstract
payload-flow metatheorem. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_via_payloadFlow
    (M : AffineMeasure (k := k))
    (hdom : SyncTerm.WrapperDominance M)
    (hunbounded : ∀ q : Nat, ∃ t : SyncTerm k, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx M.eval := by
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_affine_of_wrapper_dominance
      (W := cycleWitness (k := k) (0 : Fin (k + 1)))
      (A := AffineMeasure.toPayloadFlow M (0 : Fin (k + 1)))
      (hdom := by
        simpa [OperatorKO7.MutualDuplicationPayloadFlow.WrapperDominance,
          SyncTerm.WrapperDominance, toPayloadFlow_wrapLeftIter M (0 : Fin (k + 1)) (k + 1)] using hdom)
      (hunbounded := hunbounded)

/-- The packet-transparent preserving barrier also factors through the abstract
payload-flow metatheorem. -/
theorem no_global_orients_ctx_packetTransparent_via_payloadFlow
    (M :
      OperatorKO7.MutualDuplicationPreservingTransparent.PreservingKNode.PacketTransparentMeasure
        (k := k)) :
    ¬ GlobalOrientsCtx M.eval := by
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_transparent
      (W := cycleWitness (k := k) (0 : Fin (k + 1)))
      (A := PacketTransparentMeasure.toPayloadFlow M (0 : Fin (k + 1)))
      (hcopies := Nat.succ_pos _)

/-- The projected packet-transparent preserving barrier also factors through the abstract
payload-flow scalar-projection theorem. -/
theorem no_global_orients_ctx_matrixFunctional_of_projected_packetTransparent_via_payloadFlow
    {d : Nat} (μ : SyncTerm k → Fin d → Nat) (weight : Fin d → Nat)
    (hsupport : ∃ i : Fin d, 1 ≤ weight i)
    (M :
      OperatorKO7.MutualDuplicationPreservingTransparent.PreservingKNode.PacketTransparentMeasure
        (k := k))
    (hπ :
      ∀ t : SyncTerm k,
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.weightedSum weight (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients
        StepCtx μ (fun u v => OperatorKO7.StepDuplicating.StepDuplicatingSchema.VecLt u v) := by
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_of_scalar_projection_transparent
      (W := cycleWitness (k := k) (0 : Fin (k + 1)))
      (μ := μ)
      (R := fun u v => OperatorKO7.StepDuplicating.StepDuplicatingSchema.VecLt u v)
      (π := fun v => OperatorKO7.StepDuplicating.StepDuplicatingSchema.weightedSum weight v)
      (hproj := fun h =>
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.weightedSum_lt_of_vecLt
          hsupport h)
      (A := PacketTransparentMeasure.toPayloadFlow M (0 : Fin (k + 1)))
      (hπ := hπ)
      (hcopies := Nat.succ_pos _)

end SyncTerm

end OperatorKO7.MutualDuplicationPreservingAbstract
