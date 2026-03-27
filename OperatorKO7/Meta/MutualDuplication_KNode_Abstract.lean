import OperatorKO7.Meta.MutualDuplication_CycleFlow
import OperatorKO7.Meta.MutualDuplication_KNode

/-!
# Abstract Delayed-Cycle Instantiation for Finite k-Node SCCs

This module shows that the finite delayed-duplication `k + 1`-node SCC development
factors through the abstract one-cycle interface from
`Meta/MutualDuplication_CycleFlow.lean`.
-/

namespace OperatorKO7.MutualDuplicationKNodeAbstract

open OperatorKO7.DependencyPairsFragment
open OperatorKO7.MutualDuplicationCycleFlow
open OperatorKO7.MutualDuplicationKNode
open OperatorKO7.StepDuplicating

namespace CyclicDupSchema

variable {k : Nat}

/-- Fix a node of the cyclic SCC and forget the remaining recursors. -/
def toNodeSchema (S : CyclicDupSchema k) (i : Fin (k + 1)) : StepDuplicatingSchema where
  T := S.T
  base := S.base
  succ := S.succ
  wrap := S.wrap
  recur := S.recur i

/-- Uniform transparent-compositional measures on the cyclic SCC schema. -/
structure CompositionalMeasure (S : CyclicDupSchema k) where
  eval : S.T → Nat
  c_base : Nat
  c_succ : Nat → Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat → Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = c_succ (eval t)
  eval_wrap : ∀ x y, eval (S.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ i b s n, eval (S.recur i b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm1 : ∀ x y, c_wrap x y > x
  wrap_subterm2 : ∀ x y, c_wrap x y > y

def AdditiveMeasure.toNodeMeasure {S : OperatorKO7.MutualDuplicationKNode.CyclicDupSchema k}
    (M : OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.AdditiveMeasure S) (i : Fin (k + 1)) :
    StepDuplicatingSchema.AdditiveMeasure (toNodeSchema S i) where
  eval := M.eval
  w_base := M.w_base
  w_succ := M.w_succ
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  h_wrap_pos := M.h_wrap_pos

def AffineMeasure.toNodeMeasure {S : OperatorKO7.MutualDuplicationKNode.CyclicDupSchema k}
    (M : OperatorKO7.MutualDuplicationKNode.CyclicDupSchema.AffineMeasure S) (i : Fin (k + 1)) :
    StepDuplicatingSchema.AffineMeasure (toNodeSchema S i) where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

def CompositionalMeasure.toNodeMeasure {S : CyclicDupSchema k}
    (M : CompositionalMeasure S) (i : Fin (k + 1)) :
    StepDuplicatingSchema.CompositionalMeasure (toNodeSchema S i) where
  eval := M.eval
  c_base := M.c_base
  c_succ := M.c_succ
  c_wrap := M.c_wrap
  c_recur := M.c_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  wrap_subterm1 := M.wrap_subterm1
  wrap_subterm2 := M.wrap_subterm2

end CyclicDupSchema

namespace CyclicDupSystem

variable {k : Nat}

open CyclicDupSchema

lemma cycleFlow_succIter_eq (Sys : CyclicDupSystem k) :
    ∀ n t,
      OperatorKO7.MutualDuplicationCycleFlow.succIterOn
          (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) n t =
        Sys.toCyclicDupSchema.succIter n t
  | 0, t => by rfl
  | n + 1, t => by
      rw [OperatorKO7.MutualDuplicationCycleFlow.succIterOn, CyclicDupSchema.succIter,
        cycleFlow_succIter_eq Sys n]
      rfl

lemma cycleFlow_wrapNest_eq (Sys : CyclicDupSystem k) (s : Sys.T) :
    ∀ n t,
      OperatorKO7.MutualDuplicationCycleFlow.wrapNest
          (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) s n t =
        Sys.toCyclicDupSchema.wrapNest s n t
  | 0, t => by rfl
  | n + 1, t => by
      rw [OperatorKO7.MutualDuplicationCycleFlow.wrapNest, CyclicDupSchema.wrapNest,
        cycleFlow_wrapNest_eq Sys s n]
      rfl

/-- The finite cyclic delayed-duplication system at node `0` as an abstract cycle witness. -/
def cycleWitness (Sys : CyclicDupSystem k) :
    MutualDuplicationCycleFlow.CycleWitness
      (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) (k + 1) where
  StepCtx := StepCtx Sys
  cycle_realized := by
    intro b s n
    simpa [OperatorKO7.MutualDuplicationCycleFlow.cycleSource,
      OperatorKO7.MutualDuplicationCycleFlow.cycleTarget,
      cycleFlow_succIter_eq Sys (k + 1) n, cycleFlow_wrapNest_eq Sys s (k + 1)] using
      CyclicDupSchema.CyclicDupSystem.cycle_realized Sys (0 : Fin (k + 1)) b s n

/-- The additive finite-cycle barrier factors through the abstract delayed-cycle layer. -/
theorem no_global_orients_ctx_additive_via_cycleFlow
    (Sys : CyclicDupSystem k) (M : CyclicDupSchema.AdditiveMeasure Sys.toCyclicDupSchema) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  exact
    MutualDuplicationCycleFlow.no_global_orients_ctx_additive
      (W := cycleWitness Sys)
      (M := CyclicDupSchema.AdditiveMeasure.toNodeMeasure M (0 : Fin (k + 1)))
      (hcopies := Nat.succ_pos _)

/-- The affine finite-cycle barrier also factors through the abstract delayed-cycle layer. -/
theorem no_global_orients_ctx_affine_of_unbounded_via_cycleFlow
    (Sys : CyclicDupSystem k) (M : CyclicDupSchema.AffineMeasure Sys.toCyclicDupSchema)
    (hunbounded :
      StepDuplicatingSchema.HasUnboundedRange
        (OperatorKO7.MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          (CyclicDupSchema.AffineMeasure.toNodeMeasure M (0 : Fin (k + 1)))
          (k + 1) (Nat.succ_pos _))) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  exact
    MutualDuplicationCycleFlow.no_global_orients_ctx_affine_of_unbounded
      (W := cycleWitness Sys)
      (M := CyclicDupSchema.AffineMeasure.toNodeMeasure M (0 : Fin (k + 1)))
      (hcopies := Nat.succ_pos _)
      (hunbounded := hunbounded)

/-- The transparent-compositional finite-cycle barrier also factors through the abstract
delayed-cycle layer. -/
theorem no_global_orients_ctx_compositional_transparent_via_cycleFlow
    (Sys : CyclicDupSystem k)
    (M : CyclicDupSchema.CompositionalMeasure Sys.toCyclicDupSchema)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  exact
    MutualDuplicationCycleFlow.no_global_orients_ctx_compositional_transparent
      (W := cycleWitness Sys)
      (CM := CyclicDupSchema.CompositionalMeasure.toNodeMeasure M (0 : Fin (k + 1)))
      (hcopies := Nat.succ_pos _)
      (htrans := htrans)

/-- A projected affine contradiction on the derived one-cycle schema also blocks any
strict codomain order on the finite cyclic delayed-duplication relation. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_via_cycleFlow
    {α : Type}
    (Sys : CyclicDupSystem k) (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A :
      StepDuplicatingSchema.AffineMeasure
        (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
          (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) (k + 1)))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  exact
    MutualDuplicationCycleFlow.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
      (W := cycleWitness Sys) (μ := μ) (R := R) (π := π)
      (hproj := hproj) (A := A) (hπ := hπ) (hunbounded := hunbounded)

/-- Weighted functional matrix-style corollary obtained through the abstract delayed-cycle
projection theorem. -/
theorem no_global_orients_ctx_matrixFunctional_of_projected_unbounded_via_cycleFlow
    {d : Nat}
    (Sys : CyclicDupSystem k)
    (M :
      StepDuplicatingSchema.MatrixFunctionalMeasure
        (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
          (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) (k + 1)) d)
    (hunbounded : StepDuplicatingSchema.HasUnboundedWeightedRange M) :
    ¬ DependencyPairsFragment.GlobalOrients
        (StepCtx Sys) M.eval (fun u v => StepDuplicatingSchema.VecLt u v) := by
  exact
    no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_via_cycleFlow
      (Sys := Sys)
      (μ := M.eval)
      (R := fun u v => StepDuplicatingSchema.VecLt u v)
      (π := StepDuplicatingSchema.weightedSum M.weight)
      (hproj := by
        intro u v h
        exact StepDuplicatingSchema.weightedSum_lt_of_vecLt M.h_weight_support h)
      (A := M.projectedAffine)
      (hπ := by intro t; rfl)
      (hunbounded := by
        intro q
        rcases hunbounded q with ⟨t, ht⟩
        exact ⟨t, ht⟩)

/-- Fixed-dimension tracked-component contextual corollary via the abstract delayed-cycle
projection theorem. -/
theorem no_global_orients_ctx_matrixD_of_componentwise_pump_via_cycleFlow
    {d : Nat} {tracked : Fin d}
    (Sys : CyclicDupSystem k)
    (M :
      StepDuplicatingSchema.MatrixMeasureD
        (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
          (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) (k + 1)) d tracked)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeTracked M) :
    ¬ DependencyPairsFragment.GlobalOrients
        (StepCtx Sys) M.eval (fun u v => StepDuplicatingSchema.VecLt u v) := by
  exact
    no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_via_cycleFlow
      (Sys := Sys)
      (μ := M.eval)
      (R := fun u v => StepDuplicatingSchema.VecLt u v)
      (π := fun v => v tracked)
      (hproj := by
        intro u v h
        exact h tracked)
      (A := M.trackedAffine)
      (hπ := by intro t; rfl)
      (hunbounded := by
        intro q
        rcases hunbounded q with ⟨t, ht⟩
        exact ⟨t, ht⟩)

/-- Dimension-2 tracked-component contextual corollary via the abstract delayed-cycle
projection theorem. -/
theorem no_global_orients_ctx_matrix2_of_componentwise_pump_via_cycleFlow
    (Sys : CyclicDupSystem k)
    (M :
      StepDuplicatingSchema.MatrixMeasure2
        (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
          (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) (k + 1)))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange1 M) :
    ¬ DependencyPairsFragment.GlobalOrients
        (StepCtx Sys) M.eval StepDuplicatingSchema.PairLt := by
  exact
    no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_via_cycleFlow
      (Sys := Sys)
      (μ := M.eval)
      (R := StepDuplicatingSchema.PairLt)
      (π := Prod.fst)
      (hproj := by
        intro u v h
        exact h.1)
      (A := M.fstAffine)
      (hπ := by intro t; rfl)
      (hunbounded := by
        intro q
        rcases hunbounded q with ⟨t, ht⟩
        exact ⟨t, by simpa [StepDuplicatingSchema.MatrixMeasure2.fstAffine] using ht⟩)

/-- Balanced mixed-coordinate contextual corollary via the abstract delayed-cycle projection
theorem. -/
theorem no_global_orients_ctx_matrixMix2_of_sum_pump_via_cycleFlow
    (Sys : CyclicDupSystem k)
    (M :
      StepDuplicatingSchema.MatrixMix2Measure
        (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
          (CyclicDupSchema.toNodeSchema Sys.toCyclicDupSchema (0 : Fin (k + 1))) (k + 1)))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeSum M) :
    ¬ DependencyPairsFragment.GlobalOrients
        (StepCtx Sys) M.eval StepDuplicatingSchema.PairLt := by
  exact
    no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_via_cycleFlow
      (Sys := Sys)
      (μ := M.eval)
      (R := StepDuplicatingSchema.PairLt)
      (π := StepDuplicatingSchema.vecSum)
      (hproj := by
        intro u v h
        exact StepDuplicatingSchema.vecSum_lt_of_pairLt h)
      (A := M.sumAffine)
      (hπ := by intro t; rfl)
      (hunbounded := by
        intro q
        rcases hunbounded q with ⟨t, ht⟩
        exact ⟨t, ht⟩)

end CyclicDupSystem

end OperatorKO7.MutualDuplicationKNodeAbstract
