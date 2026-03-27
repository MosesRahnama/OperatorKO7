import OperatorKO7.Meta.MutualDuplication_GraphCycle
import OperatorKO7.Meta.MutualDuplication_PacketGraph
import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.FiniteGraphSCC

/-!
# Relational Construction of Raw-Graph SCC Systems

This module removes the last hand-written graph packaging layer for the SCC barrier story.
Instead of first building a `GraphDupSystem` or `GraphPacketSystem` manually, a caller can
start from a smaller relation-level presentation:

- a node type and edge relation,
- the shared constructor interface, and
- a local edge-realization theorem for the delayed or preserving step pattern.

From that smaller presentation we construct the raw-graph system automatically and then
re-export the existing round-trip / finite-round-trip SCC barrier wrappers.
-/

namespace OperatorKO7.MutualDuplicationRelationalGraph

open OperatorKO7.DependencyPairsFragment

namespace Delayed

open OperatorKO7.MutualDuplicationGraphCycle
open OperatorKO7.FiniteGraphSCC

/-- Minimal delayed-duplication presentation over an arbitrary relation `R`. -/
structure Presentation (ι : Type) (R : ι → ι → Prop) where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : ι → T → T → T → T
  Step : T → T → Prop
  step_succ :
    ∀ {i j}, R i j → ∀ b s n,
      Step (recur i b s (succ n)) (wrap s (recur j b s n))

namespace Presentation

variable {ι : Type} {R : ι → ι → Prop} (P : Presentation ι R)

/-- Automatically assembled raw-graph delayed-duplication system. -/
def toGraphSystem : GraphDupSystem ι where
  T := P.T
  base := P.base
  succ := P.succ
  wrap := P.wrap
  recur := P.recur
  Edge := R
  Step := P.Step
  step_succ := P.step_succ

instance instDecidableRelToGraphSystem [DecidableRel R] : DecidableRel P.toGraphSystem.Edge := by
  simpa [Presentation.toGraphSystem]

abbrev GlobalOrientsCtx {α : Type} (m : P.T → α) (lt : α → α → Prop) : Prop :=
  GraphDupSystem.GlobalOrientsCtx P.toGraphSystem m lt

abbrev AdditiveMeasure := GraphDupSystem.AdditiveMeasure P.toGraphSystem
abbrev AffineMeasure := GraphDupSystem.AffineMeasure P.toGraphSystem
abbrev CompositionalMeasure := GraphDupSystem.CompositionalMeasure P.toGraphSystem

/-- Round-trip SCC wrapper for the additive delayed barrier from a relation-level presentation. -/
theorem no_global_orients_ctx_additive_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_additive_of_roundTrip
    (Sys := P.toGraphSystem) hij hji M

/-- Finite-round-trip SCC wrapper for the additive delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_additive_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_additive_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne M

/-- Round-trip SCC wrapper for the affine delayed barrier from a relation-level presentation. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    (M : P.AffineMeasure)
    (hunbounded :
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem) hij hji
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_affine_of_unbounded_of_roundTrip
    (Sys := P.toGraphSystem) hij hji M hunbounded

/-- Finite-round-trip SCC wrapper for the affine delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    (M : P.AffineMeasure)
    (hunbounded :
      let hijT := FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij hne
      let hjiT := FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji hne.symm
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem) hijT hjiT
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_affine_of_unbounded_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne M hunbounded

/-- Round-trip SCC wrapper for the transparent delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_compositional_transparent_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    (M : P.CompositionalMeasure)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_compositional_transparent_of_roundTrip
    (Sys := P.toGraphSystem) hij hji M htrans

/-- Finite-round-trip SCC wrapper for the transparent delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_compositional_transparent_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    (M : P.CompositionalMeasure)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_compositional_transparent_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne M htrans

/-- Round-trip scalar-projection wrapper for the delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (A :
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem) hij hji
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.AffineMeasure
        (MutualDuplicationCycleFlow.toDupSchema (P.toGraphSystem.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : P.T, π (μ t) = A.eval t)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphDupSystem.StepCtx P.toGraphSystem) μ Q :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_roundTrip
    (Sys := P.toGraphSystem) hij hji μ Q π hproj A hπ hunbounded

/-- Finite-round-trip scalar-projection wrapper for the delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (A :
      let hijT := FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij hne
      let hjiT := FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji hne.symm
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem) hijT hjiT
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.AffineMeasure
        (MutualDuplicationCycleFlow.toDupSchema (P.toGraphSystem.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : P.T, π (μ t) = A.eval t)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphDupSystem.StepCtx P.toGraphSystem) μ Q :=
  GraphDupSystem.CyclePath.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne μ Q π hproj A hπ hunbounded

/-- Finite-SCC wrapper for the additive delayed barrier from a relation-level presentation. -/
theorem no_global_orients_ctx_additive_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) := by
  simpa [Presentation.toGraphSystem] using
    (GraphDupSystem.CyclePath.no_global_orients_ctx_additive_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC M)

/-- Finite-SCC wrapper for the affine delayed barrier from a relation-level presentation. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    (M : P.AffineMeasure)
    (hunbounded :
      let hij := reachable_witnessSrc_witnessDst (R := R) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := R) hSCC
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem)
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij
          (witnessSrc_ne_witnessDst (R := R) hSCC))
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji
          (witnessSrc_ne_witnessDst (R := R) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) := by
  simpa [Presentation.toGraphSystem] using
    (GraphDupSystem.CyclePath.no_global_orients_ctx_affine_of_unbounded_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC M hunbounded)

/-- Finite-SCC wrapper for the transparent delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_compositional_transparent_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    (M : P.CompositionalMeasure)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) := by
  simpa [Presentation.toGraphSystem] using
    (GraphDupSystem.CyclePath.no_global_orients_ctx_compositional_transparent_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC M htrans)

/-- Finite-SCC wrapper for the scalar-projection delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (A :
      let hij := reachable_witnessSrc_witnessDst (R := R) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := R) hSCC
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem)
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij
          (witnessSrc_ne_witnessDst (R := R) hSCC))
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji
          (witnessSrc_ne_witnessDst (R := R) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.AffineMeasure
        (MutualDuplicationCycleFlow.toDupSchema (P.toGraphSystem.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : P.T, π (μ t) = A.eval t)
    (hunbounded :
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphDupSystem.StepCtx P.toGraphSystem) μ Q := by
  simpa [Presentation.toGraphSystem] using
    (GraphDupSystem.CyclePath.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC μ Q π hproj A hπ hunbounded)

/-- Search-based finite-SCC wrapper for the additive delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  no_global_orients_ctx_additive_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    M

/-- Search-based finite-SCC wrapper for the affine delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    (M : P.AffineMeasure)
    (hunbounded :
      let hSCC := (hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind
      let hij := reachable_witnessSrc_witnessDst (R := R) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := R) hSCC
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem)
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij
          (witnessSrc_ne_witnessDst (R := R) hSCC))
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji
          (witnessSrc_ne_witnessDst (R := R) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  no_global_orients_ctx_affine_of_unbounded_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    M hunbounded

/-- Search-based finite-SCC wrapper for the transparent delayed barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_compositional_transparent_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    (M : P.CompositionalMeasure)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  no_global_orients_ctx_compositional_transparent_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    M htrans

/-- Search-based finite-SCC wrapper for the scalar-projection delayed barrier from a
relation-level presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (A :
      let hSCC := (hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind
      let hij := reachable_witnessSrc_witnessDst (R := R) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := R) hSCC
      let C := GraphDupSystem.ofRoundTrip (Sys := P.toGraphSystem)
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij
          (witnessSrc_ne_witnessDst (R := R) hSCC))
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji
          (witnessSrc_ne_witnessDst (R := R) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.AffineMeasure
        (MutualDuplicationCycleFlow.toDupSchema (P.toGraphSystem.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : P.T, π (μ t) = A.eval t)
    (hunbounded :
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphDupSystem.StepCtx P.toGraphSystem) μ Q :=
  no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    μ Q π hproj A hπ hunbounded

end Presentation

end Delayed

namespace Preserving

open OperatorKO7.MutualDuplicationPacketGraph
open OperatorKO7.FiniteGraphSCC

/-- Minimal synchronized-packet presentation over an arbitrary relation `R`. -/
structure Presentation (ι : Type) (R : ι → ι → Prop) where
  T : Type
  empty : T
  wrap : T → T → T
  recur : ι → T → T → T
  packet : ι → Nat → T → T
  packet_zero : ∀ i p, packet i 0 p = empty
  Step : T → T → Prop
  step_packet :
    ∀ {i j}, R i j → ∀ ctx payload n,
      Step (recur i ctx (packet i (n + 1) payload))
        (wrap payload (recur j ctx (packet j n payload)))

namespace Presentation

variable {ι : Type} {R : ι → ι → Prop} (P : Presentation ι R)

/-- Automatically assembled raw-graph preserving packet system. -/
def toGraphSystem : GraphPacketSystem ι where
  T := P.T
  empty := P.empty
  wrap := P.wrap
  recur := P.recur
  packet := P.packet
  packet_zero := P.packet_zero
  Edge := R
  Step := P.Step
  step_packet := P.step_packet

instance instDecidableRelToGraphSystem [DecidableRel R] : DecidableRel P.toGraphSystem.Edge := by
  simpa [Presentation.toGraphSystem]

abbrev GlobalOrientsCtx (m : P.T → Nat) : Prop :=
  GraphPacketSystem.GlobalOrientsCtx P.toGraphSystem m

abbrev AdditiveMeasure := GraphPacketSystem.CyclePath.AdditiveMeasure P.toGraphSystem
abbrev AffineMeasure := GraphPacketSystem.CyclePath.AffineMeasure P.toGraphSystem
abbrev TransparentMeasure := GraphPacketSystem.CyclePath.TransparentMeasure P.toGraphSystem

/-- Round-trip SCC wrapper for the additive preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_additive_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_additive_of_roundTrip
    (Sys := P.toGraphSystem) hij hji M

/-- Finite-round-trip SCC wrapper for the additive preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_additive_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_additive_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne M

/-- Round-trip SCC wrapper for the affine preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    (M : P.AffineMeasure)
    (hdom :
      let C := GraphPacketSystem.ofRoundTrip (Sys := P.toGraphSystem) hij hji
      MutualDuplicationPayloadFlow.WrapperDominance
        (GraphPacketSystem.CyclePath.AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : P.T, q ≤ M.eval t) :
    ¬ P.GlobalOrientsCtx M.eval :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_affine_of_wrapper_dominance_of_roundTrip
    (Sys := P.toGraphSystem) hij hji M hdom hunbounded

/-- Finite-round-trip SCC wrapper for the affine preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    (M : P.AffineMeasure)
    (hdom :
      let hijT := FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij hne
      let hjiT := FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji hne.symm
      let C := GraphPacketSystem.ofRoundTrip (Sys := P.toGraphSystem) hijT hjiT
      MutualDuplicationPayloadFlow.WrapperDominance
        (GraphPacketSystem.CyclePath.AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : P.T, q ≤ M.eval t) :
    ¬ P.GlobalOrientsCtx M.eval :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_affine_of_wrapper_dominance_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne M hdom hunbounded

/-- Round-trip SCC wrapper for the transparent preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_transparent_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    (M : P.TransparentMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_transparent_of_roundTrip
    (Sys := P.toGraphSystem) hij hji M

/-- Finite-round-trip SCC wrapper for the transparent preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_transparent_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    (M : P.TransparentMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_transparent_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne M

/-- Round-trip scalar-projection wrapper for the preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_roundTrip
    {i j : ι} (hij : Relation.TransGen R i j) (hji : Relation.TransGen R j i)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (M : P.TransparentMeasure)
    (hπ : ∀ t : P.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphPacketSystem.StepCtx P.toGraphSystem) μ Q :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_of_scalar_projection_transparent_of_roundTrip
    (Sys := P.toGraphSystem) hij hji μ Q π hproj M hπ

/-- Finite-round-trip scalar-projection wrapper for the preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    {i j : ι}
    (hij : FiniteGraphReachability.Reachable R i j)
    (hji : FiniteGraphReachability.Reachable R j i) (hne : i ≠ j)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (M : P.TransparentMeasure)
    (hπ : ∀ t : P.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphPacketSystem.StepCtx P.toGraphSystem) μ Q :=
  GraphPacketSystem.CyclePath.no_global_orients_ctx_of_scalar_projection_transparent_of_finiteRoundTrip
    (Sys := P.toGraphSystem) hij hji hne μ Q π hproj M hπ

/-- Finite-SCC wrapper for the additive preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_additive_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval := by
  simpa [Presentation.toGraphSystem] using
    (GraphPacketSystem.CyclePath.no_global_orients_ctx_additive_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC M)

/-- Finite-SCC wrapper for the affine preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    (M : P.AffineMeasure)
    (hdom :
      let hij := reachable_witnessSrc_witnessDst (R := R) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := R) hSCC
      let C := GraphPacketSystem.ofRoundTrip (Sys := P.toGraphSystem)
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij
          (witnessSrc_ne_witnessDst (R := R) hSCC))
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji
          (witnessSrc_ne_witnessDst (R := R) hSCC).symm)
      MutualDuplicationPayloadFlow.WrapperDominance
        (GraphPacketSystem.CyclePath.AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : P.T, q ≤ M.eval t) :
    ¬ P.GlobalOrientsCtx M.eval := by
  simpa [Presentation.toGraphSystem] using
    (GraphPacketSystem.CyclePath.no_global_orients_ctx_affine_of_wrapper_dominance_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC M hdom hunbounded)

/-- Finite-SCC wrapper for the transparent preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_transparent_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    (M : P.TransparentMeasure) :
    ¬ P.GlobalOrientsCtx M.eval := by
  simpa [Presentation.toGraphSystem] using
    (GraphPacketSystem.CyclePath.no_global_orients_ctx_transparent_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC M)

/-- Finite-SCC wrapper for the scalar-projection preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hSCC : HasNontrivialSCC R)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (M : P.TransparentMeasure)
    (hπ : ∀ t : P.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphPacketSystem.StepCtx P.toGraphSystem) μ Q := by
  simpa [Presentation.toGraphSystem] using
    (GraphPacketSystem.CyclePath.no_global_orients_ctx_of_scalar_projection_transparent_of_hasNontrivialSCC
      (Sys := P.toGraphSystem) hSCC μ Q π hproj M hπ)

/-- Search-based finite-SCC wrapper for the additive preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  no_global_orients_ctx_additive_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    M

/-- Search-based finite-SCC wrapper for the affine preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    (M : P.AffineMeasure)
    (hdom :
      let hSCC := (hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind
      let hij := reachable_witnessSrc_witnessDst (R := R) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := R) hSCC
      let C := GraphPacketSystem.ofRoundTrip (Sys := P.toGraphSystem)
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hij
          (witnessSrc_ne_witnessDst (R := R) hSCC))
        (FiniteGraphReachability.transGen_of_reachable_of_ne (R := R) hji
          (witnessSrc_ne_witnessDst (R := R) hSCC).symm)
      MutualDuplicationPayloadFlow.WrapperDominance
        (GraphPacketSystem.CyclePath.AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : P.T, q ≤ M.eval t) :
    ¬ P.GlobalOrientsCtx M.eval :=
  no_global_orients_ctx_affine_of_wrapper_dominance_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    M hdom hunbounded

/-- Search-based finite-SCC wrapper for the transparent preserving barrier from a relation-level
presentation. -/
theorem no_global_orients_ctx_transparent_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    (M : P.TransparentMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  no_global_orients_ctx_transparent_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    M

/-- Search-based finite-SCC wrapper for the scalar-projection preserving barrier from a
relation-level presentation. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_exists_findNontrivialSCCPair?
    [Fintype ι] [DecidableEq ι] [DecidableRel R]
    (hfind : ∃ p : ι × ι, findNontrivialSCCPair? (R := R) = some p)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (M : P.TransparentMeasure)
    (hπ : ∀ t : P.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (GraphPacketSystem.StepCtx P.toGraphSystem) μ Q :=
  no_global_orients_ctx_of_scalar_projection_transparent_of_hasNontrivialSCC
    (P := P)
    ((hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (R := R)).2 hfind)
    μ Q π hproj M hπ

end Presentation

end Preserving

end OperatorKO7.MutualDuplicationRelationalGraph
