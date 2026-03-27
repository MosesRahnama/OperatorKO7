import OperatorKO7.Meta.DependencyPairs_CallGraph
import OperatorKO7.Meta.MutualDuplication_RelationalGraph

/-!
# Call-Graph Construction of SCC Barrier Systems

This module removes another manual layer from the SCC barrier transport stack. Instead of
starting from an explicit edge relation, callers can present a finite extracted call graph:

- a finite node type,
- a key attached to each node,
- the finite successor-key set extracted from each node, and
- the local delayed or preserving edge-realization theorem whenever a target key appears in
  that successor-key set.

From that concrete call-graph presentation we build the relation-level delayed or
preserving system automatically and reexport the finite-SCC search-result barrier wrappers.
-/

namespace OperatorKO7.MutualDuplicationCallGraph

open OperatorKO7.DependencyPairsFragment

namespace Delayed

open OperatorKO7.MutualDuplicationRelationalGraph

/-- Delayed-duplication presentation over a finite extracted call graph. -/
structure Presentation (ι κ : Type) [Fintype ι] [DecidableEq ι] [DecidableEq κ] where
  graph : FiniteCallGraph ι κ
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : ι → T → T → T → T
  Step : T → T → Prop
  step_succ_of_mem :
    ∀ {i j}, graph.nodeKey j ∈ graph.succKeys i → ∀ b s n,
      Step (recur i b s (succ n)) (wrap s (recur j b s n))

namespace Presentation

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ] (P : Presentation ι κ)

abbrev Edge : ι → ι → Prop := P.graph.Edge

instance instDecidableRelEdge : DecidableRel P.Edge := by
  intro i j
  dsimp [Edge, FiniteCallGraph.Edge]
  infer_instance

/-- Convert the call-graph presentation to the existing relation-level delayed system. -/
def toRelational :
    MutualDuplicationRelationalGraph.Delayed.Presentation ι P.Edge where
  T := P.T
  base := P.base
  succ := P.succ
  wrap := P.wrap
  recur := P.recur
  Step := P.Step
  step_succ := by
    intro i j hij b s n
    exact P.step_succ_of_mem hij b s n

abbrev AdditiveMeasure := (P.toRelational).AdditiveMeasure
abbrev AffineMeasure := (P.toRelational).AffineMeasure
abbrev CompositionalMeasure := (P.toRelational).CompositionalMeasure
abbrev GlobalOrientsCtx {α : Type} (m : P.T → α) (lt : α → α → Prop) : Prop :=
  (P.toRelational).GlobalOrientsCtx m lt
abbrev HasNontrivialSCC : Prop := P.graph.HasNontrivialSCC
noncomputable abbrev findNontrivialSCCPair? : Option (ι × ι) := P.graph.findNontrivialSCCPair?

theorem no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  OperatorKO7.MutualDuplicationRelationalGraph.Delayed.Presentation.no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind M

theorem no_global_orients_ctx_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    (M : P.AffineMeasure)
    (hunbounded :
      let hSCC := (P.graph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?).2 hfind
      let hij := OperatorKO7.FiniteGraphSCC.reachable_witnessSrc_witnessDst (R := P.Edge) hSCC
      let hji := OperatorKO7.FiniteGraphSCC.reachable_witnessDst_witnessSrc (R := P.Edge) hSCC
      let C := MutualDuplicationGraphCycle.GraphDupSystem.ofRoundTrip
        (Sys := P.toRelational.toGraphSystem)
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne (R := P.Edge) hij
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst (R := P.Edge) hSCC))
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne (R := P.Edge) hji
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst (R := P.Edge) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (OperatorKO7.MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          (MutualDuplicationGraphCycle.GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  OperatorKO7.MutualDuplicationRelationalGraph.Delayed.Presentation.no_global_orients_ctx_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind M hunbounded

theorem no_global_orients_ctx_compositional_transparent_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    (M : P.CompositionalMeasure)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  OperatorKO7.MutualDuplicationRelationalGraph.Delayed.Presentation.no_global_orients_ctx_compositional_transparent_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind M htrans

theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (A :
      let hSCC := (P.graph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?).2 hfind
      let hij := OperatorKO7.FiniteGraphSCC.reachable_witnessSrc_witnessDst (R := P.Edge) hSCC
      let hji := OperatorKO7.FiniteGraphSCC.reachable_witnessDst_witnessSrc (R := P.Edge) hSCC
      let C := MutualDuplicationGraphCycle.GraphDupSystem.ofRoundTrip
        (Sys := P.toRelational.toGraphSystem)
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne (R := P.Edge) hij
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst (R := P.Edge) hSCC))
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne (R := P.Edge) hji
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst (R := P.Edge) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.AffineMeasure
        (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
          (P.toRelational.toGraphSystem.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : P.T, π (μ t) = A.eval t)
    (hunbounded :
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ OperatorKO7.DependencyPairsFragment.GlobalOrients
      (OperatorKO7.MutualDuplicationGraphCycle.GraphDupSystem.StepCtx P.toRelational.toGraphSystem)
      μ Q :=
  OperatorKO7.MutualDuplicationRelationalGraph.Delayed.Presentation.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind μ Q π hproj A hπ hunbounded

end Presentation

end Delayed

namespace Preserving

open OperatorKO7.MutualDuplicationRelationalGraph

/-- Preserving synchronized-packet presentation over a finite extracted call graph. -/
structure Presentation (ι κ : Type) [Fintype ι] [DecidableEq ι] [DecidableEq κ] where
  graph : FiniteCallGraph ι κ
  T : Type
  empty : T
  wrap : T → T → T
  recur : ι → T → T → T
  packet : ι → Nat → T → T
  packet_zero : ∀ i p, packet i 0 p = empty
  Step : T → T → Prop
  step_packet_of_mem :
    ∀ {i j}, graph.nodeKey j ∈ graph.succKeys i → ∀ ctx payload n,
      Step (recur i ctx (packet i (n + 1) payload))
        (wrap payload (recur j ctx (packet j n payload)))

namespace Presentation

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ] (P : Presentation ι κ)

abbrev Edge : ι → ι → Prop := P.graph.Edge

instance instDecidableRelEdge : DecidableRel P.Edge := by
  intro i j
  dsimp [Edge, FiniteCallGraph.Edge]
  infer_instance

/-- Convert the call-graph presentation to the existing relation-level preserving system. -/
def toRelational :
    MutualDuplicationRelationalGraph.Preserving.Presentation ι P.Edge where
  T := P.T
  empty := P.empty
  wrap := P.wrap
  recur := P.recur
  packet := P.packet
  packet_zero := P.packet_zero
  Step := P.Step
  step_packet := by
    intro i j hij ctx payload n
    exact P.step_packet_of_mem hij ctx payload n

abbrev AdditiveMeasure := (P.toRelational).AdditiveMeasure
abbrev AffineMeasure := (P.toRelational).AffineMeasure
abbrev TransparentMeasure := (P.toRelational).TransparentMeasure
abbrev GlobalOrientsCtx (m : P.T → Nat) : Prop := (P.toRelational).GlobalOrientsCtx m
abbrev HasNontrivialSCC : Prop := P.graph.HasNontrivialSCC
noncomputable abbrev findNontrivialSCCPair? : Option (ι × ι) := P.graph.findNontrivialSCCPair?

theorem no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  OperatorKO7.MutualDuplicationRelationalGraph.Preserving.Presentation.no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind M

theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    (M : P.AffineMeasure)
    (hdom :
      let hSCC := (P.graph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?).2 hfind
      let hij := OperatorKO7.FiniteGraphSCC.reachable_witnessSrc_witnessDst (R := P.Edge) hSCC
      let hji := OperatorKO7.FiniteGraphSCC.reachable_witnessDst_witnessSrc (R := P.Edge) hSCC
      let C := MutualDuplicationPacketGraph.GraphPacketSystem.ofRoundTrip
        (Sys := P.toRelational.toGraphSystem)
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne (R := P.Edge) hij
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst (R := P.Edge) hSCC))
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne (R := P.Edge) hji
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst (R := P.Edge) hSCC).symm)
      OperatorKO7.MutualDuplicationPayloadFlow.WrapperDominance
        (MutualDuplicationPacketGraph.GraphPacketSystem.CyclePath.AffineMeasure.toPacketModelMeasure
          M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : P.T, q ≤ M.eval t) :
    ¬ P.GlobalOrientsCtx M.eval :=
  OperatorKO7.MutualDuplicationRelationalGraph.Preserving.Presentation.no_global_orients_ctx_affine_of_wrapper_dominance_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind M hdom hunbounded

theorem no_global_orients_ctx_transparent_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    (M : P.TransparentMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  OperatorKO7.MutualDuplicationRelationalGraph.Preserving.Presentation.no_global_orients_ctx_transparent_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind M

theorem no_global_orients_ctx_of_scalar_projection_transparent_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : ι × ι, P.findNontrivialSCCPair? = some p)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (M : P.TransparentMeasure)
    (hπ : ∀ t : P.T, π (μ t) = M.eval t) :
    ¬ OperatorKO7.DependencyPairsFragment.GlobalOrients
      (OperatorKO7.MutualDuplicationPacketGraph.GraphPacketSystem.StepCtx P.toRelational.toGraphSystem)
      μ Q :=
  OperatorKO7.MutualDuplicationRelationalGraph.Preserving.Presentation.no_global_orients_ctx_of_scalar_projection_transparent_of_exists_findNontrivialSCCPair?
    (P := P.toRelational) hfind μ Q π hproj M hπ

end Presentation

end Preserving

end OperatorKO7.MutualDuplicationCallGraph
