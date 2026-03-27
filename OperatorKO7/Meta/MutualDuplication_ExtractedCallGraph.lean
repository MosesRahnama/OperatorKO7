import OperatorKO7.Meta.DependencyPairs_ExtractedCallGraph
import OperatorKO7.Meta.MutualDuplication_CallGraph

/-!
# Extracted-Data Construction of SCC Barrier Systems

This module removes the finite-type packaging layer from the call-graph SCC transport
stack. Callers can start from raw extracted node data stored in an array, together with
the local delayed or preserving edge-realization theorem indexed by `Fin nodes.size`.

The module then builds the corresponding call-graph presentation automatically and
reexports the finite-SCC search-result contextual barrier wrappers.
-/

namespace OperatorKO7.MutualDuplicationExtractedCallGraph

open OperatorKO7.DependencyPairsFragment

namespace Delayed

/-- Delayed-duplication presentation over array-backed extracted call-graph data. -/
structure Presentation (κ : Type) [DecidableEq κ] where
  graph : FiniteExtractedCallGraph κ
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : graph.Node → T → T → T → T
  Step : T → T → Prop
  step_succ_of_mem :
    ∀ {i j : graph.Node}, graph.nodeKey j ∈ graph.succKeys i → ∀ b s n,
      Step (recur i b s (succ n)) (wrap s (recur j b s n))

namespace Presentation

variable {κ : Type} [DecidableEq κ] (P : Presentation κ)

/-- Convert the extracted-data delayed presentation to the existing call-graph system. -/
def toCallGraph :
    OperatorKO7.MutualDuplicationCallGraph.Delayed.Presentation P.graph.Node κ where
  graph := P.graph.toFiniteCallGraph
  T := P.T
  base := P.base
  succ := P.succ
  wrap := P.wrap
  recur := P.recur
  Step := P.Step
  step_succ_of_mem := P.step_succ_of_mem

abbrev AdditiveMeasure := (P.toCallGraph).AdditiveMeasure
abbrev AffineMeasure := (P.toCallGraph).AffineMeasure
abbrev CompositionalMeasure := (P.toCallGraph).CompositionalMeasure
abbrev GlobalOrientsCtx {α : Type} (m : P.T → α) (lt : α → α → Prop) : Prop :=
  (P.toCallGraph).GlobalOrientsCtx m lt
abbrev HasNontrivialSCC : Prop := P.graph.HasNontrivialSCC
noncomputable abbrev findNontrivialSCCPair? : Option (P.graph.Node × P.graph.Node) :=
  P.graph.findNontrivialSCCPair?

  theorem no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  OperatorKO7.MutualDuplicationCallGraph.Delayed.Presentation.no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind M

theorem no_global_orients_ctx_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    (M : P.AffineMeasure)
    (hunbounded :
      let hSCC := (P.graph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?).2 hfind
      let hij := OperatorKO7.FiniteGraphSCC.reachable_witnessSrc_witnessDst
        (R := P.graph.toFiniteCallGraph.Edge) hSCC
      let hji := OperatorKO7.FiniteGraphSCC.reachable_witnessDst_witnessSrc
        (R := P.graph.toFiniteCallGraph.Edge) hSCC
      let C := MutualDuplicationGraphCycle.GraphDupSystem.ofRoundTrip
        (Sys := P.toCallGraph.toRelational.toGraphSystem)
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne
          (R := P.graph.toFiniteCallGraph.Edge) hij
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst
            (R := P.graph.toFiniteCallGraph.Edge) hSCC))
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne
          (R := P.graph.toFiniteCallGraph.Edge) hji
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst
            (R := P.graph.toFiniteCallGraph.Edge) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
        (OperatorKO7.MutualDuplicationCycleFlow.AffineOps.toDupMeasure
          (MutualDuplicationGraphCycle.GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  OperatorKO7.MutualDuplicationCallGraph.Delayed.Presentation.no_global_orients_ctx_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind M hunbounded

theorem no_global_orients_ctx_compositional_transparent_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    (M : P.CompositionalMeasure)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ P.GlobalOrientsCtx M.eval (· < ·) :=
  OperatorKO7.MutualDuplicationCallGraph.Delayed.Presentation.no_global_orients_ctx_compositional_transparent_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind M htrans

theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (A :
      let hSCC := (P.graph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?).2 hfind
      let hij := OperatorKO7.FiniteGraphSCC.reachable_witnessSrc_witnessDst
        (R := P.graph.toFiniteCallGraph.Edge) hSCC
      let hji := OperatorKO7.FiniteGraphSCC.reachable_witnessDst_witnessSrc
        (R := P.graph.toFiniteCallGraph.Edge) hSCC
      let C := MutualDuplicationGraphCycle.GraphDupSystem.ofRoundTrip
        (Sys := P.toCallGraph.toRelational.toGraphSystem)
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne
          (R := P.graph.toFiniteCallGraph.Edge) hij
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst
            (R := P.graph.toFiniteCallGraph.Edge) hSCC))
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne
          (R := P.graph.toFiniteCallGraph.Edge) hji
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst
            (R := P.graph.toFiniteCallGraph.Edge) hSCC).symm)
      OperatorKO7.StepDuplicating.StepDuplicatingSchema.AffineMeasure
        (OperatorKO7.MutualDuplicationCycleFlow.toDupSchema
          (P.toCallGraph.toRelational.toGraphSystem.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : P.T, π (μ t) = A.eval t)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ OperatorKO7.DependencyPairsFragment.GlobalOrients
      (OperatorKO7.MutualDuplicationGraphCycle.GraphDupSystem.StepCtx
        P.toCallGraph.toRelational.toGraphSystem) μ Q :=
  OperatorKO7.MutualDuplicationCallGraph.Delayed.Presentation.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind μ Q π hproj A hπ hunbounded

end Presentation

end Delayed

namespace Preserving

/-- Preserving synchronized-packet presentation over array-backed extracted call-graph data. -/
structure Presentation (κ : Type) [DecidableEq κ] where
  graph : FiniteExtractedCallGraph κ
  T : Type
  empty : T
  wrap : T → T → T
  recur : graph.Node → T → T → T
  packet : graph.Node → Nat → T → T
  packet_zero : ∀ i p, packet i 0 p = empty
  Step : T → T → Prop
  step_packet_of_mem :
    ∀ {i j : graph.Node}, graph.nodeKey j ∈ graph.succKeys i → ∀ ctx payload n,
      Step (recur i ctx (packet i (n + 1) payload))
        (wrap payload (recur j ctx (packet j n payload)))

namespace Presentation

variable {κ : Type} [DecidableEq κ] (P : Presentation κ)

/-- Convert the extracted-data preserving presentation to the existing call-graph system. -/
def toCallGraph :
    OperatorKO7.MutualDuplicationCallGraph.Preserving.Presentation P.graph.Node κ where
  graph := P.graph.toFiniteCallGraph
  T := P.T
  empty := P.empty
  wrap := P.wrap
  recur := P.recur
  packet := P.packet
  packet_zero := P.packet_zero
  Step := P.Step
  step_packet_of_mem := P.step_packet_of_mem

abbrev AdditiveMeasure := (P.toCallGraph).AdditiveMeasure
abbrev AffineMeasure := (P.toCallGraph).AffineMeasure
abbrev TransparentMeasure := (P.toCallGraph).TransparentMeasure
abbrev GlobalOrientsCtx (m : P.T → Nat) : Prop := (P.toCallGraph).GlobalOrientsCtx m
abbrev HasNontrivialSCC : Prop := P.graph.HasNontrivialSCC
noncomputable abbrev findNontrivialSCCPair? : Option (P.graph.Node × P.graph.Node) :=
  P.graph.findNontrivialSCCPair?

  theorem no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    (M : P.AdditiveMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  OperatorKO7.MutualDuplicationCallGraph.Preserving.Presentation.no_global_orients_ctx_additive_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind M

theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    (M : P.AffineMeasure)
    (hdom :
      let hSCC := (P.graph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?).2 hfind
      let hij := OperatorKO7.FiniteGraphSCC.reachable_witnessSrc_witnessDst
        (R := P.graph.toFiniteCallGraph.Edge) hSCC
      let hji := OperatorKO7.FiniteGraphSCC.reachable_witnessDst_witnessSrc
        (R := P.graph.toFiniteCallGraph.Edge) hSCC
      let C := MutualDuplicationPacketGraph.GraphPacketSystem.ofRoundTrip
        (Sys := P.toCallGraph.toRelational.toGraphSystem)
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne
          (R := P.graph.toFiniteCallGraph.Edge) hij
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst
            (R := P.graph.toFiniteCallGraph.Edge) hSCC))
        (OperatorKO7.FiniteGraphReachability.transGen_of_reachable_of_ne
          (R := P.graph.toFiniteCallGraph.Edge) hji
          (OperatorKO7.FiniteGraphSCC.witnessSrc_ne_witnessDst
            (R := P.graph.toFiniteCallGraph.Edge) hSCC).symm)
      OperatorKO7.MutualDuplicationPayloadFlow.WrapperDominance
        (MutualDuplicationPacketGraph.GraphPacketSystem.CyclePath.AffineMeasure.toPacketModelMeasure
          M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : P.T, q ≤ M.eval t) :
    ¬ P.GlobalOrientsCtx M.eval :=
  OperatorKO7.MutualDuplicationCallGraph.Preserving.Presentation.no_global_orients_ctx_affine_of_wrapper_dominance_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind M hdom hunbounded

  theorem no_global_orients_ctx_transparent_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    (M : P.TransparentMeasure) :
    ¬ P.GlobalOrientsCtx M.eval :=
  OperatorKO7.MutualDuplicationCallGraph.Preserving.Presentation.no_global_orients_ctx_transparent_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind M

theorem no_global_orients_ctx_of_scalar_projection_transparent_of_exists_findNontrivialSCCPair?
    (hfind : ∃ p : P.graph.Node × P.graph.Node, P.findNontrivialSCCPair? = some p)
    {α : Type} (μ : P.T → α) (Q : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, Q u v → π u < π v)
    (M : P.TransparentMeasure)
    (hπ : ∀ t : P.T, π (μ t) = M.eval t) :
    ¬ OperatorKO7.DependencyPairsFragment.GlobalOrients
      (OperatorKO7.MutualDuplicationPacketGraph.GraphPacketSystem.StepCtx
        P.toCallGraph.toRelational.toGraphSystem) μ Q :=
  OperatorKO7.MutualDuplicationCallGraph.Preserving.Presentation.no_global_orients_ctx_of_scalar_projection_transparent_of_exists_findNontrivialSCCPair?
    (P := P.toCallGraph) hfind μ Q π hproj M hπ

end Presentation

end Preserving

end OperatorKO7.MutualDuplicationExtractedCallGraph
