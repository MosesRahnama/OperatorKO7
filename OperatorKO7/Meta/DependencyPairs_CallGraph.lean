import OperatorKO7.Meta.DependencyPairs_FiniteGraph

/-!
# Finite Call-Graph Presentation for Dependency Pairs

This module removes one more layer of manual graph packaging for finite dependency-pair
arguments. Instead of supplying a binary pair relation directly, a caller can work with a
more concrete extracted call-graph presentation:

- a finite type of dependency-pair nodes,
- a finite key type for marked call heads,
- one key attached to each node, and
- the finite set of successor keys extracted from each node.

The binary edge relation is then built automatically by matching successor keys against the
keys of target nodes.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Finite extracted call-graph presentation for dependency-pair nodes. -/
structure FiniteCallGraph (ι κ : Type) [Fintype ι] [DecidableEq ι] [DecidableEq κ] where
  nodeKey : ι → κ
  succKeys : ι → Finset κ

namespace FiniteCallGraph

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ] (G : FiniteCallGraph ι κ)

/-- The induced dependency-pair edge relation: a target node is reachable when its key
appears in the extracted successor-key set of the source node. -/
def Edge (i j : ι) : Prop :=
  G.nodeKey j ∈ G.succKeys i

instance instDecidableRelEdge : DecidableRel G.Edge := by
  intro i j
  unfold Edge
  infer_instance

/-- The induced finite dependency-pair graph. -/
def toFiniteDPGraph : FiniteDPGraph ι where
  Pair := G.Edge
  decPair := instDecidableRelEdge (G := G)

@[simp] theorem edge_iff_mem_succKeys {i j : ι} :
    G.Edge i j ↔ G.nodeKey j ∈ G.succKeys i := by
  rfl

/-- Finite search for a nontrivial SCC in the induced dependency-pair graph. -/
noncomputable def findNontrivialSCCPair? : Option (ι × ι) :=
  G.toFiniteDPGraph.findNontrivialSCCPair?

/-- Finite-SCC existence for the induced dependency-pair graph. -/
abbrev HasNontrivialSCC : Prop :=
  G.toFiniteDPGraph.HasNontrivialSCC

theorem hasNontrivialSCC_iff_exists_findNontrivialSCCPair? :
    G.HasNontrivialSCC ↔ ∃ p : ι × ι, G.findNontrivialSCCPair? = some p := by
  simpa [FiniteCallGraph.findNontrivialSCCPair?, FiniteCallGraph.HasNontrivialSCC] using
    (FiniteDPGraph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair? (G := G.toFiniteDPGraph))

theorem hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some {p : ι × ι}
    (h : G.findNontrivialSCCPair? = some p) :
    G.HasNontrivialSCC := by
  simpa [FiniteCallGraph.findNontrivialSCCPair?, FiniteCallGraph.HasNontrivialSCC] using
    (FiniteDPGraph.hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some
      (G := G.toFiniteDPGraph) h)

theorem findNontrivialSCCPair?_spec {p : ι × ι}
    (h : G.findNontrivialSCCPair? = some p) :
    OperatorKO7.FiniteGraphSCC.NontrivialRoundTrip G.Edge p.1 p.2 := by
  simpa [FiniteCallGraph.findNontrivialSCCPair?] using
    (FiniteDPGraph.findNontrivialSCCPair?_spec (G := G.toFiniteDPGraph) h)

/-- Standard SCC witness for the induced finite dependency-pair graph. -/
noncomputable def toSCCCycle (h : G.HasNontrivialSCC) : SCCCycle ι :=
  G.toFiniteDPGraph.toSCCCycle h

theorem not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
    {m : ι → Nat} {p : ι × ι}
    (hfind : G.findNontrivialSCCPair? = some p)
    (hge : m p.1 ≤ m p.2) :
    ¬ GlobalOrients G.Edge m (· < ·) := by
  simpa [FiniteCallGraph.findNontrivialSCCPair?, FiniteCallGraph.Edge] using
    (FiniteDPGraph.not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
      (G := G.toFiniteDPGraph) hfind hge)

theorem not_globalOrients_of_source_le_target_of_hasNontrivialSCC
    {m : ι → Nat}
    (h : G.HasNontrivialSCC)
    (hge : m (G.toSCCCycle h).source ≤ m (G.toSCCCycle h).target) :
    ¬ GlobalOrients G.Edge m (· < ·) := by
  simpa [FiniteCallGraph.Edge] using
    (FiniteDPGraph.not_globalOrients_of_source_le_target_of_hasNontrivialSCC
      (G := G.toFiniteDPGraph) h hge)

end FiniteCallGraph

end OperatorKO7.DependencyPairsFragment
