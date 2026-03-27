import OperatorKO7.Meta.DependencyPairs_CallGraph

/-!
# Array-Backed Extracted Call Graphs

This module removes one more packaging layer from the finite dependency-pair graph
interface. Instead of supplying:

- a finite node type,
- a key function on nodes, and
- a successor-key function on nodes,

callers can start from raw extracted node data stored in an array. The node type is then
generated automatically as `Fin nodes.size`, and the existing finite call-graph / SCC
search surface is reexported on top of that presentation.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Raw extracted dependency-pair node data. -/
structure ExtractedCallNode (κ : Type) [DecidableEq κ] where
  nodeKey : κ
  succKeys : Finset κ

/-- Array-backed extracted call graph. -/
structure FiniteExtractedCallGraph (κ : Type) [DecidableEq κ] where
  nodes : Array (ExtractedCallNode κ)

namespace FiniteExtractedCallGraph

variable {κ : Type} [DecidableEq κ] (G : FiniteExtractedCallGraph κ)

/-- Build an extracted call graph from arbitrary node records via field extractors. -/
def ofArrayMap {σ : Type} (nodes : Array σ) (nodeKey : σ → κ) (succKeys : σ → Finset κ) :
    FiniteExtractedCallGraph κ where
  nodes := nodes.map fun s => { nodeKey := nodeKey s, succKeys := succKeys s }

/-- Automatically generated finite node type for the extracted call graph. -/
abbrev Node : Type := Fin G.nodes.size

instance instFintypeNode : Fintype G.Node := inferInstance
instance instDecidableEqNode : DecidableEq G.Node := inferInstance

/-- Raw node record at a generated node index. -/
abbrev nodeData (i : G.Node) : ExtractedCallNode κ := G.nodes[i]

/-- Extracted key attached to a generated node. -/
abbrev nodeKey (i : G.Node) : κ := (G.nodeData i).nodeKey

/-- Extracted successor-key set attached to a generated node. -/
abbrev succKeys (i : G.Node) : Finset κ := (G.nodeData i).succKeys

/-- Canonical finite call-graph view of the extracted data. -/
def toFiniteCallGraph : FiniteCallGraph G.Node κ where
  nodeKey := G.nodeKey
  succKeys := G.succKeys

/-- Search for a nontrivial SCC in the extracted call graph. -/
noncomputable abbrev findNontrivialSCCPair? : Option (G.Node × G.Node) :=
  G.toFiniteCallGraph.findNontrivialSCCPair?

/-- SCC existence for the extracted call graph. -/
abbrev HasNontrivialSCC : Prop := G.toFiniteCallGraph.HasNontrivialSCC

theorem hasNontrivialSCC_iff_exists_findNontrivialSCCPair? :
    G.HasNontrivialSCC ↔ ∃ p : G.Node × G.Node, G.findNontrivialSCCPair? = some p := by
  simpa [FiniteExtractedCallGraph.findNontrivialSCCPair?,
    FiniteExtractedCallGraph.HasNontrivialSCC] using
    (FiniteCallGraph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?
      (G := G.toFiniteCallGraph))

theorem hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some {p : G.Node × G.Node}
    (h : G.findNontrivialSCCPair? = some p) :
    G.HasNontrivialSCC := by
  simpa [FiniteExtractedCallGraph.findNontrivialSCCPair?,
    FiniteExtractedCallGraph.HasNontrivialSCC] using
    (FiniteCallGraph.hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some
      (G := G.toFiniteCallGraph) h)

theorem findNontrivialSCCPair?_spec {p : G.Node × G.Node}
    (h : G.findNontrivialSCCPair? = some p) :
    OperatorKO7.FiniteGraphSCC.NontrivialRoundTrip G.toFiniteCallGraph.Edge p.1 p.2 := by
  simpa [FiniteExtractedCallGraph.findNontrivialSCCPair?] using
    (FiniteCallGraph.findNontrivialSCCPair?_spec (G := G.toFiniteCallGraph) h)

/-- Standard SCC witness for the extracted call graph. -/
noncomputable abbrev toSCCCycle (h : G.HasNontrivialSCC) :
    SCCCycle G.Node :=
  G.toFiniteCallGraph.toSCCCycle h

theorem not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
    {m : G.Node → Nat} {p : G.Node × G.Node}
    (hfind : G.findNontrivialSCCPair? = some p)
    (hge : m p.1 ≤ m p.2) :
    ¬ GlobalOrients G.toFiniteCallGraph.Edge m (· < ·) := by
  simpa [FiniteExtractedCallGraph.findNontrivialSCCPair?] using
    (FiniteCallGraph.not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
      (G := G.toFiniteCallGraph) hfind hge)

theorem not_globalOrients_of_source_le_target_of_hasNontrivialSCC
    {m : G.Node → Nat}
    (h : G.HasNontrivialSCC)
    (hge : m (G.toSCCCycle h).source ≤ m (G.toSCCCycle h).target) :
    ¬ GlobalOrients G.toFiniteCallGraph.Edge m (· < ·) := by
  simpa using
    (FiniteCallGraph.not_globalOrients_of_source_le_target_of_hasNontrivialSCC
      (G := G.toFiniteCallGraph) h hge)

end FiniteExtractedCallGraph

end OperatorKO7.DependencyPairsFragment
