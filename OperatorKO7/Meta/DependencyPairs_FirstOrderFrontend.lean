import OperatorKO7.Meta.DependencyPairs_FirstOrderExtraction

/-!
# Rule-Record Frontend for Generic First-Order Extraction

This module removes one more packaging layer from the generic first-order dependency-pair
extraction stack. Instead of first converting an engine-specific rule record to the
uniform `FORule` structure, callers can provide:

- a finite array of rule records,
- a left-hand side extractor into `FOTerm`, and
- a right-hand side extractor into `FOTerm`.

The defined-head computation, extracted call-head node array, and array-backed call graph
are then built directly from that rule-record frontend.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Extracted dependency-pair node data for an arbitrary rule record over first-order
left- and right-hand side extractors. -/
structure ExtractedRuleFrontendNode (ρ σ : Type) [DecidableEq σ] where
  rule : ρ
  nodeKey : σ
  succKeys : Finset σ

/-- Defined heads of a finite rule-record frontend. -/
def foDefinedHeadsOf {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) : Finset σ :=
  rules.foldl
    (fun acc r =>
      match FOTerm.head? (lhs r) with
      | some f => insert f acc
      | none => acc)
    ∅

/-- Extract one dependency-pair node from an arbitrary rule record, when the left-hand
side has a function head. -/
def extractRuleFrontendNode? {ρ σ ν : Type} [DecidableEq σ]
    (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν)
    (defined : Finset σ) (r : ρ) : Option (ExtractedRuleFrontendNode ρ σ) :=
  match FOTerm.head? (lhs r) with
  | none => none
  | some f =>
      some
        { rule := r
          nodeKey := f
          succKeys := (FOTerm.allHeads (rhs r)).filter (· ∈ defined) }

/-- Extracted dependency-pair call-head nodes for a finite rule-record frontend. -/
def extractRuleFrontendNodes {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν) :
    Array (ExtractedRuleFrontendNode ρ σ) :=
  let defined := foDefinedHeadsOf rules lhs
  rules.filterMap (extractRuleFrontendNode? lhs rhs defined)

/-- Array-backed extracted call graph induced directly from a rule-record frontend. -/
def foExtractedCallGraphOf {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν) :
    FiniteExtractedCallGraph σ :=
  FiniteExtractedCallGraph.ofArrayMap
    (nodes := extractRuleFrontendNodes rules lhs rhs)
    (nodeKey := ExtractedRuleFrontendNode.nodeKey)
    (succKeys := ExtractedRuleFrontendNode.succKeys)

/-- Direct SCC search surface from a rule-record frontend. -/
noncomputable abbrev findNontrivialSCCPair?Of {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν) :
    Option ((foExtractedCallGraphOf rules lhs rhs).Node × (foExtractedCallGraphOf rules lhs rhs).Node) :=
  (foExtractedCallGraphOf rules lhs rhs).findNontrivialSCCPair?

/-- SCC existence predicate from a rule-record frontend. -/
abbrev HasNontrivialSCCOf {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν) : Prop :=
  (foExtractedCallGraphOf rules lhs rhs).HasNontrivialSCC

theorem hasNontrivialSCCOf_iff_exists_findNontrivialSCCPair? {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν) :
    HasNontrivialSCCOf rules lhs rhs ↔
      ∃ p : (foExtractedCallGraphOf rules lhs rhs).Node × (foExtractedCallGraphOf rules lhs rhs).Node,
        findNontrivialSCCPair?Of rules lhs rhs = some p := by
  simpa [HasNontrivialSCCOf, findNontrivialSCCPair?Of] using
    (FiniteExtractedCallGraph.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?
      (G := foExtractedCallGraphOf rules lhs rhs))

theorem hasNontrivialSCCOf_of_findNontrivialSCCPair?_eq_some {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν)
    {p : (foExtractedCallGraphOf rules lhs rhs).Node × (foExtractedCallGraphOf rules lhs rhs).Node}
    (h : findNontrivialSCCPair?Of rules lhs rhs = some p) :
    HasNontrivialSCCOf rules lhs rhs := by
  simpa [HasNontrivialSCCOf, findNontrivialSCCPair?Of] using
    (FiniteExtractedCallGraph.hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some
      (G := foExtractedCallGraphOf rules lhs rhs) h)

/-- Standard SCC witness recovered directly from a rule-record frontend. -/
noncomputable abbrev toSCCCycleOf {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν)
    (h : HasNontrivialSCCOf rules lhs rhs) :
    SCCCycle (foExtractedCallGraphOf rules lhs rhs).Node :=
  (foExtractedCallGraphOf rules lhs rhs).toSCCCycle h

theorem not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?Of
    {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν)
    {m : (foExtractedCallGraphOf rules lhs rhs).Node → Nat}
    {p : (foExtractedCallGraphOf rules lhs rhs).Node × (foExtractedCallGraphOf rules lhs rhs).Node}
    (hfind : findNontrivialSCCPair?Of rules lhs rhs = some p)
    (hge : m p.1 ≤ m p.2) :
    ¬ GlobalOrients (foExtractedCallGraphOf rules lhs rhs).toFiniteCallGraph.Edge m (· < ·) := by
  simpa [findNontrivialSCCPair?Of] using
    (FiniteExtractedCallGraph.not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
      (G := foExtractedCallGraphOf rules lhs rhs) hfind hge)

theorem not_globalOrients_of_source_le_target_of_hasNontrivialSCCOf
    {ρ σ ν : Type} [DecidableEq σ]
    (rules : Array ρ) (lhs : ρ → FOTerm σ ν) (rhs : ρ → FOTerm σ ν)
    {m : (foExtractedCallGraphOf rules lhs rhs).Node → Nat}
    (h : HasNontrivialSCCOf rules lhs rhs)
    (hge : m (toSCCCycleOf rules lhs rhs h).source ≤ m (toSCCCycleOf rules lhs rhs h).target) :
    ¬ GlobalOrients (foExtractedCallGraphOf rules lhs rhs).toFiniteCallGraph.Edge m (· < ·) := by
  simpa [HasNontrivialSCCOf, toSCCCycleOf] using
    (FiniteExtractedCallGraph.not_globalOrients_of_source_le_target_of_hasNontrivialSCC
      (G := foExtractedCallGraphOf rules lhs rhs) h hge)

theorem foDefinedHeadsOf_eq_foDefinedHeads {σ ν : Type} [DecidableEq σ]
    (rules : Array (FORule σ ν)) :
    foDefinedHeadsOf rules FORule.lhs = foDefinedHeads rules := by
  rfl

private def packExtractedFORuleNode {σ ν : Type} [DecidableEq σ] :
    ExtractedFORuleNode σ ν → ExtractedRuleFrontendNode (FORule σ ν) σ
  | n => {
      rule := n.rule
      nodeKey := n.nodeKey
      succKeys := n.succKeys
    }

private theorem extractRuleFrontendNode?_eq_map_extractFORuleNode? {σ ν : Type}
    [DecidableEq σ] (defined : Finset σ) (r : FORule σ ν) :
    extractRuleFrontendNode? FORule.lhs FORule.rhs defined r =
      (extractFORuleNode? defined r).map (packExtractedFORuleNode (σ := σ) (ν := ν)) := by
  cases h : FOTerm.head? (FORule.lhs r) <;>
    simp [extractRuleFrontendNode?, extractFORuleNode?, FORule.lhsHead?, h,
      packExtractedFORuleNode]

private theorem extractRuleFrontendNode?_eq_map_extractFORuleNode {σ ν : Type}
    [DecidableEq σ] (defined : Finset σ) :
    extractRuleFrontendNode? FORule.lhs FORule.rhs defined =
      fun r =>
        (extractFORuleNode? defined r).map (packExtractedFORuleNode (σ := σ) (ν := ν)) := by
  funext r
  exact extractRuleFrontendNode?_eq_map_extractFORuleNode? defined r

theorem extractRuleFrontendNodes_eq_extractFORuleNodes {σ ν : Type} [DecidableEq σ]
    (rules : Array (FORule σ ν)) :
    extractRuleFrontendNodes rules FORule.lhs FORule.rhs =
      (extractFORuleNodes rules).map (packExtractedFORuleNode (σ := σ) (ν := ν)) := by
  have hlist :
      (extractRuleFrontendNodes rules FORule.lhs FORule.rhs).toList =
        ((extractFORuleNodes rules).map (packExtractedFORuleNode (σ := σ) (ν := ν))).toList := by
    simpa [extractRuleFrontendNodes, extractFORuleNodes, foDefinedHeadsOf_eq_foDefinedHeads,
      packExtractedFORuleNode, Array.toList_filterMap, Array.toList_map,
      extractRuleFrontendNode?_eq_map_extractFORuleNode] using
      (List.map_filterMap (f := extractFORuleNode? (foDefinedHeads rules))
        (g := packExtractedFORuleNode (σ := σ) (ν := ν)) (l := rules.toList)).symm
  have hmap :
      (List.map (packExtractedFORuleNode (σ := σ) (ν := ν))
        (extractFORuleNodes rules).toList).toArray =
        (extractFORuleNodes rules).map (packExtractedFORuleNode (σ := σ) (ν := ν)) := by
    simpa [Array.toList_map] using
      (Array.toArray_toList
        (xs := (extractFORuleNodes rules).map (packExtractedFORuleNode (σ := σ) (ν := ν))))
  calc
    extractRuleFrontendNodes rules FORule.lhs FORule.rhs =
        (List.map (packExtractedFORuleNode (σ := σ) (ν := ν))
          (extractFORuleNodes rules).toList).toArray := by
            simpa [Array.toArray_toList, Array.toList_map, packExtractedFORuleNode] using
              congrArg List.toArray hlist
    _ =
        (extractFORuleNodes rules).map (packExtractedFORuleNode (σ := σ) (ν := ν)) := hmap

end OperatorKO7.DependencyPairsFragment
