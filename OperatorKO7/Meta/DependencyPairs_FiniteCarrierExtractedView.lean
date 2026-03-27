import OperatorKO7.Meta.DependencyPairs_FiniteCarrierHeadView

/-!
# Finite Extracted-Data Carrier View for Internal Engines

This module is the bottom of the current dependency-pair frontend stack. It starts from:

- a finite rule carrier,
- one already-extracted node key per rule, and
- one already-extracted successor-key set per rule.

There is no explicit rule array and no term interface at all. The array-backed extracted
call graph and the finite-SCC search / contradiction surface are recovered directly from
that data.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Packaged extracted-data engine with a finite rule carrier. -/
structure FiniteCarrierExtractedEngine (κ : Type) [DecidableEq κ] where
  Rule : Type
  ruleFintype : Fintype Rule
  ruleDecEq : DecidableEq Rule
  nodeKey? : Rule → Option κ
  succKeys : Rule → Finset κ

namespace FiniteCarrierExtractedEngine

variable {κ : Type} [DecidableEq κ] (E : FiniteCarrierExtractedEngine κ)

/-- Enumerated extracted node records recovered from the finite rule carrier. -/
noncomputable def extractedNodes : Array (ExtractedCallNode κ) := by
  let _ : Fintype E.Rule := E.ruleFintype
  let _ : DecidableEq E.Rule := E.ruleDecEq
  exact ((Finset.univ : Finset E.Rule).toList.filterMap fun r =>
    match E.nodeKey? r with
    | none => none
    | some k => some ({ nodeKey := k, succKeys := E.succKeys r } : ExtractedCallNode κ)).toArray

/-- Canonical extracted call graph recovered from the finite carrier data. -/
noncomputable def toFiniteExtractedCallGraph : FiniteExtractedCallGraph κ where
  nodes := E.extractedNodes

/-- Direct SCC search recovered from the finite extracted carrier. -/
noncomputable abbrev findNontrivialSCCPair? :
    Option (E.toFiniteExtractedCallGraph.Node × E.toFiniteExtractedCallGraph.Node) :=
  E.toFiniteExtractedCallGraph.findNontrivialSCCPair?

/-- SCC existence predicate recovered from the finite extracted carrier. -/
abbrev HasNontrivialSCC : Prop :=
  E.toFiniteExtractedCallGraph.HasNontrivialSCC

/-- Standard SCC witness recovered from the finite extracted carrier. -/
noncomputable abbrev toSCCCycle (h : E.HasNontrivialSCC) :
    SCCCycle E.toFiniteExtractedCallGraph.Node :=
  E.toFiniteExtractedCallGraph.toSCCCycle h

end FiniteCarrierExtractedEngine

/-- Typeclass-level finite extracted-data carrier for internal systems. -/
class HasFiniteCarrierExtractedView (ε κ : Type) [DecidableEq κ] where
  Rule : Type
  ruleFintype : Fintype Rule
  ruleDecEq : DecidableEq Rule
  nodeKey? : ε → Rule → Option κ
  succKeys : ε → Rule → Finset κ

namespace HasFiniteCarrierExtractedView

variable {ε κ : Type} [DecidableEq κ] [H : HasFiniteCarrierExtractedView ε κ]

/-- Package the typeclass-level extracted carrier as the canonical extracted engine. -/
def toFiniteCarrierExtractedEngine (e : ε) : FiniteCarrierExtractedEngine κ where
  Rule := H.Rule
  ruleFintype := H.ruleFintype
  ruleDecEq := H.ruleDecEq
  nodeKey? := H.nodeKey? e
  succKeys := H.succKeys e

/-- Extracted node records recovered directly from the extracted carrier view. -/
noncomputable abbrev extractedNodes (e : ε) : Array (ExtractedCallNode κ) :=
  (toFiniteCarrierExtractedEngine (ε := ε) (κ := κ) e).extractedNodes

/-- Extracted call graph recovered directly from the extracted carrier view. -/
noncomputable abbrev extractedCallGraph (e : ε) : FiniteExtractedCallGraph κ :=
  (toFiniteCarrierExtractedEngine (ε := ε) (κ := κ) e).toFiniteExtractedCallGraph

/-- Direct SCC search recovered directly from the extracted carrier view. -/
noncomputable abbrev findNontrivialSCCPair? (e : ε) :
    Option ((extractedCallGraph (ε := ε) (κ := κ) e).Node ×
      (extractedCallGraph (ε := ε) (κ := κ) e).Node) :=
  (toFiniteCarrierExtractedEngine (ε := ε) (κ := κ) e).findNontrivialSCCPair?

/-- SCC existence predicate recovered directly from the extracted carrier view. -/
abbrev HasNontrivialSCC (e : ε) : Prop :=
  (toFiniteCarrierExtractedEngine (ε := ε) (κ := κ) e).HasNontrivialSCC

end HasFiniteCarrierExtractedView

/-- Explicit adapter from a finite head-carrier view to the extracted-data carrier view. -/
def finiteCarrierExtractedViewOfHeadCarrier
    (ε κ : Type) [DecidableEq κ] [H : HasFiniteCarrierHeadView ε κ] :
    HasFiniteCarrierExtractedView ε κ where
  Rule := H.Rule
  ruleFintype := H.ruleFintype
  ruleDecEq := H.ruleDecEq
  nodeKey? := by
    intro _ r
    let _ : HasCallHeadView H.Term κ := H.termView
    exact HasCallHeadView.rootHead? (H.lhs r)
  succKeys := by
    intro _ r
    let _ : HasCallHeadView H.Term κ := H.termView
    exact HasCallHeadView.callHeads (H.rhs r)

end OperatorKO7.DependencyPairsFragment
