import OperatorKO7.Meta.DependencyPairs_HeadView

/-!
# Finite Rule-Carrier View for Internal First-Order Engines

This module removes the remaining explicit rule-array layer for engines whose rules are
already organized as a finite carrier type. Instead of exposing an `Array Rule`, callers
can expose:

- a finite rule carrier,
- left-hand sides, and
- right-hand sides.

The canonical first-order and head-view extraction surfaces are then recovered by
enumerating that carrier.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Packaged first-order engine with a finite rule carrier instead of an explicit rule
array. -/
structure FiniteCarrierFirstOrderEngine (σ ν : Type) [DecidableEq σ] where
  Rule : Type
  ruleFintype : Fintype Rule
  ruleDecEq : DecidableEq Rule
  lhs : Rule → FOTerm σ ν
  rhs : Rule → FOTerm σ ν

namespace FiniteCarrierFirstOrderEngine

variable {σ ν : Type} [DecidableEq σ] (E : FiniteCarrierFirstOrderEngine σ ν)

/-- Enumerated rule array recovered from the finite rule carrier. -/
noncomputable def rules : Array E.Rule := by
  let _ : Fintype E.Rule := E.ruleFintype
  let _ : DecidableEq E.Rule := E.ruleDecEq
  exact (Finset.univ : Finset E.Rule).toList.toArray

/-- Canonical finite first-order engine recovered from the finite rule carrier. -/
noncomputable def toFiniteFirstOrderEngine : FiniteFirstOrderEngine σ ν where
  Rule := E.Rule
  rules := E.rules
  lhs := E.lhs
  rhs := E.rhs

/-- Smaller head-view engine recovered from the finite rule carrier. -/
noncomputable def toFiniteHeadRuleEngine : FiniteHeadRuleEngine σ :=
  FiniteHeadRuleEngine.ofFiniteFirstOrderEngine E.toFiniteFirstOrderEngine

/-- Defined heads recovered from the finite rule carrier. -/
noncomputable abbrev definedHeads : Finset σ :=
  E.toFiniteFirstOrderEngine.definedHeads

/-- Extracted nodes recovered from the finite rule carrier. -/
noncomputable abbrev extractedNodes : Array (ExtractedRuleFrontendNode E.Rule σ) :=
  E.toFiniteFirstOrderEngine.extractedNodes

/-- Extracted call graph recovered from the finite rule carrier. -/
noncomputable abbrev extractedCallGraph : FiniteExtractedCallGraph σ :=
  E.toFiniteFirstOrderEngine.extractedCallGraph

/-- Direct SCC search recovered from the finite rule carrier. -/
noncomputable abbrev findNontrivialSCCPair? :
    Option (E.extractedCallGraph.Node × E.extractedCallGraph.Node) :=
  E.toFiniteFirstOrderEngine.findNontrivialSCCPair?

/-- SCC existence predicate recovered from the finite rule carrier. -/
abbrev HasNontrivialSCC : Prop :=
  E.toFiniteFirstOrderEngine.HasNontrivialSCC

/-- Standard SCC witness recovered from the finite rule carrier. -/
noncomputable abbrev toSCCCycle (h : E.HasNontrivialSCC) :
    SCCCycle E.extractedCallGraph.Node :=
  E.toFiniteFirstOrderEngine.toSCCCycle h

end FiniteCarrierFirstOrderEngine

/-- Typeclass-level finite rule-carrier view for internal systems. -/
class HasFiniteCarrierFirstOrderView (ε σ ν : Type) [DecidableEq σ] where
  Rule : Type
  ruleFintype : Fintype Rule
  ruleDecEq : DecidableEq Rule
  lhs : ε → Rule → FOTerm σ ν
  rhs : ε → Rule → FOTerm σ ν

namespace HasFiniteCarrierFirstOrderView

variable {ε σ ν : Type} [DecidableEq σ] [H : HasFiniteCarrierFirstOrderView ε σ ν]

/-- Pack the typeclass-level finite rule-carrier view as the canonical carrier engine. -/
def toFiniteCarrierFirstOrderEngine (e : ε) : FiniteCarrierFirstOrderEngine σ ν where
  Rule := H.Rule
  ruleFintype := H.ruleFintype
  ruleDecEq := H.ruleDecEq
  lhs := H.lhs e
  rhs := H.rhs e

/-- Canonical finite first-order engine recovered directly from the carrier view. -/
noncomputable abbrev toFiniteFirstOrderEngine (e : ε) : FiniteFirstOrderEngine σ ν :=
  (toFiniteCarrierFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).toFiniteFirstOrderEngine

/-- Smaller head-view engine recovered directly from the carrier view. -/
noncomputable abbrev toFiniteHeadRuleEngine (e : ε) : FiniteHeadRuleEngine σ :=
  (toFiniteCarrierFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).toFiniteHeadRuleEngine

/-- Defined heads recovered directly from the carrier view. -/
noncomputable abbrev definedHeads (e : ε) : Finset σ :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).definedHeads

/-- Extracted nodes recovered directly from the carrier view. -/
noncomputable abbrev extractedNodes (e : ε) :
    Array (ExtractedRuleFrontendNode
      (HasFiniteCarrierFirstOrderView.Rule (ε := ε) (σ := σ) (ν := ν)) σ) :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).extractedNodes

/-- Extracted call graph recovered directly from the carrier view. -/
noncomputable abbrev extractedCallGraph (e : ε) : FiniteExtractedCallGraph σ :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).extractedCallGraph

/-- Direct SCC search recovered directly from the carrier view. -/
noncomputable abbrev findNontrivialSCCPair? (e : ε) :
    Option ((extractedCallGraph (ε := ε) (σ := σ) (ν := ν) e).Node ×
      (extractedCallGraph (ε := ε) (σ := σ) (ν := ν) e).Node) :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).findNontrivialSCCPair?

/-- SCC existence predicate recovered directly from the carrier view. -/
abbrev HasNontrivialSCC (e : ε) : Prop :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).HasNontrivialSCC

/-- Standard SCC witness recovered directly from the carrier view. -/
noncomputable abbrev toSCCCycle (e : ε)
    (h : (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).HasNontrivialSCC) :
    SCCCycle (extractedCallGraph (ε := ε) (σ := σ) (ν := ν) e).Node :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) e).toSCCCycle h

end HasFiniteCarrierFirstOrderView

end OperatorKO7.DependencyPairsFragment
