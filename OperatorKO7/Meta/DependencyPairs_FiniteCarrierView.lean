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

/-- Typeclass-level finite raw rule-carrier view for internal systems. -/
class HasFiniteCarrierRawFirstOrderView (ε σ ν : Type) [DecidableEq σ] where
  Rule : Type
  ruleFintype : Fintype Rule
  ruleDecEq : DecidableEq Rule
  Term : Type
  termView : HasFirstOrderTermView Term σ ν
  lhs : Rule → Term
  rhs : Rule → Term

/-- Any finite raw rule-carrier view induces the canonical finite carrier first-order view. -/
instance instHasFiniteCarrierFirstOrderViewOfRawCarrier
    (ε σ ν : Type) [DecidableEq σ] [H : HasFiniteCarrierRawFirstOrderView ε σ ν] :
    HasFiniteCarrierFirstOrderView ε σ ν where
  Rule := H.Rule
  ruleFintype := H.ruleFintype
  ruleDecEq := H.ruleDecEq
  lhs := by
    intro _ r
    let _ : HasFirstOrderTermView H.Term σ ν := H.termView
    exact HasFirstOrderTermView.toFOTerm (H.lhs r)
  rhs := by
    intro _ r
    let _ : HasFirstOrderTermView H.Term σ ν := H.termView
    exact HasFirstOrderTermView.toFOTerm (H.rhs r)

/-- Explicit adapter from a finite raw rule-carrier view to the smaller head-view engine
surface. -/
noncomputable def finiteHeadRuleViewOfFiniteCarrierRaw
    (ε σ ν : Type) [DecidableEq σ] [H : HasFiniteCarrierRawFirstOrderView ε σ ν] :
    HasFiniteHeadRuleView ε σ where
  Rule := H.Rule
  Term := H.Term
  termView := by
    let _ : HasFirstOrderTermView H.Term σ ν := H.termView
    exact headViewOfFirstOrderTermView H.Term σ ν
  rules := by
    intro _
    let _ : Fintype H.Rule := H.ruleFintype
    let _ : DecidableEq H.Rule := H.ruleDecEq
    exact (Finset.univ : Finset H.Rule).toList.toArray
  lhs := H.lhs
  rhs := H.rhs

/-- Packaged head-view engine with a finite rule carrier instead of an explicit rule array. -/
structure FiniteCarrierHeadEngine (σ : Type) [DecidableEq σ] where
  Rule : Type
  ruleFintype : Fintype Rule
  ruleDecEq : DecidableEq Rule
  Term : Type
  termView : HasCallHeadView Term σ
  lhs : Rule → Term
  rhs : Rule → Term

namespace FiniteCarrierHeadEngine

variable {σ : Type} [DecidableEq σ] (E : FiniteCarrierHeadEngine σ)

/-- Enumerated rule array recovered from the finite rule carrier. -/
noncomputable def rules : Array E.Rule := by
  let _ : Fintype E.Rule := E.ruleFintype
  let _ : DecidableEq E.Rule := E.ruleDecEq
  exact (Finset.univ : Finset E.Rule).toList.toArray

/-- Canonical finite head-view engine recovered from the finite rule carrier. -/
noncomputable def toFiniteHeadRuleEngine : FiniteHeadRuleEngine σ where
  Rule := E.Rule
  Term := E.Term
  termView := E.termView
  rules := E.rules
  lhs := E.lhs
  rhs := E.rhs

/-- Defined heads recovered from the finite head carrier. -/
noncomputable abbrev definedHeads : Finset σ :=
  E.toFiniteHeadRuleEngine.definedHeads

/-- Extracted nodes recovered from the finite head carrier. -/
noncomputable abbrev extractedNodes : Array (ExtractedHeadRuleNode E.Rule σ) :=
  E.toFiniteHeadRuleEngine.extractedNodes

/-- Extracted call graph recovered from the finite head carrier. -/
noncomputable abbrev extractedCallGraph : FiniteExtractedCallGraph σ :=
  E.toFiniteHeadRuleEngine.extractedCallGraph

end FiniteCarrierHeadEngine

/-- Typeclass-level finite head-view carrier for internal systems. -/
class HasFiniteCarrierHeadView (ε σ : Type) [DecidableEq σ] where
  Rule : Type
  ruleFintype : Fintype Rule
  ruleDecEq : DecidableEq Rule
  Term : Type
  termView : HasCallHeadView Term σ
  lhs : Rule → Term
  rhs : Rule → Term

namespace HasFiniteCarrierHeadView

variable {ε σ : Type} [DecidableEq σ] [H : HasFiniteCarrierHeadView ε σ]

/-- Package the typeclass-level finite head carrier as the canonical carrier engine. -/
def toFiniteCarrierHeadEngine (_e : ε) : FiniteCarrierHeadEngine σ where
  Rule := H.Rule
  ruleFintype := H.ruleFintype
  ruleDecEq := H.ruleDecEq
  Term := H.Term
  termView := H.termView
  lhs := H.lhs
  rhs := H.rhs

/-- Canonical finite head-view engine recovered directly from the carrier view. -/
noncomputable abbrev toFiniteHeadRuleEngine (e : ε) : FiniteHeadRuleEngine σ :=
  (toFiniteCarrierHeadEngine (ε := ε) (σ := σ) e).toFiniteHeadRuleEngine

/-- Defined heads recovered directly from the carrier view. -/
noncomputable abbrev definedHeads (e : ε) : Finset σ :=
  (toFiniteHeadRuleEngine (ε := ε) (σ := σ) e).definedHeads

/-- Extracted nodes recovered directly from the carrier view. -/
noncomputable abbrev extractedNodes (e : ε) :
    Array (ExtractedHeadRuleNode
      (HasFiniteCarrierHeadView.Rule (ε := ε) (σ := σ)) σ) :=
  (toFiniteHeadRuleEngine (ε := ε) (σ := σ) e).extractedNodes

/-- Extracted call graph recovered directly from the carrier view. -/
noncomputable abbrev extractedCallGraph (e : ε) : FiniteExtractedCallGraph σ :=
  (toFiniteHeadRuleEngine (ε := ε) (σ := σ) e).extractedCallGraph

end HasFiniteCarrierHeadView

/-- Explicit adapter from a finite raw rule-carrier view to the smaller finite head-carrier
view. -/
def finiteCarrierHeadViewOfFiniteCarrierRaw
    (ε σ ν : Type) [DecidableEq σ] [H : HasFiniteCarrierRawFirstOrderView ε σ ν] :
    HasFiniteCarrierHeadView ε σ where
  Rule := H.Rule
  ruleFintype := H.ruleFintype
  ruleDecEq := H.ruleDecEq
  Term := H.Term
  termView := by
    let _ : HasFirstOrderTermView H.Term σ ν := H.termView
    exact headViewOfFirstOrderTermView H.Term σ ν
  lhs := H.lhs
  rhs := H.rhs

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
