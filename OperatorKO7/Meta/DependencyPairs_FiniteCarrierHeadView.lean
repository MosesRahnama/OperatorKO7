import OperatorKO7.Meta.DependencyPairs_FiniteCarrierRawView

/-!
# Finite Head/Call-Head Carrier View for Internal Engines

This module is the smallest finite dependency-pair frontend currently in the artifact.
It starts from:

- a finite rule carrier, and
- the minimal head / recursive-call-head term view.

No explicit rule array and no full `FOTerm` conversion are needed.
-/

namespace OperatorKO7.DependencyPairsFragment

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

end OperatorKO7.DependencyPairsFragment
