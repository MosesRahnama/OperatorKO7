import OperatorKO7.Meta.DependencyPairs_FirstOrderEngine

/-!
# Typeclass View for Internal First-Order Engines

This module removes the remaining explicit engine-construction step for internal systems
whose rule representation is fixed at the type level. A type can expose a finite
first-order view through one instance, and the generic dependency-pair extraction / SCC
surface is then available directly from values of that type.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Typeclass view exposing a finite first-order rule engine from an internal system type. -/
class HasFiniteFirstOrderView (ε σ ν : Type) [DecidableEq σ] where
  Rule : Type
  rules : ε → Array Rule
  lhs : Rule → FOTerm σ ν
  rhs : Rule → FOTerm σ ν

namespace HasFiniteFirstOrderView

variable {ε σ ν : Type} [DecidableEq σ] [HasFiniteFirstOrderView ε σ ν]

/-- Canonical packaged engine induced by the typeclass view. -/
def toFiniteFirstOrderEngine (E : ε) : FiniteFirstOrderEngine σ ν where
  Rule := HasFiniteFirstOrderView.Rule (ε := ε) (σ := σ) (ν := ν)
  rules := HasFiniteFirstOrderView.rules (ε := ε) (σ := σ) (ν := ν) E
  lhs := HasFiniteFirstOrderView.lhs (ε := ε) (σ := σ) (ν := ν)
  rhs := HasFiniteFirstOrderView.rhs (ε := ε) (σ := σ) (ν := ν)

/-- Defined heads exposed directly from a viewed engine value. -/
abbrev definedHeads (E : ε) : Finset σ :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) E).definedHeads

/-- Extracted nodes exposed directly from a viewed engine value. -/
abbrev extractedNodes (E : ε) :
    Array (ExtractedRuleFrontendNode (HasFiniteFirstOrderView.Rule (ε := ε) (σ := σ) (ν := ν)) σ) :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) E).extractedNodes

/-- Extracted call graph exposed directly from a viewed engine value. -/
abbrev extractedCallGraph (E : ε) : FiniteExtractedCallGraph σ :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) E).extractedCallGraph

/-- Direct SCC search exposed from a viewed engine value. -/
noncomputable abbrev findNontrivialSCCPair? (E : ε) :
    Option ((extractedCallGraph (ε := ε) (σ := σ) (ν := ν) E).Node ×
      (extractedCallGraph (ε := ε) (σ := σ) (ν := ν) E).Node) :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) E).findNontrivialSCCPair?

/-- SCC existence predicate exposed from a viewed engine value. -/
abbrev HasNontrivialSCC (E : ε) : Prop :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) E).HasNontrivialSCC

/-- Standard SCC witness exposed from a viewed engine value. -/
noncomputable abbrev toSCCCycle (E : ε)
    (h : (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) E).HasNontrivialSCC) :
    SCCCycle (extractedCallGraph (ε := ε) (σ := σ) (ν := ν) E).Node :=
  (toFiniteFirstOrderEngine (ε := ε) (σ := σ) (ν := ν) E).toSCCCycle h

end HasFiniteFirstOrderView

end OperatorKO7.DependencyPairsFragment
