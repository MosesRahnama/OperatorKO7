import OperatorKO7.Meta.DependencyPairs_FirstOrderFrontend

/-!
# Engine-Level Frontend for Generic First-Order Extraction

This module removes one more packaging layer from the generic first-order extraction stack.
Instead of passing

- a finite rule array,
- a left-hand side extractor, and
- a right-hand side extractor

at each use site, callers can package an internal first-order TRS / DP engine once as a
single structure. The same extracted-node, call-graph, SCC-search, and contradiction
surface is then reexported from that engine object directly.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Minimal finite first-order rule engine packaged as one object. -/
structure FiniteFirstOrderEngine (σ ν : Type) [DecidableEq σ] where
  Rule : Type
  rules : Array Rule
  lhs : Rule → FOTerm σ ν
  rhs : Rule → FOTerm σ ν

namespace FiniteFirstOrderEngine

variable {σ ν : Type} [DecidableEq σ] (E : FiniteFirstOrderEngine σ ν)

/-- Defined heads of the packaged engine. -/
abbrev definedHeads : Finset σ :=
  foDefinedHeadsOf E.rules E.lhs

/-- Extracted dependency-pair nodes of the packaged engine. -/
abbrev extractedNodes : Array (ExtractedRuleFrontendNode E.Rule σ) :=
  extractRuleFrontendNodes E.rules E.lhs E.rhs

/-- Array-backed extracted call graph of the packaged engine. -/
abbrev extractedCallGraph : FiniteExtractedCallGraph σ :=
  foExtractedCallGraphOf E.rules E.lhs E.rhs

/-- Direct SCC search on the packaged engine. -/
noncomputable abbrev findNontrivialSCCPair? :
    Option (E.extractedCallGraph.Node × E.extractedCallGraph.Node) :=
  findNontrivialSCCPair?Of E.rules E.lhs E.rhs

/-- SCC existence predicate on the packaged engine. -/
abbrev HasNontrivialSCC : Prop :=
  HasNontrivialSCCOf E.rules E.lhs E.rhs

theorem hasNontrivialSCC_iff_exists_findNontrivialSCCPair? :
    E.HasNontrivialSCC ↔
      ∃ p : E.extractedCallGraph.Node × E.extractedCallGraph.Node,
        E.findNontrivialSCCPair? = some p := by
  simpa [FiniteFirstOrderEngine.HasNontrivialSCC, FiniteFirstOrderEngine.findNontrivialSCCPair?,
    FiniteFirstOrderEngine.extractedCallGraph] using
    (hasNontrivialSCCOf_iff_exists_findNontrivialSCCPair? E.rules E.lhs E.rhs)

theorem hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some
    {p : E.extractedCallGraph.Node × E.extractedCallGraph.Node}
    (h : E.findNontrivialSCCPair? = some p) :
    E.HasNontrivialSCC := by
  simpa [FiniteFirstOrderEngine.HasNontrivialSCC, FiniteFirstOrderEngine.findNontrivialSCCPair?,
    FiniteFirstOrderEngine.extractedCallGraph] using
    (hasNontrivialSCCOf_of_findNontrivialSCCPair?_eq_some E.rules E.lhs E.rhs h)

/-- Standard SCC witness recovered directly from the packaged engine. -/
noncomputable abbrev toSCCCycle (h : E.HasNontrivialSCC) :
    SCCCycle E.extractedCallGraph.Node :=
  toSCCCycleOf E.rules E.lhs E.rhs h

theorem not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
    {m : E.extractedCallGraph.Node → Nat}
    {p : E.extractedCallGraph.Node × E.extractedCallGraph.Node}
    (hfind : E.findNontrivialSCCPair? = some p)
    (hge : m p.1 ≤ m p.2) :
    ¬ GlobalOrients E.extractedCallGraph.toFiniteCallGraph.Edge m (· < ·) := by
  simpa [FiniteFirstOrderEngine.findNontrivialSCCPair?, FiniteFirstOrderEngine.extractedCallGraph]
    using
      (not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?Of
        E.rules E.lhs E.rhs hfind hge)

theorem not_globalOrients_of_source_le_target_of_hasNontrivialSCC
    {m : E.extractedCallGraph.Node → Nat}
    (h : E.HasNontrivialSCC)
    (hge : m (E.toSCCCycle h).source ≤ m (E.toSCCCycle h).target) :
    ¬ GlobalOrients E.extractedCallGraph.toFiniteCallGraph.Edge m (· < ·) := by
  simpa [FiniteFirstOrderEngine.HasNontrivialSCC, FiniteFirstOrderEngine.toSCCCycle,
    FiniteFirstOrderEngine.extractedCallGraph] using
    (not_globalOrients_of_source_le_target_of_hasNontrivialSCCOf
      E.rules E.lhs E.rhs h hge)

end FiniteFirstOrderEngine

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

/-- Conversion from an internal first-order term syntax to the canonical `FOTerm` view. -/
class HasFirstOrderTermView (τ σ ν : Type) where
  toFOTerm : τ → FOTerm σ ν

/-- Identity term-view instance for the canonical `FOTerm` syntax itself. -/
instance instHasFirstOrderTermViewFOTerm (σ ν : Type) :
    HasFirstOrderTermView (FOTerm σ ν) σ ν where
  toFOTerm := id

/-- Raw finite first-order engine view using an internal term syntax stored in the class. -/
class HasFiniteRawFirstOrderView (ε σ ν : Type) [DecidableEq σ] where
  Rule : Type
  Term : Type
  termView : HasFirstOrderTermView Term σ ν
  rules : ε → Array Rule
  lhs : Rule → Term
  rhs : Rule → Term

/-- Any raw first-order engine view induces the canonical `FOTerm`-based view automatically. -/
instance instHasFiniteFirstOrderViewOfRaw
    (ε σ ν : Type) [DecidableEq σ] [H : HasFiniteRawFirstOrderView ε σ ν] :
    HasFiniteFirstOrderView ε σ ν where
  Rule := H.Rule
  rules := H.rules
  lhs := by
    intro r
    let _ := H.termView
    exact HasFirstOrderTermView.toFOTerm (H.lhs r)
  rhs := by
    intro r
    let _ := H.termView
    exact HasFirstOrderTermView.toFOTerm (H.rhs r)

end OperatorKO7.DependencyPairsFragment
