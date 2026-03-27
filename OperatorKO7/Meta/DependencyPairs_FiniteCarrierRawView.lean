import OperatorKO7.Meta.DependencyPairs_FiniteCarrierView

/-!
# Finite Raw Rule-Carrier View for Internal Engines

This module combines two reductions at once:

- rules are given by a finite carrier type rather than an explicit array, and
- terms can remain in an internal syntax rather than being exposed directly as `FOTerm`.

From that smaller interface, the finite carrier first-order surface is recovered
automatically, and the smaller head-view surface can be recovered through an explicit
adapter.
-/

namespace OperatorKO7.DependencyPairsFragment

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

end OperatorKO7.DependencyPairsFragment
