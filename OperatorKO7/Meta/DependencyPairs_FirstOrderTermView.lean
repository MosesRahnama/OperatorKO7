import OperatorKO7.Meta.DependencyPairs_FirstOrderView

/-!
# Raw-Term View for Internal First-Order Engines

This module removes one more explicit conversion layer for internal systems. An engine can
keep its own first-order term syntax and expose:

- a conversion to the canonical `FOTerm` syntax, and
- a finite raw rule view using that internal term type.

The generic `HasFiniteFirstOrderView` surface is then derived automatically.
-/

namespace OperatorKO7.DependencyPairsFragment

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
