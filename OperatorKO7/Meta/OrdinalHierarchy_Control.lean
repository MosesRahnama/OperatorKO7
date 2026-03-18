import OperatorKO7.Meta.OrdinalHierarchy

/-!
# Exact controlled descent for ordinal notations

This module packages the generic theorem behind the strict S142 roadmap:
an exact fundamental-sequence descent chain has length bounded by the
corresponding `cichon` value.

The relation here is intentionally exact. It does not yet allow arbitrary
smaller descendants beneath the chosen fundamental-sequence approximation.
That stronger abstraction is the remaining proof-engineering gap for a full
Moser--Weiermann-style extraction on the KO7 relations.
-/

open ONote

namespace OperatorKO7.OrdinalHierarchy

/-- Exact controlled descent with an explicit endpoint. -/
inductive ExactControlledPow : ONote → Nat → Nat → ONote → Nat → Prop
  | refl (o : ONote) (k : Nat) : ExactControlledPow o k 0 o k
  | succ {o a r : ONote} {k k' n : Nat}
      (hfs : fundamentalSequence o = Sum.inl (some a))
      (hrest : ExactControlledPow a (k + 1) n r k') :
      ExactControlledPow o k (n + 1) r k'
  | limit {o r : ONote} {f : Nat → ONote} {k k' n : Nat}
      (hfs : fundamentalSequence o = Sum.inr f)
      (hrest : ExactControlledPow (f k) (k + 1) n r k') :
      ExactControlledPow o k (n + 1) r k'

/-- Length-only projection of the endpoint-tracking relation. -/
abbrev ExactControlledPath (o : ONote) (k n : Nat) : Prop :=
  ∃ r k', ExactControlledPow o k n r k'

/-- Generic Cichon bound for exact fundamental-sequence descent. -/
theorem exactControlledPow_length_le_cichon :
    ∀ {o r : ONote} {k k' n : Nat}, ExactControlledPow o k n r k' → n ≤ cichon o k
  | _, _, _, _, _, ExactControlledPow.refl _ _ => by
      simp
  | _, _, _, _, _, ExactControlledPow.succ hfs hrest => by
      have ih := exactControlledPow_length_le_cichon hrest
      rw [cichon_succ _ hfs]
      exact Nat.succ_le_succ ih
  | _, _, _, _, _, ExactControlledPow.limit hfs hrest => by
      have ih := exactControlledPow_length_le_cichon hrest
      rw [cichon_limit _ hfs]
      exact Nat.succ_le_succ ih

theorem exactControlledPath_length_le_cichon
    {o : ONote} {k n : Nat} (h : ExactControlledPath o k n) :
    n ≤ cichon o k := by
  rcases h with ⟨r, k', hp⟩
  exact exactControlledPow_length_le_cichon hp

end OperatorKO7.OrdinalHierarchy
