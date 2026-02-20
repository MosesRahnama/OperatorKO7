/-!
GoodsteinCore - a tiny, standalone toy for Goodstein-style base-change shape.
This does NOT modify the KO7 kernel; it exists for examples and cross-links.
It models a pair (base, counter) and a single-step that bumps the base while
consuming one successor on the counter side.
-/

namespace OperatorKO7
namespace GoodsteinCore

/-- Base parameter (modeled minimally as a wrapped `Nat`). -/
inductive Base where
  | b : Nat → Base
deriving Repr, DecidableEq

/-- Unary naturals used as a toy counter for Goodstein-style steps. -/
inductive Cn where
  | z  : Cn
  | s  : Cn → Cn
deriving Repr, DecidableEq

/-- A Goodstein-state is a pair (base, counter). -/
structure St where
  base : Base
  cnt  : Cn
deriving Repr, DecidableEq

open Base Cn

/-- Goodstein-like one-step: bump base, drop one successor on the counter. -/
inductive Step : St → St → Prop where
  | base_change (b : Nat) (t : Cn) :
      Step ⟨.b b, .s t⟩ ⟨.b (b+1), t⟩

/-- Convenience lemma: the single `Step.base_change` rule is always available on `(.s t)` counters. -/
@[simp] theorem one_step (b : Nat) (t : Cn) :
    Step ⟨.b b, .s t⟩ ⟨.b (b+1), t⟩ := Step.base_change b t

end GoodsteinCore
end OperatorKO7
