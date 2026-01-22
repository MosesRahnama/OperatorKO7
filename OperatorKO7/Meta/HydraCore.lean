/-!
HydraCore - a tiny, standalone toy hydra relation to serve as a minimal
"hydra core" rule set for demonstrations. This does NOT change the KO7 kernel
and is only for examples/tests of duplication-style steps.

This captures the duplication flavor: chopping a head duplicates a subtree.
We keep it intentionally small and independent of KO7.
-/

namespace OperatorKO7
namespace HydraCore

/-- A minimal hydra-as-binary-tree datatype. `head` is a leaf; `node l r` has two sub-hydras. -/
inductive Hydra where
  | head : Hydra
  | node : Hydra → Hydra → Hydra
deriving Repr, DecidableEq

open Hydra

/-- One-step toy hydra rule: cutting a head on one side duplicates the other side. -/
inductive Step : Hydra → Hydra → Prop where
  | chop_left  (h : Hydra) : Step (node head h) (node h h)
  | chop_right (h : Hydra) : Step (node h head) (node h h)

/-- Convenience lemma: left chop duplicates the right subtree. -/
@[simp] theorem dup_left (h : Hydra) : Step (node head h) (node h h) := Step.chop_left h
/-- Convenience lemma: right chop duplicates the left subtree. -/
@[simp] theorem dup_right (h : Hydra) : Step (node h head) (node h h) := Step.chop_right h

/-- Example: a single chop duplicates the non-head subtree. -/
example (h : Hydra) : ∃ h', Step (node head h) h' := ⟨node h h, Step.chop_left h⟩

end HydraCore
end OperatorKO7
