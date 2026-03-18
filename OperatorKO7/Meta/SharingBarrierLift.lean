import Mathlib.Order.WellFounded

/-!
# Sharing-aware lift of the duplication story

This file formalizes a minimal sharing-aware surrogate of the duplicating recursor.
The point is not to rebuild graph rewriting. It is to make one structural fact from
the paper precise inside Lean:

- the tree/no-sharing assumption is load-bearing,
- once the step payload is shared rather than copied syntactically, the direct
  additive obstruction can disappear.

The surrogate keeps only the successor/recursor shape and a shared application node.
-/

namespace OperatorKO7.SharingBarrierLift

/-- Minimal sharing-aware syntax. -/
inductive SharedTerm : Type
| base : SharedTerm
| succ : SharedTerm → SharedTerm
| shareApp : SharedTerm → SharedTerm → SharedTerm
| recur : SharedTerm → SharedTerm → SharedTerm → SharedTerm
deriving DecidableEq, Repr

open SharedTerm

/-- Sharing-aware recursive step: the payload is referenced once under `shareApp`
rather than counted as two tree copies. -/
inductive SharedStep : SharedTerm → SharedTerm → Prop
| rec_succ : ∀ b s n, SharedStep (recur b s (succ n)) (shareApp s (recur b s n))

/-- A simple counter depth for the shared recursor. The shared application counts only the
recursive continuation, making the load-bearing role of tree semantics explicit. -/
@[simp] def sharedCounter : SharedTerm → Nat
| base => 0
| succ t => sharedCounter t + 1
| shareApp _ r => sharedCounter r
| recur _ _ n => sharedCounter n

/-- The sharing-aware direct counter strictly decreases on the duplicating step. -/
theorem sharedCounter_orients_step :
    ∀ {a b : SharedTerm}, SharedStep a b → sharedCounter b < sharedCounter a
  | _, _, SharedStep.rec_succ _ _ _ => by
      simp [sharedCounter]

/-- Reverse sharing-aware step relation is well-founded. -/
theorem wf_SharedStepRev : WellFounded (fun a b : SharedTerm => SharedStep b a) := by
  have hsub : Subrelation (fun a b : SharedTerm => SharedStep b a)
      (fun x y : SharedTerm => sharedCounter x < sharedCounter y) := by
    intro x y hxy
    exact sharedCounter_orients_step hxy
  exact Subrelation.wf hsub (InvImage.wf (f := sharedCounter) Nat.lt_wfRel.wf)

/-- A simple additive-style direct counter succeeds in the sharing-aware surrogate.
This is the formal witness that the tree/no-sharing assumption in the paper is genuine. -/
theorem sharing_breaks_tree_barrier :
    ∀ b s n : SharedTerm,
      sharedCounter (shareApp s (recur b s n)) <
        sharedCounter (recur b s (succ n)) := by
  intro b s n
  simp

end OperatorKO7.SharingBarrierLift
