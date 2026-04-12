import OperatorKO7.Meta.LinearRec_Ablation
import OperatorKO7.Meta.TypedBarrierSurvival
import OperatorKO7.Meta.SharingBarrierLift

/-!
# Boundary Factorization

This module packages the three ablation-style facts that explain why the KO7
orientation barrier sits where it does:

* removing step duplication dissolves the direct barrier;
* simple typing by itself does not dissolve the barrier;
* sharing-aware semantics can dissolve the tree-specific obstruction.

Together these support the paper-facing claim that the load-bearing structural
feature is step-payload duplication under tree semantics, not recursion in
general and not merely the absence of simple typing.
-/

namespace OperatorKO7.BarrierFactorization

open OperatorKO7
open Trace

/-- Removing step duplication dissolves the direct barrier on the linearized
recursor variant. -/
theorem recursion_alone_not_sufficient_for_barrier :
    ∃ μ : Trace → Nat,
      ∀ {a b : Trace}, LinearStep a b → μ b < μ a := by
  refine ⟨simpleSize, ?_⟩
  intro a b h
  exact simpleSize_orients_linearStep h

/-- Simple typing is not, by itself, an escape mechanism for the additive
direct-measure barrier. -/
theorem simple_typing_not_escape_mechanism_additive :
    ∀ M : TypedBarrierSurvival.AdditiveMeasure,
      ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
           (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
           (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
        M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
          M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n))) := by
  intro M
  exact TypedBarrierSurvival.no_additive_orients_typed_recSucc M

/-- The affine typed fragment also preserves the barrier once the step sort
admits an unbounded typed pump family. -/
theorem simple_typing_not_escape_mechanism_affine :
    ∀ M : TypedBarrierSurvival.AffineMeasure,
      TypedBarrierSurvival.HasTypedStepPump M →
        ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
             (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
             (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
          M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
            M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n))) := by
  intro M hpump
  exact TypedBarrierSurvival.no_affine_orients_typed_recSucc_of_stepPump M hpump

/-- Sharing-aware semantics can dissolve the tree-specific direct barrier. -/
theorem sharing_can_break_tree_barrier :
    ∀ b s n : SharingBarrierLift.SharedTerm,
      SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.shareApp s
        (SharingBarrierLift.SharedTerm.recur b s n)) <
      SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.recur b s
        (SharingBarrierLift.SharedTerm.succ n)) := by
  intro b s n
  exact SharingBarrierLift.sharing_breaks_tree_barrier b s n

/-- Packaged cross-paper factorization theorem: the KO7 boundary is explained
by step-payload duplication under tree semantics. -/
theorem ko7_barrier_is_duplication :
    (∃ μ : Trace → Nat,
        ∀ {a b : Trace}, LinearStep a b → μ b < μ a) ∧
      (∀ M : TypedBarrierSurvival.AdditiveMeasure,
        ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
             (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
             (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
          M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
            M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n)))) ∧
      (∀ M : TypedBarrierSurvival.AffineMeasure,
        TypedBarrierSurvival.HasTypedStepPump M →
          ¬ (∀ (b : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.res)
               (s : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.step)
               (n : TypedBarrierSurvival.Term TypedBarrierSurvival.Ty.cnt),
            M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
              M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n)))) ∧
      (∀ b s n : SharingBarrierLift.SharedTerm,
        SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.shareApp s
          (SharingBarrierLift.SharedTerm.recur b s n)) <
        SharingBarrierLift.sharedCounter (SharingBarrierLift.SharedTerm.recur b s
          (SharingBarrierLift.SharedTerm.succ n))) := by
  exact ⟨recursion_alone_not_sufficient_for_barrier,
    simple_typing_not_escape_mechanism_additive,
    simple_typing_not_escape_mechanism_affine,
    sharing_can_break_tree_barrier⟩

end OperatorKO7.BarrierFactorization
