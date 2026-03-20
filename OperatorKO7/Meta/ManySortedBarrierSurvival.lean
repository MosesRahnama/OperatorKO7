import OperatorKO7.Meta.TypedBarrierSurvival

/-!
# Many-Sorted Barrier Survival

This module repackages `TypedBarrierSurvival` as a many-sorted first-order
presentation. We do **not** formalize the full general Aoto-Yamada translation
theorem here. Instead we record the specialized consequence needed for KO7's
recursor fragment:

- the already-formalized sort-indexed first-order syntax can be read directly as
  a many-sorted TRS presentation;
- under that reading, the additive barrier and the affine barrier with a step-pump
  survive unchanged.

The result is therefore a theorem-backed many-sorted extension of the existing
typed fragment, while staying honest about the scope of the formalization.
-/

namespace OperatorKO7.ManySortedBarrierSurvival

open OperatorKO7.TypedBarrierSurvival

/-- Sorts of the specialized many-sorted first-order recursor fragment. -/
abbrev MSort := Ty

/-- Terms of the specialized many-sorted first-order recursor fragment. -/
abbrev Term := TypedBarrierSurvival.Term

/-- Many-sorted step-sort iterator. -/
abbrev stepIter := TypedBarrierSurvival.stepIter

/-- Additive constructor-local measures on the many-sorted presentation. -/
abbrev AdditiveMeasure := TypedBarrierSurvival.AdditiveMeasure

/-- Affine constructor-local measures on the many-sorted presentation. -/
abbrev AffineMeasure := TypedBarrierSurvival.AffineMeasure

/-- Explicit many-sorted step-pump hypothesis. -/
abbrev HasManySortedStepPump := TypedBarrierSurvival.HasTypedStepPump

/-- The additive barrier survives in the many-sorted first-order presentation. -/
theorem no_additive_orients_manySorted_recSucc (M : AdditiveMeasure) :
    ¬ (∀ (b : Term .res) (s : Term .step) (n : Term .cnt),
      M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
        M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n))) :=
  no_additive_orients_typed_recSucc M

/-- The affine barrier also survives once the many-sorted step sort still admits
an unbounded closed pump family. -/
theorem no_affine_orients_manySorted_recSucc_of_stepPump (M : AffineMeasure)
    (hpump : HasManySortedStepPump M) :
    ¬ (∀ (b : Term .res) (s : Term .step) (n : Term .cnt),
      M.evalRes (TypedBarrierSurvival.Term.wrap s (TypedBarrierSurvival.Term.recur b s n)) <
        M.evalRes (TypedBarrierSurvival.Term.recur b s (TypedBarrierSurvival.Term.succ n))) :=
  no_affine_orients_typed_recSucc_of_stepPump M hpump

end OperatorKO7.ManySortedBarrierSurvival
