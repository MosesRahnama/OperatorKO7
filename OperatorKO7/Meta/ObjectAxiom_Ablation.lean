import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.LinearRec_Ablation
import OperatorKO7.Meta.PolyInterpretation_FullStep

/-!
# Object-Axiom Ablation via Directed Wrapper Collapse

This module tests a bounded first-order surrogate for the paper's "no object-level axioms"
condition.  We extend KO7 by one directed collapse rule

`app t t → t`

and check what changes.

Outcome:

- the extra rule itself is harmless and is oriented by simple additive size and by the
  nonlinear full-step witness `W`;
- the extended root relation is still terminating, witnessed by `W`;
- the existing barrier classes still fail, because the duplicating step `rec_succ` remains
  present unchanged inside the extended relation.

So this directed first-order collapse does **not** by itself dissolve the barrier.
-/

namespace OperatorKO7.ObjectAxiomAblation

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.PolyInterpretation

/-- KO7 extended by one directed collapse rule `app t t → t`. -/
inductive StepCollapse : Trace → Trace → Prop
| ofStep : ∀ {a b : Trace}, Step a b → StepCollapse a b
| R_app_collapse : ∀ t, StepCollapse (app t t) t

/-- The extended system still contains the same step-duplicating schema instance. -/
def stepCollapseSystem : StepDuplicatingSchema.StepDuplicatingSystem where
  toStepDuplicatingSchema := ko7Schema
  Step := StepCollapse
  dup_step := by
    intro b s n
    exact StepCollapse.ofStep (Step.R_rec_succ b s n)

/-- The added collapse rule strictly decreases the additive node-count measure. -/
theorem simpleSize_orients_app_collapse (t : Trace) :
    simpleSize t < simpleSize (app t t) := by
  simp [simpleSize]

/-- The nonlinear polynomial witness `W` also strictly orients the added collapse rule. -/
theorem W_orients_app_collapse (t : Trace) :
    W t < W (app t t) := by
  simp [W]
  have ht := W_pos t
  omega

/-- Every step of the extended relation strictly decreases `W`. -/
theorem W_orients_stepCollapse : ∀ {a b : Trace}, StepCollapse a b → W b < W a
  | _, _, StepCollapse.ofStep h => W_orients_step h
  | _, _, StepCollapse.R_app_collapse t => W_orients_app_collapse t

/-- Root-step termination of the extended relation: the added collapse rule introduces
no loops and does not break the existing nonlinear full-step proof. -/
theorem wf_StepCollapseRev : WellFounded (fun a b : Trace => StepCollapse b a) := by
  exact wellFounded_of_W_decreases (R := StepCollapse) (fun {_ _} h => W_orients_stepCollapse h)

/-- The additive barrier persists under the directed collapse extension. -/
theorem no_global_stepCollapse_orientation_additive
    (M : StepDuplicatingSchema.AdditiveMeasure ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients stepCollapseSystem M.eval (· < ·) := by
  exact StepDuplicatingSchema.no_global_orients_additive (Sys := stepCollapseSystem) M

/-- The transparent-compositional barrier persists under the directed collapse extension. -/
theorem no_global_stepCollapse_orientation_compositional_transparent
    (CM : StepDuplicatingSchema.CompositionalMeasure ko7Schema)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    ¬ StepDuplicatingSchema.GlobalOrients stepCollapseSystem CM.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_compositional_transparent_succ
      (Sys := stepCollapseSystem) CM h_transparent

/-- The affine barrier also persists under the directed collapse extension. -/
theorem no_global_stepCollapse_orientation_affine_of_unbounded
    (M : StepDuplicatingSchema.AffineMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange M) :
    ¬ StepDuplicatingSchema.GlobalOrients stepCollapseSystem M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_affine_of_unbounded
      (Sys := stepCollapseSystem) M hunbounded

/-- The directed collapse rule changes the system but does not dissolve the existing
global barrier classes: the same duplicating-step obstruction survives unchanged. -/
theorem collapse_surrogate_preserves_direct_barrier :
    (∀ M : StepDuplicatingSchema.AdditiveMeasure ko7Schema,
      ¬ StepDuplicatingSchema.GlobalOrients stepCollapseSystem M.eval (· < ·)) ∧
    (∀ CM : StepDuplicatingSchema.CompositionalMeasure ko7Schema,
      CM.c_succ CM.c_base = CM.c_base →
      ¬ StepDuplicatingSchema.GlobalOrients stepCollapseSystem CM.eval (· < ·)) := by
  refine ⟨?_, ?_⟩
  · intro M
    exact no_global_stepCollapse_orientation_additive M
  · intro CM htrans
    exact no_global_stepCollapse_orientation_compositional_transparent CM htrans

end OperatorKO7.ObjectAxiomAblation
