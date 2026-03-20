import OperatorKO7.Meta.BarrierWitness

/-!
# Textbook Step-Duplicating TRS Instance

This module instantiates the generic step-duplicating schema on the standard
first-order rule

`f(x, s(y)) -> g(x, f(x, y))`.

To fit the four-role schema, we use a dummy `base` argument that the recursor
projection ignores:

- `succ := s`
- `wrap := g`
- `recur b x y := f x y`

The resulting duplicating step is exactly the textbook rule above.
-/

namespace OperatorKO7.TextbookDupInstance

open OperatorKO7.StepDuplicating
open StepDuplicatingSchema

/-- Minimal syntax for the textbook duplicating rule `f(x, s(y)) -> g(x, f(x, y))`. -/
inductive TextbookTerm
  | zero
  | succ : TextbookTerm → TextbookTerm
  | g : TextbookTerm → TextbookTerm → TextbookTerm
  | f : TextbookTerm → TextbookTerm → TextbookTerm
  deriving DecidableEq, Repr

open TextbookTerm

/-- Schema view of the textbook system. The schema's dummy base parameter is ignored by `recur`,
so `recur b x y` is the textbook constructor `f x y`. -/
def textbookSchema : StepDuplicatingSchema where
  T := TextbookTerm
  base := zero
  succ := succ
  wrap := g
  recur := fun _ x y => f x y

/-- Root rewrite relation for the textbook duplicating rule. -/
inductive TextbookStep : TextbookTerm → TextbookTerm → Prop
  | dup (x y : TextbookTerm) : TextbookStep (f x (succ y)) (g x (f x y))

/-- The textbook TRS packaged as a step-duplicating system. -/
def textbookSystem : StepDuplicatingSystem where
  toStepDuplicatingSchema := textbookSchema
  Step := TextbookStep
  dup_step := by
    intro _ x y
    exact TextbookStep.dup x y

/-- Textbook additive barrier corollary. -/
theorem no_global_textbook_orientation_additive
    (M : AdditiveMeasure textbookSchema) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) := by
  exact no_global_orients_additive (Sys := textbookSystem) M

/-- Textbook affine barrier corollary under the usual unbounded-range hypothesis. -/
theorem no_global_textbook_orientation_affine_of_unbounded
    (M : AffineMeasure textbookSchema) (hunbounded : HasUnboundedRange M) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) := by
  exact no_global_orients_affine_of_unbounded (Sys := textbookSystem) M hunbounded

/-- Textbook compositional barrier corollary under base-level successor transparency. -/
theorem no_global_textbook_orientation_compositional_transparent_succ
    (M : CompositionalMeasure textbookSchema)
    (h_transparent : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) := by
  exact no_global_orients_compositional_transparent_succ (Sys := textbookSystem) M h_transparent

/-- The generic additive witness extractor specializes directly to the textbook system. -/
def textbook_additive_witness (M : AdditiveMeasure textbookSchema) :
    BarrierCertificate textbookSchema M.eval :=
  additive_witness M

/-- The generic compositional witness extractor specializes directly to the textbook system. -/
def textbook_compositional_witness
    (M : CompositionalMeasure textbookSchema)
    (h_transparent : M.c_succ M.c_base = M.c_base) :
    BarrierCertificate textbookSchema M.eval :=
  compositional_witness M h_transparent

/-- The affine witness extractor also specializes directly once a pump term is supplied. -/
def textbook_affine_witness
    (M : AffineMeasure textbookSchema)
    (s₀ : textbookSchema.T)
    (hs : M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) ≤ M.eval s₀) :
    BarrierCertificate textbookSchema M.eval :=
  affine_witness M s₀ hs

end OperatorKO7.TextbookDupInstance
