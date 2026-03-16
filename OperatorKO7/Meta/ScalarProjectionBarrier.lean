import OperatorKO7.Meta.MatrixBarrier2
import OperatorKO7.Meta.MatrixBarrierFunctional

/-!
# Scalar Projection Barrier

Many of the vector-valued barriers in the artifact reduce to the same template:

- a direct orienter produces values in some richer codomain `α`,
- a fixed scalar projection `π : α → Nat` extracts the tracked primary quantity,
- every permitted strict decrease in the codomain forces strict decrease of that scalar,
- the projected scalar family is already blocked by one of the scalar barrier theorems.

This module packages that template once. It does not replace the stronger bespoke
theorems such as the lexicographic primary barrier, but it subsumes a large part of
the projection-based matrix stack: tracked componentwise pairs, weighted functional
matrix measures, and balanced mixed-coordinate sum barriers.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Generic scalar-projection lift: if every `R`-decrease forces strict decrease of a
projected scalar, and that scalar decrease is already impossible on the duplicating step,
then `R` itself cannot orient the duplicating step uniformly. -/
theorem no_orients_dup_step_of_scalar_projection
    {S : StepDuplicatingSchema} {α : Type} (μ : S.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (hscalar :
      ¬ (∀ (b s n : S.T),
        π (μ (S.wrap s (S.recur b s n))) < π (μ (S.recur b s (S.succ n))))) :
    ¬ (∀ (b s n : S.T), R (μ (S.wrap s (S.recur b s n))) (μ (S.recur b s (S.succ n)))) := by
  intro h
  apply hscalar
  intro b s n
  exact hproj (h b s n)

/-- The same projection principle lifts to global root orientation. -/
theorem no_global_orients_of_scalar_projection
    {Sys : StepDuplicatingSystem} {α : Type}
    (μ : Sys.toStepDuplicatingSchema.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (hscalar :
      ¬ (∀ (b s n : Sys.toStepDuplicatingSchema.T),
        π (μ (Sys.wrap s (Sys.recur b s n))) < π (μ (Sys.recur b s (Sys.succ n))))) :
    ¬ GlobalOrients Sys μ R := by
  intro h
  apply hscalar
  intro b s n
  exact hproj (h (Sys.dup_step b s n))

/-- The tracked first-component pair barrier is an instance of the scalar-projection
principle via the first coordinate. -/
theorem no_matrix2_orients_dup_step_of_componentwise_pump_via_projection
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (hunbounded : HasUnboundedRange1 M) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_orients_dup_step_of_scalar_projection (μ := M.eval) (R := PairLt) (π := Prod.fst)
  · intro u v h
    exact h.1
  · exact no_affine_orients_dup_step_of_unbounded (S := S) M.fstAffine hunbounded

/-- Any weighted functional matrix orienter is blocked once its chosen scalar projection
falls under the scalar affine barrier. This re-derives `MatrixBarrierFunctional` from the
generic projection theorem. -/
theorem no_matrixFunctional_orients_dup_step_of_componentwise_pump_via_projection
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d)
    (hunbounded : HasUnboundedWeightedRange M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_orients_dup_step_of_scalar_projection
    (μ := M.eval) (R := VecLt) (π := weightedSum M.weight)
  · intro u v h
    exact weightedSum_lt_of_vecLt M.h_weight_support h
  · have hunbounded' : HasUnboundedRange M.projectedAffine := by
      intro k
      rcases hunbounded k with ⟨t, ht⟩
      exact ⟨t, ht⟩
    exact no_affine_orients_dup_step_of_unbounded (S := S) M.projectedAffine hunbounded'

/-- The balanced mixed-coordinate pair barrier is also an instance of the scalar-projection
principle via the coordinate sum. -/
theorem no_matrixMix2_orients_dup_step_of_sum_pump_via_projection
    {S : StepDuplicatingSchema} (M : MatrixMix2Measure S)
    (hunbounded : HasUnboundedRangeSum M) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_orients_dup_step_of_scalar_projection
    (μ := M.eval) (R := PairLt) (π := vecSum)
  · intro u v h
    exact vecSum_lt_of_pairLt h
  · have hunbounded' : HasUnboundedRange M.sumAffine := by
      intro k
      rcases hunbounded k with ⟨t, ht⟩
      exact ⟨t, ht⟩
    exact no_affine_orients_dup_step_of_unbounded (S := S) M.sumAffine hunbounded'

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
