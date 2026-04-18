import OperatorKO7.Meta.BarrierWitness
import OperatorKO7.Meta.PumpedBarrierClasses_Schema

/-!
# Extended computable barrier-witness extractors

This module extends `BarrierWitness.lean` with additional constructive extractors for:

* restricted quadratic counter measures with an internal pump,
* max-plus measures with an internal pump,
* weighted functional matrix measures whose chosen scalar projection has an internal
  affine pump.

The new extractors stay off the root import surface for now so they can be integrated
later without disturbing the public library entrypoint.
-/

namespace OperatorKO7.StepDuplicating
open StepDuplicatingSchema

namespace StepDuplicatingSchema

/-- A bundled counterexample for relations not necessarily valued in `Nat`. -/
structure RelationBarrierCertificate
    (S : StepDuplicatingSchema) (α : Type) (eval : S.T → α) (lt : α → α → Prop) where
  b : S.T
  s : S.T
  n : S.T
  fails : ¬ lt (eval (S.wrap s (S.recur b s n))) (eval (S.recur b s (S.succ n)))

/-- Automatic witness extractor for the strengthened affine pumped subclass. -/
def affine_with_pump_witness {S : StepDuplicatingSchema}
    (M : AffineMeasureWithPump S) :
    BarrierCertificate S M.eval := by
  classical
  let t :=
    M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  if hsucc : 1 ≤ M.succ_bias ∧ 1 ≤ M.succ_scale then
    exact
      affine_witness M.toAffineMeasure (succIter S t)
        (by
          simpa [t] using
            eval_succIter_ge M.toAffineMeasure hsucc.1 hsucc.2 t)
  else
    have hwrap : 1 ≤ M.wrap_const + M.wrap_right * M.c_base := by
      rcases M.has_pump with hsucc' | hwrap
      · exact False.elim (hsucc hsucc')
      · exact hwrap
    exact
      affine_witness M.toAffineMeasure (wrapIter S t)
        (by
          simpa [t] using
            eval_wrapIter_ge_affine M.toAffineMeasure hwrap t)

@[simp] private def quadraticSuccBase {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) : Nat :=
  M.succ_bias + M.succ_scale * M.c_base

@[simp] private def quadraticThreshold {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) : Nat :=
  M.recur_counter * quadraticSuccBase M +
    M.recur_quad * quadraticSuccBase M * quadraticSuccBase M

private theorem quadratic_failure_at_base
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) (s : S.T)
    (hs : quadraticThreshold M ≤ M.eval s) :
    ¬ (M.eval (S.wrap s (S.recur S.base s S.base)) <
        M.eval (S.recur S.base s (S.succ S.base))) := by
  intro h
  let Sval := M.eval s
  let A := M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval
  let B := M.recur_counter * M.c_base
  let Q := M.recur_quad * M.c_base * M.c_base
  let T := quadraticThreshold M
  have hspec' :
      M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) < A + T := by
    simpa [Sval, A, B, Q, T, quadraticSuccBase, quadraticThreshold,
      M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hsT : T ≤ Sval := by
    simpa [T, Sval, quadraticThreshold] using hs
  have hS : Sval ≤ M.wrap_left * Sval := by
    calc
      Sval = 1 * Sval := by simp
      _ ≤ M.wrap_left * Sval := Nat.mul_le_mul_right Sval M.h_wrap_left_pos
  have hABQ : A + B + Q ≤ M.wrap_right * (A + B + Q) := by
    calc
      A + B + Q = 1 * (A + B + Q) := by simp
      _ ≤ M.wrap_right * (A + B + Q) := Nat.mul_le_mul_right (A + B + Q) M.h_wrap_right_pos
  have h_rhs_to_aS : A + T ≤ A + Sval := Nat.add_le_add_left hsT A
  have h_aS_to_aWS : A + Sval ≤ A + M.wrap_left * Sval := Nat.add_le_add_left hS A
  have h_aWS_to_sum : A + M.wrap_left * Sval ≤ A + M.wrap_left * Sval + (B + Q) := by
    exact Nat.le_add_right _ _
  have h_sum_to_wsum :
      A + M.wrap_left * Sval + (B + Q) ≤
        M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
    have hABQ' :
        M.wrap_left * Sval + (A + B + Q) ≤
          M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
      exact Nat.add_le_add_left hABQ (M.wrap_left * Sval)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hABQ'
  have h_with_const :
      M.wrap_left * Sval + M.wrap_right * (A + B + Q) ≤
        M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
    calc
      M.wrap_left * Sval + M.wrap_right * (A + B + Q)
          ≤ M.wrap_const + (M.wrap_left * Sval + M.wrap_right * (A + B + Q)) := by
            exact Nat.le_add_left _ _
      _ = M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
            simp [Nat.add_assoc]
  have hge :
      A + T ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B + Q) := by
    exact le_trans h_rhs_to_aS <|
      le_trans h_aS_to_aWS <|
      le_trans h_aWS_to_sum <|
      le_trans h_sum_to_wsum h_with_const
  exact Nat.not_lt_of_ge hge hspec'

/-- Concrete restricted-quadratic witness extracted from a successor pump. -/
def quadratic_witness_of_succ_pump {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    BarrierCertificate S M.eval where
  b := S.base
  s := succIter S (quadraticThreshold M)
  n := S.base
  fails :=
    quadratic_failure_at_base M (succIter S (quadraticThreshold M))
      (by
        simpa [quadraticThreshold] using
          eval_succIter_ge_quadratic (M := M) h_succ_bias h_succ_scale
            (quadraticThreshold M))

/-- Concrete restricted-quadratic witness extracted from a wrapper pump. -/
def quadratic_witness_of_wrap_pump {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    BarrierCertificate S M.eval where
  b := S.base
  s := wrapIter S (quadraticThreshold M)
  n := S.base
  fails :=
    quadratic_failure_at_base M (wrapIter S (quadraticThreshold M))
      (by
        simpa [quadraticThreshold] using
          eval_wrapIter_ge_quadratic (M := M) h_wrap_bias
            (quadraticThreshold M))

/-- Automatic witness extractor for the strengthened restricted-quadratic pumped subclass. -/
def quadratic_with_pump_witness {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasureWithPump S) :
    BarrierCertificate S M.eval := by
  classical
  if hsucc : 1 ≤ M.succ_bias ∧ 1 ≤ M.succ_scale then
    exact quadratic_witness_of_succ_pump M.toQuadraticCounterMeasure hsucc.1 hsucc.2
  else
    have hwrap : 1 ≤ M.wrap_const + M.wrap_right * M.c_base := by
      rcases M.has_pump with hsucc' | hwrap
      · exact False.elim (hsucc hsucc')
      · exact hwrap
    exact quadratic_witness_of_wrap_pump M.toQuadraticCounterMeasure hwrap

@[simp] private def maxSuccBase {S : StepDuplicatingSchema} (M : MaxMeasure S) : Nat :=
  M.succ_const + M.c_base

@[simp] private def maxThreshold {S : StepDuplicatingSchema} (M : MaxMeasure S) : Nat :=
  max (M.recur_base + M.c_base) (M.recur_counter + maxSuccBase M)

private theorem max_failure_at_base
    {S : StepDuplicatingSchema} (M : MaxMeasure S) (s : S.T)
    (hs : maxThreshold M ≤ M.eval s) :
    ¬ (M.eval (S.wrap s (S.recur S.base s S.base)) <
        M.eval (S.recur S.base s (S.succ S.base))) := by
  intro h
  let Sval := M.eval s
  have hs_base : M.recur_base + M.c_base ≤ M.recur_step + Sval := by
    have h0 : M.recur_base + M.c_base ≤ maxThreshold M := by
      exact le_max_left _ _
    have h1 : maxThreshold M ≤ Sval := by
      simpa [maxThreshold, Sval] using hs
    exact le_trans h0 <| le_trans h1 (Nat.le_add_left _ _)
  have hs_ctr_src : M.recur_counter + maxSuccBase M ≤ M.recur_step + Sval := by
    have h0 : M.recur_counter + maxSuccBase M ≤ maxThreshold M := by
      exact le_max_right _ _
    have h1 : maxThreshold M ≤ Sval := by
      simpa [maxThreshold, Sval] using hs
    exact le_trans h0 <| le_trans h1 (Nat.le_add_left _ _)
  have hs_ctr_tgt : M.recur_counter + M.c_base ≤ M.recur_step + Sval := by
    calc
      M.recur_counter + M.c_base ≤ M.recur_counter + maxSuccBase M := by
        simp [maxSuccBase]
      _ ≤ M.recur_step + Sval := hs_ctr_src
  have hsrc_eq :
      M.eval (S.recur S.base s (S.succ S.base)) = M.recur_const + (M.recur_step + Sval) := by
    rw [M.eval_recur, M.eval_succ, M.eval_base]
    have hs_base' : M.c_base + M.recur_base ≤ M.recur_step + Sval := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_base
    have hs_ctr_src' : M.c_base + (M.succ_const + M.recur_counter) ≤ M.recur_step + Sval := by
      simpa [maxSuccBase, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_ctr_src
    have hmax :
        max (M.c_base + M.recur_base)
            (max (M.recur_step + Sval) (M.c_base + (M.succ_const + M.recur_counter))) =
          M.recur_step + Sval := by
      have hinner :
          max (M.recur_step + Sval) (M.c_base + (M.succ_const + M.recur_counter)) =
            M.recur_step + Sval := by
        exact max_eq_left hs_ctr_src'
      rw [hinner]
      exact max_eq_right hs_base'
    simp [Sval, Nat.add_left_comm, Nat.add_comm, hmax]
  have hinner_eq :
      M.eval (S.recur S.base s S.base) = M.recur_const + (M.recur_step + Sval) := by
    rw [M.eval_recur, M.eval_base]
    have hs_base' : M.c_base + M.recur_base ≤ M.recur_step + Sval := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_base
    have hs_ctr_tgt' : M.c_base + M.recur_counter ≤ M.recur_step + Sval := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_ctr_tgt
    have hmax :
        max (M.c_base + M.recur_base)
            (max (M.recur_step + Sval) (M.c_base + M.recur_counter)) =
          M.recur_step + Sval := by
      have hinner :
          max (M.recur_step + Sval) (M.c_base + M.recur_counter) =
            M.recur_step + Sval := by
        exact max_eq_left hs_ctr_tgt'
      rw [hinner]
      exact max_eq_right hs_base'
    simp [Sval, Nat.add_comm, hmax]
  rw [hsrc_eq, M.eval_wrap, hinner_eq] at h
  have htarget_ge :
      M.recur_const + (M.recur_step + Sval) + 1 ≤
        M.wrap_const +
          max (M.wrap_left + Sval)
            (M.wrap_right + (M.recur_const + (M.recur_step + Sval))) := by
    have hright :
        M.recur_const + (M.recur_step + Sval) + 1 ≤
          M.wrap_right + (M.recur_const + (M.recur_step + Sval)) := by
      nlinarith [M.h_wrap_right_pos]
    have hmax :
        M.wrap_right + (M.recur_const + (M.recur_step + Sval)) ≤
          max (M.wrap_left + Sval)
            (M.wrap_right + (M.recur_const + (M.recur_step + Sval))) := by
      exact le_max_right _ _
    exact le_trans hright <| le_trans hmax (Nat.le_add_left _ _)
  have hge :
      M.recur_const + (M.recur_step + Sval) <
        M.wrap_const +
          max (M.wrap_left + Sval)
            (M.wrap_right + (M.recur_const + (M.recur_step + Sval))) := by
    omega
  exact Nat.not_lt_of_ge (Nat.le_of_lt hge) h

/-- Concrete max-plus witness extracted from a successor pump. -/
def max_witness_of_succ_pump {S : StepDuplicatingSchema}
    (M : MaxMeasure S) (h_succ_const : 1 ≤ M.succ_const) :
    BarrierCertificate S M.eval where
  b := S.base
  s := succIter S (maxThreshold M)
  n := S.base
  fails :=
    max_failure_at_base M (succIter S (maxThreshold M))
      (by
        simpa [maxThreshold] using
          eval_succIter_ge_max (M := M) h_succ_const (maxThreshold M))

/-- Concrete max-plus witness extracted from a wrapper pump. -/
def max_witness_of_wrap_pump {S : StepDuplicatingSchema}
    (M : MaxMeasure S) (h_wrap_drift : 1 ≤ M.wrap_const + M.wrap_left) :
    BarrierCertificate S M.eval where
  b := S.base
  s := wrapIter S (maxThreshold M)
  n := S.base
  fails :=
    max_failure_at_base M (wrapIter S (maxThreshold M))
      (by
        simpa [maxThreshold] using
          eval_wrapIter_ge_max (M := M) h_wrap_drift (maxThreshold M))

/-- Automatic witness extractor for the strengthened max-plus pumped subclass. -/
def max_with_pump_witness {S : StepDuplicatingSchema}
    (M : MaxMeasureWithPump S) :
    BarrierCertificate S M.eval := by
  classical
  if hsucc : 1 ≤ M.succ_const then
    exact max_witness_of_succ_pump M.toMaxMeasure hsucc
  else
    have hwrap : 1 ≤ M.wrap_const + M.wrap_left := by
      rcases M.has_pump with hsucc' | hwrap
      · exact False.elim (hsucc hsucc')
      · exact hwrap
    exact max_witness_of_wrap_pump M.toMaxMeasure hwrap

/-- Lift the projected affine witness back to the vector-valued matrix family. -/
def matrixFunctional_with_projected_affine_pump_witness
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasureWithProjectedAffinePump S d) :
    RelationBarrierCertificate S (Fin d → Nat) M.eval VecLt := by
  let cert := affine_with_pump_witness (S := S) M.projectedAffineWithPump
  exact
    { b := cert.b
      s := cert.s
      n := cert.n
      fails := by
        intro hlt
        exact cert.fails (weightedSum_lt_of_vecLt M.h_weight_support hlt) }

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
