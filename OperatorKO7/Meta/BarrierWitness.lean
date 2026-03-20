import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Computable barrier-witness extractors

This module packages the constructive content of the barrier theorems as
computable certificate extractors.  Given any claimed measure (additive,
compositional, or affine), the extractors produce a concrete instantiation
`(b, s, n)` for which orientation fails:

    M.eval (S.wrap s (S.recur b s n)) ≥ M.eval (S.recur b s (S.succ n))

Main definitions:

* `additive_witness`       — Tier 1 counterexample extractor
* `compositional_witness`  — Tier 2 counterexample extractor (with transparency)
* `affine_witness`         — Affine/linear counterexample extractor (with pump term)

Each returns a bundled triple with a proof that orientation fails on that triple.
-/

namespace OperatorKO7.StepDuplicating
open StepDuplicatingSchema

/-! Tier 1: Additive barrier witness -/

/-- Bundled counterexample: a triple `(b, s, n)` on which orientation provably fails. -/
structure BarrierCertificate (S : StepDuplicatingSchema) (eval : S.T → Nat) where
  b : S.T
  s : S.T
  n : S.T
  fails : ¬ (eval (S.wrap s (S.recur b s n)) < eval (S.recur b s (S.succ n)))

/-- Counterexample extractor for the Tier 1 (additive) barrier.
Given any additive compositional measure `M`, produces a concrete triple
`(base, wrapIter w_succ, base)` witnessing orientation failure. -/
def additive_witness {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    BarrierCertificate S M.eval where
  b := S.base
  s := wrapIter S M.w_succ
  n := S.base
  fails := by
    intro h
    have hge := eval_wrapIter_ge M M.w_succ
    simp [M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur] at h
    have := M.h_wrap_pos
    omega

/-- The additive witness term is computable from the measure weights alone. -/
theorem additive_witness_computable {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    (additive_witness M).s = wrapIter S M.w_succ := rfl

/-! Tier 2: Compositional barrier witness (with transparency) -/

/-- Counterexample extractor for the Tier 2 (compositional) barrier.
Given a compositional measure with base-level successor transparency,
produces the trivial triple `(base, base, base)` witnessing failure. -/
def compositional_witness {S : StepDuplicatingSchema}
    (CM : CompositionalMeasure S)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    BarrierCertificate S CM.eval where
  b := S.base
  s := S.base
  n := S.base
  fails := by
    intro h
    simp [CM.eval_base, CM.eval_succ, CM.eval_wrap, CM.eval_recur, h_transparent] at h
    have hsub := CM.wrap_subterm2 CM.c_base (CM.c_recur CM.c_base CM.c_base CM.c_base)
    omega

/-- The compositional witness is the minimal all-base instantiation. -/
theorem compositional_witness_is_base {S : StepDuplicatingSchema}
    (CM : CompositionalMeasure S)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    (compositional_witness CM h_transparent).b = S.base ∧
    (compositional_witness CM h_transparent).s = S.base ∧
    (compositional_witness CM h_transparent).n = S.base := ⟨rfl, rfl, rfl⟩

/-! Affine barrier witness -/

/-- Counterexample extractor for the affine/linear barrier.
Given an affine measure and a pump term `s₀` with `eval s₀ ≥ threshold`,
produces `(base, s₀, base)` witnessing orientation failure. -/
def affine_witness {S : StepDuplicatingSchema}
    (M : AffineMeasure S)
    (s₀ : S.T)
    (hs : M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) ≤ M.eval s₀) :
    BarrierCertificate S M.eval where
  b := S.base
  s := s₀
  n := S.base
  fails := by
    intro h
    let Sval := M.eval s₀
    let A := M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval
    let B := M.recur_counter * M.c_base
    let T := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
    have hspec' :
        M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) < A + T := by
      simpa [Sval, A, B, T, M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add] using h
    have hsT : T ≤ Sval := hs
    have hS : Sval ≤ M.wrap_left * Sval := by
      calc Sval = 1 * Sval := by simp
        _ ≤ M.wrap_left * Sval := Nat.mul_le_mul_right Sval M.h_wrap_left_pos
    have hAB : A + B ≤ M.wrap_right * (A + B) := by
      calc A + B = 1 * (A + B) := by simp
        _ ≤ M.wrap_right * (A + B) := Nat.mul_le_mul_right (A + B) M.h_wrap_right_pos
    have : A + T ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
      calc A + T
          ≤ A + Sval := Nat.add_le_add_left hsT A
        _ ≤ A + M.wrap_left * Sval := Nat.add_le_add_left hS A
        _ ≤ A + M.wrap_left * Sval + B := Nat.le_add_right _ _
        _ ≤ M.wrap_left * Sval + M.wrap_right * (A + B) := by
            have : M.wrap_left * Sval + (A + B) ≤
                M.wrap_left * Sval + M.wrap_right * (A + B) :=
              Nat.add_le_add_left hAB (M.wrap_left * Sval)
            omega
        _ ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
            omega
    exact Nat.not_lt_of_ge this hspec'

end OperatorKO7.StepDuplicating
