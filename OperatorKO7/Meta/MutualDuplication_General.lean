import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Bounded SCC-Level Composite Duplication

This module lifts the concrete alternating two-recursors example to a bounded theorem-level
generalization. Each root rule already duplicates the payload once. The point of the result
is different: a fixed two-node mutually recursive SCC yields a stable two-step composite
profile and an induced minimal context relation on which the additive and affine barrier
arguments still go through.
-/

namespace OperatorKO7.MutualDuplicationGeneral

open OperatorKO7.StepDuplicating

/-- Shared constructor interface for a bounded two-node mutually recursive SCC. -/
structure AlternatingDupSchema where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recurA : T → T → T → T
  recurB : T → T → T → T

namespace AlternatingDupSchema

/-- Forget the second recursor and expose the ordinary base/successor/wrapper interface
needed for the additive pump argument. -/
def toPumpSchema (S : AlternatingDupSchema) : StepDuplicatingSchema where
  T := S.T
  base := S.base
  succ := S.succ
  wrap := S.wrap
  recur := S.recurA

/-- Wrapper-chain pump used in the bounded SCC theorem. -/
def wrapIter (S : AlternatingDupSchema) : Nat → S.T :=
  StepDuplicatingSchema.wrapIter S.toPumpSchema

/-- Derived single-rule schema for one full SCC cycle: the successor is doubled and
the wrapper duplicates the payload across two nested wraps. -/
def toDup2Schema (S : AlternatingDupSchema) : StepDuplicatingSchema where
  T := S.T
  base := S.base
  succ := fun n => S.succ (S.succ n)
  wrap := fun s t => S.wrap s (S.wrap s t)
  recur := S.recurA

/-- Uniform additive measures on the alternating SCC schema. Both recursors share one
constructor-local weight profile. -/
structure AdditiveMeasure (S : AlternatingDupSchema) where
  eval : S.T → Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval S.base = w_base
  eval_succ : ∀ t, eval (S.succ t) = w_succ + eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = w_wrap + eval x + eval y
  eval_recurA :
    ∀ b s n, eval (S.recurA b s n) = w_recur + eval b + eval s + eval n
  eval_recurB :
    ∀ b s n, eval (S.recurB b s n) = w_recur + eval b + eval s + eval n
  h_wrap_pos : 1 ≤ w_wrap

/-- Convert the alternating additive measure to the ordinary schema-level additive measure
used by the wrapper pump. -/
def AdditiveMeasure.toPumpMeasure {S : AlternatingDupSchema}
    (M : AdditiveMeasure S) :
    StepDuplicatingSchema.AdditiveMeasure S.toPumpSchema where
  eval := M.eval
  w_base := M.w_base
  w_succ := M.w_succ
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recurA
  h_wrap_pos := M.h_wrap_pos

/-- The ordinary wrapper-chain pump still grows additive measures on the alternating schema. -/
lemma eval_wrapIter_ge {S : AlternatingDupSchema} (M : AdditiveMeasure S) (k : Nat) :
    M.eval (S.wrapIter k) ≥ k := by
  simpa [AlternatingDupSchema.wrapIter, AdditiveMeasure.toPumpMeasure] using
    (StepDuplicatingSchema.eval_wrapIter_ge
      (S := S.toPumpSchema) (M := M.toPumpMeasure) k)

/-- Uniform affine constructor-local measures on the alternating SCC schema. Both recursors
share one constructor-local affine profile. -/
structure AffineMeasure (S : AlternatingDupSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recurA :
    ∀ b s n, eval (S.recurA b s n) = recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  eval_recurB :
    ∀ b s n, eval (S.recurB b s n) = recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- View the alternating SCC affine measure as a schema-level affine measure for one
full SCC cycle. -/
def AffineMeasure.toDup2Measure {S : AlternatingDupSchema}
    (M : AffineMeasure S) :
    StepDuplicatingSchema.AffineMeasure S.toDup2Schema where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias + M.succ_scale * M.succ_bias
  succ_scale := M.succ_scale * M.succ_scale
  wrap_const := M.wrap_const + M.wrap_right * M.wrap_const
  wrap_left := M.wrap_left + M.wrap_right * M.wrap_left
  wrap_right := M.wrap_right * M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := by
    intro t
    rw [show S.toDup2Schema.succ t = S.succ (S.succ t) by rfl]
    rw [M.eval_succ, M.eval_succ]
    ring
  eval_wrap := by
    intro x y
    rw [show S.toDup2Schema.wrap x y = S.wrap x (S.wrap x y) by rfl]
    rw [M.eval_wrap, M.eval_wrap]
    ring
  eval_recur := by
    intro b s n
    simpa [AlternatingDupSchema.toDup2Schema] using M.eval_recurA b s n
  h_wrap_left_pos := by
    have hwl := M.h_wrap_left_pos
    have hnonneg : 0 ≤ M.wrap_right * M.wrap_left := Nat.zero_le _
    omega
  h_wrap_right_pos := by
    have hwr := M.h_wrap_right_pos
    have hsq : 1 * 1 ≤ M.wrap_right * M.wrap_right := by
      exact Nat.mul_le_mul hwr hwr
    simpa using hsq

/-- Bounded SCC theorem: one alternating two-step duplicate already defeats any additive
direct orienter on the composite profile. -/
theorem no_additive_orients_alternating_dup2_composite
    {S : AlternatingDupSchema} (M : AdditiveMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.wrap s (S.recurA b s n))) <
        M.eval (S.recurA b s (S.succ (S.succ n)))) := by
  intro h
  let Sval := M.eval (S.wrapIter M.w_succ)
  have hspec := h S.base (S.wrapIter M.w_succ) S.base
  have hge := eval_wrapIter_ge M M.w_succ
  have hspec' :
      M.w_wrap + (M.w_wrap + (M.w_recur + (Sval + (Sval + Sval)))) <
        M.w_succ + (M.w_succ + (M.w_recur + Sval)) := by
    simpa [Sval, AlternatingDupSchema.wrapIter, AlternatingDupSchema.toPumpSchema,
      M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recurA,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hspec
  have hS : M.w_succ ≤ Sval := by
    simpa [Sval] using hge
  have hwrap := M.h_wrap_pos
  omega

/-- One SCC cycle also defeats any affine direct orienter on the composite profile,
provided the derived two-step schema admits the usual unbounded pump. -/
theorem no_affine_orients_alternating_dup2_composite_of_unbounded
    {S : AlternatingDupSchema} (M : AffineMeasure S)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange M.toDup2Measure) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.wrap s (S.recurA b s n))) <
        M.eval (S.recurA b s (S.succ (S.succ n)))) := by
  simpa [AlternatingDupSchema.toDup2Schema, AffineMeasure.toDup2Measure] using
    (StepDuplicatingSchema.no_affine_orients_dup_step_of_unbounded
      (S := S.toDup2Schema) (M := M.toDup2Measure) hunbounded)

/-- A bounded two-node mutually recursive system whose payload duplication appears only after
one full SCC cycle. -/
structure AlternatingDupSystem extends AlternatingDupSchema where
  Step : T → T → Prop
  stepA_succ : ∀ b s n, Step (recurA b s (succ n)) (wrap s (recurB b s n))
  stepB_succ : ∀ b s n, Step (recurB b s (succ n)) (wrap s (recurA b s n))

/-- Minimal context closure needed for the SCC-cycle realization:
root steps plus reduction under the right wrapper argument. -/
inductive StepCtx (Sys : AlternatingDupSystem) : Sys.T → Sys.T → Prop
| root : ∀ {a b}, Sys.Step a b → StepCtx Sys a b
| wrap_right : ∀ s {a b}, StepCtx Sys a b → StepCtx Sys (Sys.wrap s a) (Sys.wrap s b)

/-- Orientation of the bounded SCC relation under the minimal context closure. -/
def GlobalOrientsCtx {α : Type} (Sys : AlternatingDupSystem) (m : Sys.T → α)
    (lt : α → α → Prop) : Prop :=
  ∀ {a b : Sys.T}, StepCtx Sys a b → lt (m b) (m a)

/-- One SCC cycle realizes the delayed duplicate generically. -/
theorem alternating_dup2_realized (Sys : AlternatingDupSystem) (b s n : Sys.T) :
    ∃ u,
      StepCtx Sys (Sys.recurA b s (Sys.succ (Sys.succ n))) u ∧
      StepCtx Sys u (Sys.wrap s (Sys.wrap s (Sys.recurA b s n))) := by
  refine ⟨Sys.wrap s (Sys.recurB b s (Sys.succ n)), ?_, ?_⟩
  · exact StepCtx.root (Sys.stepA_succ b s (Sys.succ n))
  · exact StepCtx.wrap_right s (StepCtx.root (Sys.stepB_succ b s n))

/-- The bounded SCC theorem also rules out any additive orientation of the whole
minimal-context relation, because that would force the composite duplicate to decrease. -/
theorem no_global_orients_ctx_additive
    {Sys : AlternatingDupSystem} (M : AdditiveMeasure Sys.toAlternatingDupSchema) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : Sys.T),
        M.eval (Sys.wrap s (Sys.wrap s (Sys.recurA b s n))) <
          M.eval (Sys.recurA b s (Sys.succ (Sys.succ n))) := by
    intro b s n
    rcases alternating_dup2_realized Sys b s n with ⟨u, h₁, h₂⟩
    exact Nat.lt_trans (h h₂) (h h₁)
  exact no_additive_orients_alternating_dup2_composite (S := Sys.toAlternatingDupSchema) M hcomp

/-- The bounded SCC theorem also rules out any affine orientation of the whole
minimal-context relation, provided the derived two-step schema admits the usual
unbounded pump. -/
theorem no_global_orients_ctx_affine_of_unbounded
    {Sys : AlternatingDupSystem} (M : AffineMeasure Sys.toAlternatingDupSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange M.toDup2Measure) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : Sys.T),
        M.eval (Sys.wrap s (Sys.wrap s (Sys.recurA b s n))) <
          M.eval (Sys.recurA b s (Sys.succ (Sys.succ n))) := by
    intro b s n
    rcases alternating_dup2_realized Sys b s n with ⟨u, h₁, h₂⟩
    exact Nat.lt_trans (h h₂) (h h₁)
  exact
    no_affine_orients_alternating_dup2_composite_of_unbounded
      (S := Sys.toAlternatingDupSchema) M hunbounded hcomp

end AlternatingDupSchema

end OperatorKO7.MutualDuplicationGeneral
