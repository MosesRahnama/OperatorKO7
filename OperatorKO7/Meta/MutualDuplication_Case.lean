import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Concrete Alternating / Delayed Duplication Case

This file implements one explicit alternating two-function example.  No single root rule
duplicates the step argument.  Duplication appears only after composing two steps:

- `recurA b s (succ n) → wrap s (recurB b s n)`
- `recurB b s (succ n) → wrap s (recurA b s n)`

Starting from `recurA b s (succ (succ n))`, one root step plus one step under the right
argument of `wrap` yields

`wrap s (wrap s (recurA b s n))`.

The key point is that this effective two-step shape already exhibits the same additive
duplication obstruction directly: the composite target carries three copies of the step
payload measure against one copy on the source side.
-/

namespace OperatorKO7.MutualDuplicationCase

open OperatorKO7.StepDuplicating

/-- Minimal alternating syntax with two recursors sharing the same base/successor/wrapper
constructors. -/
inductive AltTerm : Type
| base : AltTerm
| succ : AltTerm → AltTerm
| wrap : AltTerm → AltTerm → AltTerm
| recurA : AltTerm → AltTerm → AltTerm → AltTerm
| recurB : AltTerm → AltTerm → AltTerm → AltTerm
deriving DecidableEq, Repr

open AltTerm

/-- The alternating root rules: no single rule duplicates the step argument. -/
inductive AltStep : AltTerm → AltTerm → Prop
| R_A_zero : ∀ b s, AltStep (recurA b s base) b
| R_A_succ : ∀ b s n, AltStep (recurA b s (succ n)) (wrap s (recurB b s n))
| R_B_zero : ∀ b s, AltStep (recurB b s base) b
| R_B_succ : ∀ b s n, AltStep (recurB b s (succ n)) (wrap s (recurA b s n))

/-- Minimal context closure needed to realize the delayed duplicate:
we may reduce under the right argument of the wrapper. -/
inductive AltStepCtx : AltTerm → AltTerm → Prop
| root : ∀ {a b}, AltStep a b → AltStepCtx a b
| wrap_right : ∀ s {a b}, AltStepCtx a b → AltStepCtx (wrap s a) (wrap s b)

/-- One explicit two-step realization of the delayed duplicate. -/
theorem alternating_dup2_realized (b s n : AltTerm) :
    ∃ u,
      AltStepCtx (recurA b s (succ (succ n))) u ∧
      AltStepCtx u (wrap s (wrap s (recurA b s n))) := by
  refine ⟨wrap s (recurB b s (succ n)), ?_, ?_⟩
  · exact AltStepCtx.root (AltStep.R_A_succ b s (succ n))
  · exact AltStepCtx.wrap_right s (AltStepCtx.root (AltStep.R_B_succ b s n))

/-- Uniform additive measures on the alternating syntax: both recursors share the same
constructor-local weight.  This is the bounded worked case treated here. -/
structure AdditiveAlternatingMeasure where
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  h_wrap_pos : 1 ≤ w_wrap

/-- Evaluation for the uniform additive alternating measures. -/
@[simp] def AdditiveAlternatingMeasure.eval (M : AdditiveAlternatingMeasure) : AltTerm → Nat
  | base => M.w_base
  | succ t => M.w_succ + M.eval t
  | wrap a b => M.w_wrap + M.eval a + M.eval b
  | recurA b s n => M.w_recur + M.eval b + M.eval s + M.eval n
  | recurB b s n => M.w_recur + M.eval b + M.eval s + M.eval n

def alternatingPumpSchema : StepDuplicatingSchema where
  T := AltTerm
  base := base
  succ := succ
  wrap := wrap
  recur := recurA

/-- The ordinary wrapper chain used to pump the step payload in the worked alternating case. -/
def wrapIter : Nat → AltTerm :=
  StepDuplicatingSchema.wrapIter alternatingPumpSchema

/-- Forget the second recursor and view the measure on the ordinary base/successor/wrapper
interface needed for the additive pump argument. -/
def AdditiveAlternatingMeasure.toPumpMeasure
    (M : AdditiveAlternatingMeasure) :
    StepDuplicatingSchema.AdditiveMeasure alternatingPumpSchema where
  eval := M.eval
  w_base := M.w_base
  w_succ := M.w_succ
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_base := by rfl
  eval_succ := by
    intro t
    simp [alternatingPumpSchema, AdditiveAlternatingMeasure.eval]
  eval_wrap := by
    intro x y
    simp [alternatingPumpSchema, AdditiveAlternatingMeasure.eval]
  eval_recur := by
    intro b s n
    simp [alternatingPumpSchema, AdditiveAlternatingMeasure.eval]
  h_wrap_pos := by
    exact M.h_wrap_pos

/-- The ordinary wrapper chain pumps additive measures on the alternating syntax. -/
lemma eval_wrapIter_ge (M : AdditiveAlternatingMeasure) (k : Nat) :
    M.eval (wrapIter k) ≥ k := by
  simpa [wrapIter, AdditiveAlternatingMeasure.toPumpMeasure] using
    (StepDuplicatingSchema.eval_wrapIter_ge
      (S := alternatingPumpSchema) (M := M.toPumpMeasure) k)

/-- Additive measures still cannot orient the delayed-duplication composite uniformly. -/
theorem no_additive_orients_alternating_dup2_step (M : AdditiveAlternatingMeasure) :
    ¬ (∀ (b s n : AltTerm),
      M.eval (wrap s (wrap s (recurA b s n))) <
        M.eval (recurA b s (succ (succ n)))) := by
  intro h
  let Sval := M.eval (wrapIter M.w_succ)
  have hspec := h base (wrapIter M.w_succ) base
  have hge := eval_wrapIter_ge M M.w_succ
  have hspec' :
      M.w_wrap + (M.w_wrap + (M.w_recur + (Sval + (Sval + Sval)))) <
        M.w_succ + (M.w_succ + (M.w_recur + Sval)) := by
    simpa [Sval, wrapIter, alternatingPumpSchema, AdditiveAlternatingMeasure.eval,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hspec
  have hwrap := M.h_wrap_pos
  have hS : M.w_succ ≤ Sval := by
    simpa [Sval] using hge
  omega

end OperatorKO7.MutualDuplicationCase
