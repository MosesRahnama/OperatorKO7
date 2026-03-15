import OperatorKO7.Meta.PolyInterpretation_FullStep
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith

/-!
Context-closed strong normalization for the full unguarded KO7 system.

This module closes the remaining internal gap between the root-step full-system proofs and
context-closed termination. The key point is that the nonlinear polynomial witness `W`
from `Meta/PolyInterpretation_FullStep.lean` is strictly monotone in every constructor
argument, so every contextual closure of a `Step` contraction still strictly decreases `W`.
-/

open OperatorKO7 Trace
open OperatorKO7.PolyInterpretation

namespace MetaSN_KO7

/-- Full context closure of the unguarded kernel relation `Step`. -/
inductive StepCtxFull : Trace → Trace → Prop
| root {a b : Trace} : Step a b → StepCtxFull a b
| delta {t u : Trace} : StepCtxFull t u → StepCtxFull (delta t) (delta u)
| integrate {t u : Trace} : StepCtxFull t u → StepCtxFull (integrate t) (integrate u)
| mergeL {a a' b : Trace} : StepCtxFull a a' → StepCtxFull (merge a b) (merge a' b)
| mergeR {a b b' : Trace} : StepCtxFull b b' → StepCtxFull (merge a b) (merge a b')
| appL {a a' b : Trace} : StepCtxFull a a' → StepCtxFull (app a b) (app a' b)
| appR {a b b' : Trace} : StepCtxFull b b' → StepCtxFull (app a b) (app a b')
| recB {b b' s n : Trace} : StepCtxFull b b' → StepCtxFull (recΔ b s n) (recΔ b' s n)
| recS {b s s' n : Trace} : StepCtxFull s s' → StepCtxFull (recΔ b s n) (recΔ b s' n)
| recN {b s n n' : Trace} : StepCtxFull n n' → StepCtxFull (recΔ b s n) (recΔ b s n')
| eqWL {a a' b : Trace} : StepCtxFull a a' → StepCtxFull (eqW a b) (eqW a' b)
| eqWR {a b b' : Trace} : StepCtxFull b b' → StepCtxFull (eqW a b) (eqW a b')

/-- Reverse full context relation. -/
def StepCtxFullRev : Trace → Trace → Prop := fun a b => StepCtxFull b a

/-- The global polynomial witness `W` strictly decreases on every full contextual step. -/
theorem W_orients_stepCtxFull : ∀ {a b : Trace}, StepCtxFull a b → W b < W a
  | _, _, StepCtxFull.root h => W_orients_step h
  | _, _, StepCtxFull.delta h => by
      simpa [W] using Nat.succ_lt_succ (W_orients_stepCtxFull h)
  | _, _, StepCtxFull.integrate h => by
      simpa [W] using Nat.succ_lt_succ (W_orients_stepCtxFull h)
  | _, _, StepCtxFull.mergeL h => by
      have hh := W_orients_stepCtxFull h
      simp only [W] at hh ⊢
      omega
  | _, _, StepCtxFull.mergeR h => by
      have hh := W_orients_stepCtxFull h
      simp only [W] at hh ⊢
      omega
  | _, _, StepCtxFull.appL h => by
      have hh := W_orients_stepCtxFull h
      simp only [W] at hh ⊢
      omega
  | _, _, StepCtxFull.appR h => by
      have hh := W_orients_stepCtxFull h
      simp only [W] at hh ⊢
      omega
  | _, _, StepCtxFull.recB (s := s) (n := n) h => by
      have hh := W_orients_stepCtxFull h
      have hs : 1 ≤ W s := W_pos s
      have hn : 1 ≤ W n := W_pos n
      simp only [W] at hh ⊢
      nlinarith
  | _, _, StepCtxFull.recS (b := b) (n := n) h => by
      have hh := W_orients_stepCtxFull h
      have hb : 1 ≤ W b := W_pos b
      have hn : 1 ≤ W n := W_pos n
      simp only [W] at hh ⊢
      nlinarith
  | _, _, StepCtxFull.recN (b := b) (s := s) h => by
      have hh := W_orients_stepCtxFull h
      have hb : 1 ≤ W b := W_pos b
      have hs : 1 ≤ W s := W_pos s
      simp only [W] at hh ⊢
      nlinarith
  | _, _, StepCtxFull.eqWL h => by
      have hh := W_orients_stepCtxFull h
      simp only [W] at hh ⊢
      omega
  | _, _, StepCtxFull.eqWR h => by
      have hh := W_orients_stepCtxFull h
      simp only [W] at hh ⊢
      omega

/-- Full context-closed strong normalization from the global polynomial witness. -/
theorem wf_StepCtxFullRev_poly : WellFounded StepCtxFullRev := by
  have hsub :
      Subrelation StepCtxFullRev (fun x y : Trace => W x < W y) := by
    intro x y hxy
    exact W_orients_stepCtxFull hxy
  exact Subrelation.wf hsub (InvImage.wf (f := W) Nat.lt_wfRel.wf)

end MetaSN_KO7
