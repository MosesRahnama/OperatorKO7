/-!
# Symbolic Variable-Condition Barrier: Schema Layer

Schema-generic symbolic obstruction behind direct KBO-style comparators.

This file isolates the variable-count argument on the primitive duplicating
schema terms themselves. KO7-specific trace instantiation lives in
`Meta/SymbolicComparatorBarrier.lean`.
-/

namespace OperatorKO7.SymbolicComparatorBarrier

inductive SchemaVar where
  | b
  | s
  | n
deriving DecidableEq, Repr

inductive STerm where
  | var : SchemaVar → STerm
  | base : STerm
  | succ : STerm → STerm
  | wrap : STerm → STerm → STerm
  | recur : STerm → STerm → STerm → STerm
deriving DecidableEq, Repr

open SchemaVar

def countVar (v : SchemaVar) : STerm → Nat
  | STerm.var w => if v = w then 1 else 0
  | STerm.base => 0
  | STerm.succ t => countVar v t
  | STerm.wrap x y => countVar v x + countVar v y
  | STerm.recur bT sT nT => countVar v bT + countVar v sT + countVar v nT

def dupSrc : STerm :=
  STerm.recur (STerm.var b) (STerm.var s) (STerm.succ (STerm.var n))

def dupTgt : STerm :=
  STerm.wrap (STerm.var s) (STerm.recur (STerm.var b) (STerm.var s) (STerm.var n))

theorem countVar_dupSrc_b : countVar b dupSrc = 1 := by
  simp [dupSrc, countVar]

theorem countVar_dupSrc_s : countVar s dupSrc = 1 := by
  simp [dupSrc, countVar]

theorem countVar_dupSrc_n : countVar n dupSrc = 1 := by
  simp [dupSrc, countVar]

theorem countVar_dupTgt_b : countVar b dupTgt = 1 := by
  simp [dupTgt, countVar]

theorem countVar_dupTgt_s : countVar s dupTgt = 2 := by
  simp [dupTgt, countVar]

theorem countVar_dupTgt_n : countVar n dupTgt = 1 := by
  simp [dupTgt, countVar]

structure VariableConditionOrder where
  gt : STerm → STerm → Prop
  variable_condition :
    ∀ {x y : STerm} {v : SchemaVar}, gt x y → countVar v y ≤ countVar v x

theorem not_orients_dup_rule (O : VariableConditionOrder) :
    ¬ O.gt dupSrc dupTgt := by
  intro h
  have hs : countVar s dupTgt ≤ countVar s dupSrc := O.variable_condition h
  simp [countVar_dupSrc_s, countVar_dupTgt_s] at hs

theorem no_symbolic_variable_condition_orients_dup_step :
    ¬ ∃ O : VariableConditionOrder, O.gt dupSrc dupTgt := by
  rintro ⟨O, h⟩
  exact not_orients_dup_rule O h

end OperatorKO7.SymbolicComparatorBarrier
