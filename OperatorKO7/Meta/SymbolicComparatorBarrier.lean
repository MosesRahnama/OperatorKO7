import OperatorKO7.Kernel

/-!
# Symbolic Variable-Condition Barrier

This module isolates a symbolic obstruction behind direct KBO-style comparators.
The only axiom used is the standard variable condition: if `x ≻ y`, then every
variable occurs in `y` at most as often as in `x`.

For the duplicating schema step

`recur(b,s,succ(n)) -> wrap(s, recur(b,s,n))`

the payload variable `s` occurs once on the source side and twice on the target
side. Any symbolic comparator satisfying the variable condition therefore fails
on this step.
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

def instantiate (bT sT nT : Trace) : STerm → Trace
  | STerm.var SchemaVar.b => bT
  | STerm.var SchemaVar.s => sT
  | STerm.var SchemaVar.n => nT
  | STerm.base => Trace.void
  | STerm.succ t => Trace.delta (instantiate bT sT nT t)
  | STerm.wrap x y => Trace.app (instantiate bT sT nT x) (instantiate bT sT nT y)
  | STerm.recur bU sU nU =>
      Trace.recΔ (instantiate bT sT nT bU) (instantiate bT sT nT sU) (instantiate bT sT nT nU)

theorem instantiate_dupSrc (bT sT nT : Trace) :
    instantiate bT sT nT dupSrc = Trace.recΔ bT sT (Trace.delta nT) := by
  simp [dupSrc, instantiate]

theorem instantiate_dupTgt (bT sT nT : Trace) :
    instantiate bT sT nT dupTgt = Trace.app sT (Trace.recΔ bT sT nT) := by
  simp [dupTgt, instantiate]

end OperatorKO7.SymbolicComparatorBarrier
