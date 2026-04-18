import OperatorKO7.Meta.SymbolicComparatorBarrier_Schema
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
