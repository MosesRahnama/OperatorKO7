import OperatorKO7.Meta.Conjecture_Boundary

/-!
# Max-Based Depth Barrier

This module upgrades the standalone tree-depth witness to a theorem-backed family.
The family is still KO7-specific: constructor-local heights are aggregated by `max`,
not by addition, and the critical failure is exhibited on the kernel `rec_succ` rule.
-/

namespace OperatorKO7.DepthBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.MetaConjectureBoundary

/-- A KO7-specific max-aggregative depth family. Unary constructors add a fixed bump;
binary and ternary constructors add a fixed bump on top of the maximum depth of their
arguments. -/
structure MaxDepthMeasure where
  c_void : Nat
  c_delta : Nat
  c_integrate : Nat
  c_merge : Nat
  c_app : Nat
  c_rec : Nat
  c_eq : Nat
  h_app_pos : 1 ≤ c_app

/-- Evaluation for the max-aggregative depth family. -/
@[simp] def MaxDepthMeasure.eval (M : MaxDepthMeasure) : Trace → Nat
  | .void => M.c_void
  | .delta t => M.c_delta + M.eval t
  | .integrate t => M.c_integrate + M.eval t
  | .merge a b => M.c_merge + max (M.eval a) (M.eval b)
  | .app a b => M.c_app + max (M.eval a) (M.eval b)
  | .recΔ b s n => M.c_rec + max (max (M.eval b) (M.eval s)) (M.eval n)
  | .eqW a b => M.c_eq + max (M.eval a) (M.eval b)

/-- No max-aggregative depth measure can globally orient `Step`. The duplicating rule
already forces a contradiction at `b = void`, `s = delta void`, `n = void`. -/
theorem no_global_step_orientation_maxDepth (M : MaxDepthMeasure) :
    ¬ GlobalOrients M.eval (· < ·) := by
  intro h
  have hstep : Step (recΔ void (delta void) (delta void))
      (app (delta void) (recΔ void (delta void) void)) :=
    Step.R_rec_succ void (delta void) void
  have hlt := h hstep
  simp [MaxDepthMeasure.eval] at hlt

/-- The usual unit-increment tree depth is an instance of the max-depth family. -/
def standardTreeDepthMeasure : MaxDepthMeasure where
  c_void := 0
  c_delta := 1
  c_integrate := 1
  c_merge := 1
  c_app := 1
  c_rec := 1
  c_eq := 1
  h_app_pos := by simp

/-- The standard KO7 tree depth is exactly the unit-increment max-depth instance. -/
theorem standardTreeDepth_eval :
    standardTreeDepthMeasure.eval = MetaConjectureBoundary.treeDepth := by
  funext t
  induction t with
  | void =>
      simp [standardTreeDepthMeasure, MaxDepthMeasure.eval, MetaConjectureBoundary.treeDepth]
  | delta a ih =>
      rw [MaxDepthMeasure.eval, MetaConjectureBoundary.treeDepth, ih]
      simp [standardTreeDepthMeasure, Nat.add_comm]
  | integrate a ih =>
      rw [MaxDepthMeasure.eval, MetaConjectureBoundary.treeDepth, ih]
      simp [standardTreeDepthMeasure, Nat.add_comm]
  | merge a b iha ihb =>
      rw [MaxDepthMeasure.eval, MetaConjectureBoundary.treeDepth, iha, ihb]
      simp [standardTreeDepthMeasure, Nat.add_comm]
  | app a b iha ihb =>
      rw [MaxDepthMeasure.eval, MetaConjectureBoundary.treeDepth, iha, ihb]
      simp [standardTreeDepthMeasure, Nat.add_comm]
  | recΔ b s n ihb ihs ihn =>
      rw [MaxDepthMeasure.eval, MetaConjectureBoundary.treeDepth, ihb, ihs, ihn]
      simp [standardTreeDepthMeasure, max_assoc, Nat.add_comm]
  | eqW a b iha ihb =>
      rw [MaxDepthMeasure.eval, MetaConjectureBoundary.treeDepth, iha, ihb]
      simp [standardTreeDepthMeasure, Nat.add_comm]

/-- The existing tree-depth witness is therefore subsumed by the max-depth family theorem. -/
theorem no_global_step_orientation_standardTreeDepth :
    ¬ GlobalOrients MetaConjectureBoundary.treeDepth (· < ·) := by
  simpa [standardTreeDepth_eval] using
    no_global_step_orientation_maxDepth standardTreeDepthMeasure

end OperatorKO7.DepthBarrier
