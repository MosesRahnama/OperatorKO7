import OperatorKO7.Meta.ProjectedPrimaryBarrier

/-!
# Permutation-Priority Finite Lexicographic Barrier

This module extends the finite tracked-primary lexicographic barrier from the fixed natural
coordinate order to arbitrary priority permutations.

The important point is structural: once a chosen primary coordinate is placed at highest
priority in the lex order, the same barrier proof goes through. A lexicographic decrease
under that priority permutation still forces the primary coordinate to be non-increasing,
so the standard affine pump on that coordinate blocks orientation.

This sharpens the orientation boundary in a mathematically meaningful way:
the barrier no longer depends on the incidental choice of coordinate enumeration.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- The distinguished highest-priority coordinate under a permutation-based lex order. -/
@[simp] def permPrimaryIdx {d : Nat} (σ : Equiv.Perm (Fin (d + 1))) : Fin (d + 1) :=
  σ (primaryIdx d)

/-- Strict lexicographic order induced by a priority permutation. -/
def VecPermLexLt {d : Nat} (σ : Equiv.Perm (Fin (d + 1)))
    (u v : Fin (d + 1) → Nat) : Prop :=
  ∃ i : Fin (d + 1),
    (∀ j : Fin (d + 1), j.val < i.val → u (σ j) = v (σ j)) ∧ u (σ i) < v (σ i)

/-- Any permutation-priority lex decrease forces the highest-priority coordinate to be
non-increasing. -/
theorem permPrimary_le_of_vecPermLexLt {d : Nat} {σ : Equiv.Perm (Fin (d + 1))}
    {u v : Fin (d + 1) → Nat}
    (h : VecPermLexLt σ u v) :
    u (permPrimaryIdx σ) ≤ v (permPrimaryIdx σ) := by
  rcases h with ⟨i, hprefix, hlt⟩
  by_cases hi : i = primaryIdx d
  · subst hi
    simpa [permPrimaryIdx] using Nat.le_of_lt hlt
  · have hpos : 0 < i.val := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply hi
      apply Fin.ext
      simpa [primaryIdx] using hz
    have heq := hprefix (primaryIdx d) hpos
    exact Nat.le_of_eq (by simpa [permPrimaryIdx] using heq)

/-- A finite-dimensional lexicographic direct measure whose highest-priority coordinate is a
tracked affine primary component. -/
structure MatrixLexPermMeasureD (S : StepDuplicatingSchema) (d : Nat) where
  priority : Equiv.Perm (Fin (d + 1))
  eval : S.T → Fin (d + 1) → Nat
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
  eval_base : eval S.base (permPrimaryIdx priority) = c_base
  eval_succ :
    ∀ t,
      eval (S.succ t) (permPrimaryIdx priority) =
        succ_bias + succ_scale * eval t (permPrimaryIdx priority)
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) (permPrimaryIdx priority) =
        wrap_const + wrap_left * eval x (permPrimaryIdx priority) +
          wrap_right * eval y (permPrimaryIdx priority)
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) (permPrimaryIdx priority) =
        recur_const + recur_base * eval b (permPrimaryIdx priority) +
          recur_step * eval s (permPrimaryIdx priority) +
          recur_counter * eval n (permPrimaryIdx priority)
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- The primary affine projection exposed by the permutation-priority family. -/
def MatrixLexPermMeasureD.primaryAffine
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexPermMeasureD S d) : AffineMeasure S where
  eval := fun t => M.eval t (permPrimaryIdx M.priority)
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Unbounded pump in the highest-priority coordinate. -/
def HasUnboundedPermPrimaryRange
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexPermMeasureD S d) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t (permPrimaryIdx M.priority)

/-- Permutation-priority lex families are instances of the generic projected-primary
dominance theorem. -/
theorem no_matrixLexPermD_orients_dup_step_of_unbounded_primary
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexPermMeasureD S d)
    (hunbounded : HasUnboundedPermPrimaryRange M) :
    ¬ (∀ (b s n : S.T),
      VecPermLexLt M.priority (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  apply no_orients_dup_step_of_projected_primary_dominance
    (μ := M.eval) (R := VecPermLexLt M.priority)
    (π := fun v => v (permPrimaryIdx M.priority)) (M := M.primaryAffine)
  · intro u v h
    exact permPrimary_le_of_vecPermLexLt h
  · intro t
    rfl
  · intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, ht⟩

/-- Successor-pump corollary for permutation-priority lex families. -/
theorem no_matrixLexPermD_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexPermMeasureD S d)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      VecPermLexLt M.priority (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  apply no_matrixLexPermD_orients_dup_step_of_unbounded_primary (M := M)
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa [MatrixLexPermMeasureD.primaryAffine] using
    (eval_succIter_ge M.primaryAffine h_succ_bias h_succ_scale k)

/-- Wrap-pump corollary for permutation-priority lex families. -/
theorem no_matrixLexPermD_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexPermMeasureD S d)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      VecPermLexLt M.priority (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  apply no_matrixLexPermD_orients_dup_step_of_unbounded_primary (M := M)
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa [MatrixLexPermMeasureD.primaryAffine] using
    (eval_wrapIter_ge_affine M.primaryAffine h_wrap_bias k)

/-- Strengthened permutation-priority family with an internal primary pump. -/
structure MatrixLexPermMeasureDWithPrimaryPump (S : StepDuplicatingSchema) (d : Nat)
    extends MatrixLexPermMeasureD S d where
  has_primary_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨ 1 ≤ wrap_const + wrap_right * c_base

/-- Unconditional barrier for the strengthened permutation-priority subclass. -/
theorem no_matrixLexPermD_with_primary_pump_orients_dup_step
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexPermMeasureDWithPrimaryPump S d) :
    ¬ (∀ (b s n : S.T),
      VecPermLexLt M.priority (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n)))) := by
  rcases M.has_primary_pump with hsucc | hwrap
  · exact no_matrixLexPermD_orients_dup_step_of_succ_pump (M := M.toMatrixLexPermMeasureD) hsucc.1 hsucc.2
  · exact no_matrixLexPermD_orients_dup_step_of_wrap_pump (M := M.toMatrixLexPermMeasureD) hwrap

/-- Global root orientation would orient the duplicating step as well. -/
theorem no_global_orients_matrixLexPermD_with_primary_pump
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixLexPermMeasureDWithPrimaryPump Sys.toStepDuplicatingSchema d) :
    ¬ GlobalOrients Sys M.eval (VecPermLexLt M.priority) := by
  intro h
  exact
    no_matrixLexPermD_with_primary_pump_orients_dup_step
      (S := Sys.toStepDuplicatingSchema) M
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.MatrixBarrierLexPermD

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 unconditional specialization for the strengthened permutation-priority subclass. -/
theorem no_global_step_orientation_matrixLexPermD_with_primary_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexPermMeasureDWithPrimaryPump ko7Schema d) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval
        (StepDuplicatingSchema.VecPermLexLt M.priority) := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixLexPermD_with_primary_pump
      (Sys := ko7System) M

end OperatorKO7.MatrixBarrierLexPermD
