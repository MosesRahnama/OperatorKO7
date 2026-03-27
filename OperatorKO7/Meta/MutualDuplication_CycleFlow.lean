import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.ScalarProjectionBarrier
import OperatorKO7.Meta.DependencyPairs_Fragment

/-!
# Abstract Delayed-Duplication Cycle Barrier

This module isolates the common proof pattern behind the delayed-duplication SCC
results. A single full cycle is treated abstractly as a contextual path from

`recur b s (succ^copies n)`

to

`wrap^copies s (recur b s n)`.

The resulting theorems rederive additive, affine, transparent-compositional, and
scalar-projection contextual barriers from that one-cycle witness.
-/

namespace OperatorKO7.MutualDuplicationCycleFlow

open OperatorKO7.StepDuplicating
open OperatorKO7.DependencyPairsFragment
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Iterate the successor constructor on an arbitrary starting term. -/
def succIterOn (S : StepDuplicatingSchema) : Nat → S.T → S.T
  | 0, t => t
  | n + 1, t => S.succ (succIterOn S n t)

/-- Left-nested wrapper iteration around an arbitrary seed term. -/
def wrapNest (S : StepDuplicatingSchema) (s : S.T) : Nat → S.T → S.T
  | 0, t => t
  | n + 1, t => wrapNest S s n (S.wrap s t)

/-- One-cycle delayed-duplication source term. -/
def cycleSource (S : StepDuplicatingSchema) (copies : Nat) (b s n : S.T) : S.T :=
  S.recur b s (succIterOn S copies n)

/-- One-cycle delayed-duplication target term. -/
def cycleTarget (S : StepDuplicatingSchema) (copies : Nat) (b s n : S.T) : S.T :=
  wrapNest S s copies (S.recur b s n)

/-- Derived one-cycle schema on the same carrier. -/
def toDupSchema (S : StepDuplicatingSchema) (copies : Nat) : StepDuplicatingSchema where
  T := S.T
  base := S.base
  succ := succIterOn S copies
  wrap := fun s t => wrapNest S s copies t
  recur := S.recur

/-- Exact one-cycle witness for the induced minimal contextual relation. -/
structure CycleWitness (S : StepDuplicatingSchema) (copies : Nat) where
  StepCtx : S.T → S.T → Prop
  cycle_realized :
    ∀ b s n,
      Relation.TransGen StepCtx
        (cycleSource S copies b s n)
        (cycleTarget S copies b s n)

/-- Orientation of the induced contextual relation. -/
def GlobalOrientsCtx {S : StepDuplicatingSchema} {copies : Nat} {α : Type}
    (W : CycleWitness S copies) (m : S.T → α) (lt : α → α → Prop) : Prop :=
  ∀ {a b : S.T}, W.StepCtx a b → lt (m b) (m a)

lemma eval_succIter_additive {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    ∀ n t, M.eval (succIterOn S n t) = n * M.w_succ + M.eval t
  | 0, t => by simp [succIterOn]
  | n + 1, t => by
      rw [succIterOn, M.eval_succ, eval_succIter_additive M n t]
      ring

lemma eval_wrapNest_additive {S : StepDuplicatingSchema} (M : AdditiveMeasure S) (s : S.T) :
    ∀ n t, M.eval (wrapNest S s n t) = n * M.w_wrap + n * M.eval s + M.eval t
  | 0, t => by simp [wrapNest]
  | n + 1, t => by
      rw [wrapNest, eval_wrapNest_additive M s n (S.wrap s t), M.eval_wrap]
      ring

/-- A delayed duplicate over `copies ≥ 1` already defeats any additive direct orienter on
the composite one-cycle profile. -/
theorem no_additive_orients_cycle_composite
    {S : StepDuplicatingSchema} (M : AdditiveMeasure S) {copies : Nat}
    (hcopies : 1 ≤ copies) :
    ¬ (∀ (b s n : S.T),
      M.eval (cycleTarget S copies b s n) <
        M.eval (cycleSource S copies b s n)) := by
  intro h
  let sval := M.eval (wrapIter S M.w_succ)
  have hspec := h S.base (wrapIter S M.w_succ) S.base
  have hspec' :
      copies * M.w_wrap + copies * sval +
          (M.w_recur + M.w_base + sval + M.w_base) <
        copies * M.w_succ + (M.w_recur + M.w_base + sval + M.w_base) := by
    simpa [cycleSource, cycleTarget, sval, M.eval_base, M.eval_recur,
      eval_succIter_additive, eval_wrapNest_additive, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hspec
  have hdrop : copies * M.w_wrap + copies * sval < copies * M.w_succ := by
    exact Nat.lt_of_add_lt_add_right hspec'
  have hsval : M.w_succ ≤ sval := by
    simpa [sval] using eval_wrapIter_ge M M.w_succ
  have hmul : copies * M.w_succ ≤ copies * sval := by
    exact Nat.mul_le_mul_left _ hsval
  have hwrap : 1 ≤ copies * M.w_wrap := by
    exact Nat.mul_le_mul hcopies M.h_wrap_pos
  have hstrict : copies * M.w_succ < copies * M.w_wrap + copies * sval := by
    have hsval_lt : copies * sval < copies * M.w_wrap + copies * sval := by
      exact Nat.lt_add_of_pos_left hwrap
    exact lt_of_le_of_lt hmul hsval_lt
  exact Nat.not_lt_of_ge (Nat.le_of_lt hstrict) hdrop

/-- Any contextual relation realizing the delayed duplicate cycle is also blocked by the
additive barrier. -/
theorem no_global_orients_ctx_additive
    {S : StepDuplicatingSchema} {copies : Nat}
    (W : CycleWitness S copies) (M : AdditiveMeasure S) (hcopies : 1 ≤ copies) :
    ¬ GlobalOrientsCtx W M.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : S.T),
        M.eval (cycleTarget S copies b s n) <
          M.eval (cycleSource S copies b s n) := by
    intro b s n
    have horient : DependencyPairsFragment.GlobalOrients W.StepCtx M.eval (· < ·) := by
      intro a b hstep
      exact h hstep
    exact
      DependencyPairsFragment.transGen_drop
        (R := W.StepCtx) (m := M.eval) horient (W.cycle_realized b s n)
  exact no_additive_orients_cycle_composite M hcopies hcomp

namespace AffineOps

def succConst {S : StepDuplicatingSchema} (M : AffineMeasure S) : Nat → Nat
  | 0 => 0
  | n + 1 => M.succ_bias + M.succ_scale * succConst M n

def wrapRightIter {S : StepDuplicatingSchema} (M : AffineMeasure S) : Nat → Nat
  | 0 => 1
  | n + 1 => wrapRightIter M n * M.wrap_right

def wrapConstIter {S : StepDuplicatingSchema} (M : AffineMeasure S) : Nat → Nat
  | 0 => 0
  | n + 1 => wrapConstIter M n + wrapRightIter M n * M.wrap_const

def wrapLeftIter {S : StepDuplicatingSchema} (M : AffineMeasure S) : Nat → Nat
  | 0 => 0
  | n + 1 => wrapLeftIter M n + wrapRightIter M n * M.wrap_left

lemma eval_succIter {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    ∀ n t, M.eval (succIterOn S n t) = succConst M n + M.succ_scale ^ n * M.eval t
  | 0, t => by simp [succIterOn, succConst]
  | n + 1, t => by
      rw [succIterOn, M.eval_succ, eval_succIter M n t, succConst, Nat.pow_succ]
      ring

lemma eval_wrapNest {S : StepDuplicatingSchema} (M : AffineMeasure S) (s : S.T) :
    ∀ n t,
      M.eval (wrapNest S s n t) =
        wrapConstIter M n + wrapLeftIter M n * M.eval s + wrapRightIter M n * M.eval t
  | 0, t => by
      simp [wrapNest, wrapConstIter, wrapLeftIter, wrapRightIter]
  | n + 1, t => by
      rw [wrapNest, eval_wrapNest M s n (S.wrap s t), M.eval_wrap]
      simp [wrapConstIter, wrapLeftIter, wrapRightIter, Nat.mul_add, Nat.add_mul]
      ring

lemma wrapRightIter_pos {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    ∀ n, 1 ≤ wrapRightIter M n
  | 0 => by simp [wrapRightIter]
  | n + 1 => by
      simp [wrapRightIter]
      exact Nat.mul_le_mul (wrapRightIter_pos M n) M.h_wrap_right_pos

lemma wrapLeftIter_pos {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    ∀ n, 0 < n → 1 ≤ wrapLeftIter M n
  | 0, h => by cases Nat.not_lt_zero _ h
  | n + 1, _ => by
      have hterm : 1 ≤ wrapRightIter M n * M.wrap_left := by
        exact Nat.mul_le_mul (wrapRightIter_pos M n) M.h_wrap_left_pos
      have hsum : 1 ≤ wrapLeftIter M n + wrapRightIter M n * M.wrap_left := by
        exact le_trans hterm (Nat.le_add_left _ _)
      simpa [wrapLeftIter] using hsum

/-- Transport an affine measure to the one-cycle derived schema. -/
def toDupMeasure {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (copies : Nat) (hcopies : 0 < copies) :
    AffineMeasure (toDupSchema S copies) where
  eval := M.eval
  c_base := M.c_base
  succ_bias := AffineOps.succConst M copies
  succ_scale := M.succ_scale ^ copies
  wrap_const := AffineOps.wrapConstIter M copies
  wrap_left := AffineOps.wrapLeftIter M copies
  wrap_right := AffineOps.wrapRightIter M copies
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := by
    intro t
    simpa [toDupSchema] using AffineOps.eval_succIter M copies t
  eval_wrap := by
    intro x y
    simpa [toDupSchema] using AffineOps.eval_wrapNest M x copies y
  eval_recur := by
    intro b s n
    simpa [toDupSchema] using M.eval_recur b s n
  h_wrap_left_pos := by
    exact AffineOps.wrapLeftIter_pos M copies hcopies
  h_wrap_right_pos := by
    exact AffineOps.wrapRightIter_pos M copies

end AffineOps

/-- The delayed one-cycle profile also defeats any affine direct orienter, provided the
derived one-cycle schema admits the usual unbounded pump. -/
theorem no_affine_orients_cycle_composite_of_unbounded
    {S : StepDuplicatingSchema} (M : AffineMeasure S) {copies : Nat}
    (hcopies : 0 < copies)
    (hunbounded : HasUnboundedRange (AffineOps.toDupMeasure M copies hcopies)) :
    ¬ (∀ (b s n : S.T),
      M.eval (cycleTarget S copies b s n) <
        M.eval (cycleSource S copies b s n)) := by
  simpa [toDupSchema, cycleSource, cycleTarget, AffineOps.toDupMeasure] using
    (no_affine_orients_dup_step_of_unbounded
      (S := toDupSchema S copies)
      (M := AffineOps.toDupMeasure M copies hcopies) hunbounded)

/-- Any contextual relation realizing the delayed duplicate cycle is also blocked by the
affine barrier under the usual derived-schema unbounded-pump hypothesis. -/
theorem no_global_orients_ctx_affine_of_unbounded
    {S : StepDuplicatingSchema} {copies : Nat}
    (W : CycleWitness S copies) (M : AffineMeasure S)
    (hcopies : 0 < copies)
    (hunbounded : HasUnboundedRange (AffineOps.toDupMeasure M copies hcopies)) :
    ¬ GlobalOrientsCtx W M.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : S.T),
        M.eval (cycleTarget S copies b s n) <
          M.eval (cycleSource S copies b s n) := by
    intro b s n
    have horient : DependencyPairsFragment.GlobalOrients W.StepCtx M.eval (· < ·) := by
      intro a b hstep
      exact h hstep
    exact
      DependencyPairsFragment.transGen_drop
        (R := W.StepCtx) (m := M.eval) horient (W.cycle_realized b s n)
  exact no_affine_orients_cycle_composite_of_unbounded M hcopies hunbounded hcomp

namespace CompositionalOps

def succIterFn {S : StepDuplicatingSchema} (CM : CompositionalMeasure S) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => CM.c_succ (succIterFn CM n x)

def wrapNestFn {S : StepDuplicatingSchema} (CM : CompositionalMeasure S) :
    Nat → Nat → Nat → Nat
  | 0, _, y => y
  | n + 1, x, y => wrapNestFn CM n x (CM.c_wrap x y)

lemma eval_succIter {S : StepDuplicatingSchema} (CM : CompositionalMeasure S) :
    ∀ n t, CM.eval (succIterOn S n t) = succIterFn CM n (CM.eval t)
  | 0, t => by simp [succIterOn, succIterFn]
  | n + 1, t => by
      rw [succIterOn, CM.eval_succ, eval_succIter CM n t, succIterFn]

lemma eval_wrapNest {S : StepDuplicatingSchema} (CM : CompositionalMeasure S) (s : S.T) :
    ∀ n t, CM.eval (wrapNest S s n t) = wrapNestFn CM n (CM.eval s) (CM.eval t)
  | 0, t => by simp [wrapNest, wrapNestFn]
  | n + 1, t => by
      rw [wrapNest, eval_wrapNest CM s n (S.wrap s t), CM.eval_wrap, wrapNestFn]

lemma succIter_transparent_at_base {S : StepDuplicatingSchema}
    (CM : CompositionalMeasure S) (htrans : CM.c_succ CM.c_base = CM.c_base) :
    ∀ n, succIterFn CM n CM.c_base = CM.c_base
  | 0 => by simp [succIterFn]
  | n + 1 => by simp [succIterFn, succIter_transparent_at_base CM htrans n, htrans]

lemma wrapNestFn_gt_subterm1 {S : StepDuplicatingSchema} (CM : CompositionalMeasure S) :
    ∀ n x y, 0 < n → x < wrapNestFn CM n x y
  | 0, x, y, h => by cases Nat.not_lt_zero _ h
  | 1, x, y, _ => by simpa [wrapNestFn] using CM.wrap_subterm1 x y
  | n + 2, x, y, _ => by
      simpa [wrapNestFn] using
        wrapNestFn_gt_subterm1 CM (n + 1) x (CM.c_wrap x y) (Nat.succ_pos _)

lemma wrapNestFn_gt_subterm2 {S : StepDuplicatingSchema} (CM : CompositionalMeasure S) :
    ∀ n x y, 0 < n → y < wrapNestFn CM n x y
  | 0, x, y, h => by cases Nat.not_lt_zero _ h
  | 1, x, y, _ => by simpa [wrapNestFn] using CM.wrap_subterm2 x y
  | n + 2, x, y, _ => by
      have hbase : y < CM.c_wrap x y := CM.wrap_subterm2 x y
      have htail :
          CM.c_wrap x y < wrapNestFn CM (n + 1) x (CM.c_wrap x y) := by
        exact wrapNestFn_gt_subterm2 CM (n + 1) x (CM.c_wrap x y) (Nat.succ_pos _)
      simpa [wrapNestFn] using Nat.lt_trans hbase htail

/-- Transport a transparent-compositional measure to the one-cycle derived schema. -/
def toDupMeasure {S : StepDuplicatingSchema} (CM : CompositionalMeasure S)
    (copies : Nat) (hcopies : 0 < copies) :
    CompositionalMeasure (toDupSchema S copies) where
  eval := CM.eval
  c_base := CM.c_base
  c_succ := CompositionalOps.succIterFn CM copies
  c_wrap := CompositionalOps.wrapNestFn CM copies
  c_recur := CM.c_recur
  eval_base := CM.eval_base
  eval_succ := by
    intro t
    simpa [toDupSchema] using CompositionalOps.eval_succIter CM copies t
  eval_wrap := by
    intro x y
    simpa [toDupSchema] using CompositionalOps.eval_wrapNest CM x copies y
  eval_recur := by
    intro b s n
    simpa [toDupSchema] using CM.eval_recur b s n
  wrap_subterm1 := by
    intro x y
    exact CompositionalOps.wrapNestFn_gt_subterm1 CM copies x y hcopies
  wrap_subterm2 := by
    intro x y
    exact CompositionalOps.wrapNestFn_gt_subterm2 CM copies x y hcopies

end CompositionalOps

/-- A transparent-compositional measure also cannot orient the delayed one-cycle profile,
provided successor is transparent at the base point. -/
theorem no_compositional_orients_cycle_composite_transparent
    {S : StepDuplicatingSchema} (CM : CompositionalMeasure S) {copies : Nat}
    (hcopies : 0 < copies) (htrans : CM.c_succ CM.c_base = CM.c_base) :
    ¬ (∀ (b s n : S.T),
      CM.eval (cycleTarget S copies b s n) <
        CM.eval (cycleSource S copies b s n)) := by
  have htrans' :
      (CompositionalOps.toDupMeasure CM copies hcopies).c_succ
          (CompositionalOps.toDupMeasure CM copies hcopies).c_base =
        (CompositionalOps.toDupMeasure CM copies hcopies).c_base := by
    simpa [CompositionalOps.toDupMeasure] using
      CompositionalOps.succIter_transparent_at_base CM htrans copies
  simpa [toDupSchema, cycleSource, cycleTarget, CompositionalOps.toDupMeasure] using
    (no_compositional_orients_dup_step_transparent_succ
      (S := toDupSchema S copies)
      (CM := CompositionalOps.toDupMeasure CM copies hcopies) htrans')

/-- Any contextual relation realizing the delayed duplicate cycle is also blocked by the
transparent-compositional barrier. -/
theorem no_global_orients_ctx_compositional_transparent
    {S : StepDuplicatingSchema} {copies : Nat}
    (W : CycleWitness S copies) (CM : CompositionalMeasure S)
    (hcopies : 0 < copies) (htrans : CM.c_succ CM.c_base = CM.c_base) :
    ¬ GlobalOrientsCtx W CM.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : S.T),
        CM.eval (cycleTarget S copies b s n) <
          CM.eval (cycleSource S copies b s n) := by
    intro b s n
    have horient : DependencyPairsFragment.GlobalOrients W.StepCtx CM.eval (· < ·) := by
      intro a b hstep
      exact h hstep
    exact
      DependencyPairsFragment.transGen_drop
        (R := W.StepCtx) (m := CM.eval) horient (W.cycle_realized b s n)
  exact no_compositional_orients_cycle_composite_transparent CM hcopies htrans hcomp

/-- Generic scalar-projection lift for delayed-duplication cycles, using an affine barrier on
the derived one-cycle schema. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
    {S : StepDuplicatingSchema} {copies : Nat} {α : Type}
    (W : CycleWitness S copies) (μ : S.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A : AffineMeasure (toDupSchema S copies))
    (hπ : ∀ t : S.T, π (μ t) = A.eval t)
    (hunbounded : HasUnboundedRange A) :
    ¬ GlobalOrientsCtx W μ R := by
  intro h
  have hcomp :
      ∀ (b s n : S.T),
        A.eval (cycleTarget S copies b s n) <
          A.eval (cycleSource S copies b s n) := by
    intro b s n
    have horient :
        DependencyPairsFragment.GlobalOrients W.StepCtx (fun t => π (μ t)) (· < ·) := by
      intro a b hstep
      exact hproj (h hstep)
    have hlt :
        π (μ (cycleTarget S copies b s n)) <
          π (μ (cycleSource S copies b s n)) := by
      exact
        DependencyPairsFragment.transGen_drop
          (R := W.StepCtx) (m := fun t => π (μ t)) horient (W.cycle_realized b s n)
    simpa [hπ (cycleTarget S copies b s n), hπ (cycleSource S copies b s n)] using hlt
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := toDupSchema S copies) A hunbounded
      (by
        intro b s n
        simpa [toDupSchema, cycleSource, cycleTarget] using hcomp b s n)

end OperatorKO7.MutualDuplicationCycleFlow
