import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.DependencyPairs_Fragment

/-!
# Finite k-Node Delayed Duplication

This module generalizes the bounded two-node delayed-duplication SCC to a finite
cyclic family of `k + 1` recursors. One full cycle peels `k + 1` successors and
accumulates `k + 1` nested wrappers around the duplicated payload.

The file now treats the additive branch and the affine branch with the same
reduction pattern: exact cycle realization first, then reduction to the existing
schema-level barrier theorems.
-/

namespace OperatorKO7.MutualDuplicationKNode

open OperatorKO7.StepDuplicating
open OperatorKO7.DependencyPairsFragment

/-- Shared constructor interface for a finite cyclic SCC with `k + 1` recursors. -/
structure CyclicDupSchema (k : Nat) where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : Fin (k + 1) → T → T → T → T

namespace CyclicDupSchema

/-- Forget the cyclic index and expose the ordinary wrapper-pump interface. -/
def toPumpSchema {k : Nat} (S : CyclicDupSchema k) : StepDuplicatingSchema where
  T := S.T
  base := S.base
  succ := S.succ
  wrap := S.wrap
  recur := S.recur 0

/-- Wrapper-chain pump inherited from the ordinary duplication schema. -/
def wrapIter {k : Nat} (S : CyclicDupSchema k) : Nat → S.T :=
  StepDuplicatingSchema.wrapIter S.toPumpSchema

/-- Iterate the successor constructor. -/
def succIter {k : Nat} (S : CyclicDupSchema k) : Nat → S.T → S.T
  | 0, t => t
  | n + 1, t => S.succ (S.succIter n t)

/-- Repeatedly wrap the same payload on the left. The recursive orientation is
chosen so that lifting a contextual step through the wrapper chain is definitional. -/
def wrapNest {k : Nat} (S : CyclicDupSchema k) (s : S.T) : Nat → S.T → S.T
  | 0, t => t
  | n + 1, t => S.wrapNest s n (S.wrap s t)

/-- One full cycle advances the recursor index by `n` modulo `k + 1`. -/
def advance {k : Nat} (_S : CyclicDupSchema k) (i : Fin (k + 1)) (n : Nat) : Fin (k + 1) where
  val := (i.1 + n) % (k + 1)
  isLt := Nat.mod_lt _ (Nat.succ_pos _)

/-- One full SCC cycle peels `k + 1` successors. -/
def cycleSucc {k : Nat} (S : CyclicDupSchema k) (t : S.T) : S.T :=
  S.succIter (k + 1) t

/-- One full SCC cycle accumulates `k + 1` identical wrappers. -/
def cycleWrap {k : Nat} (S : CyclicDupSchema k) (s t : S.T) : S.T :=
  S.wrapNest s (k + 1) t

lemma advance_zero {k : Nat} (S : CyclicDupSchema k) (i : Fin (k + 1)) :
    S.advance i 0 = i := by
  ext
  simp [advance]

lemma advance_add {k : Nat} (S : CyclicDupSchema k) (i : Fin (k + 1)) (m n : Nat) :
    S.advance (S.advance i m) n = S.advance i (m + n) := by
  ext
  simp [advance, Nat.add_assoc, Nat.mod_add_mod]

lemma advance_cycleLen {k : Nat} (S : CyclicDupSchema k) (i : Fin (k + 1)) :
    S.advance i (k + 1) = i := by
  ext
  simp [advance]

/-- Uniform additive constructor-local measures on the cyclic SCC schema. -/
structure AdditiveMeasure {k : Nat} (S : CyclicDupSchema k) where
  eval : S.T → Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval S.base = w_base
  eval_succ : ∀ t, eval (S.succ t) = w_succ + eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ i b s n, eval (S.recur i b s n) = w_recur + eval b + eval s + eval n
  h_wrap_pos : 1 ≤ w_wrap

/-- Uniform affine constructor-local measures on the cyclic SCC schema. -/
structure AffineMeasure {k : Nat} (S : CyclicDupSchema k) where
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
  eval_recur :
    ∀ i b s n,
      eval (S.recur i b s n) =
        recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Derived one-cycle schema at a fixed SCC node. -/
def toDupKSchemaAt {k : Nat} (S : CyclicDupSchema k) (i : Fin (k + 1)) : StepDuplicatingSchema where
  T := S.T
  base := S.base
  succ := S.cycleSucc
  wrap := S.cycleWrap
  recur := S.recur i

/-- Convert the cyclic additive measure to the ordinary wrapper-pump measure. -/
def AdditiveMeasure.toPumpMeasure {k : Nat} {S : CyclicDupSchema k}
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
  eval_recur := M.eval_recur 0
  h_wrap_pos := M.h_wrap_pos

lemma eval_wrapIter_ge {k : Nat} {S : CyclicDupSchema k} (M : AdditiveMeasure S) (n : Nat) :
    M.eval (S.wrapIter n) ≥ n := by
  simpa [CyclicDupSchema.wrapIter, AdditiveMeasure.toPumpMeasure] using
    (StepDuplicatingSchema.eval_wrapIter_ge
      (S := S.toPumpSchema) (M := M.toPumpMeasure) n)

lemma eval_succIter {k : Nat} {S : CyclicDupSchema k} (M : AdditiveMeasure S) :
    ∀ n t, M.eval (S.succIter n t) = n * M.w_succ + M.eval t
  | 0, t => by simp [CyclicDupSchema.succIter]
  | n + 1, t => by
      rw [CyclicDupSchema.succIter, M.eval_succ, eval_succIter M n t]
      ring

lemma eval_wrapNest {k : Nat} {S : CyclicDupSchema k} (M : AdditiveMeasure S) :
    ∀ n s t, M.eval (S.wrapNest s n t) = n * M.w_wrap + n * M.eval s + M.eval t
  | 0, s, t => by simp [CyclicDupSchema.wrapNest]
  | n + 1, s, t => by
      rw [CyclicDupSchema.wrapNest, eval_wrapNest M n s (S.wrap s t), M.eval_wrap]
      ring

def AffineMeasure.succConst {k : Nat} {S : CyclicDupSchema k} (M : AffineMeasure S) : Nat → Nat
  | 0 => 0
  | n + 1 => M.succ_bias + M.succ_scale * M.succConst n

def AffineMeasure.wrapRightIter {k : Nat} {S : CyclicDupSchema k}
    (M : AffineMeasure S) : Nat → Nat
  | 0 => 1
  | n + 1 => M.wrapRightIter n * M.wrap_right

def AffineMeasure.wrapConstIter {k : Nat} {S : CyclicDupSchema k}
    (M : AffineMeasure S) : Nat → Nat
  | 0 => 0
  | n + 1 => M.wrapConstIter n + M.wrapRightIter n * M.wrap_const

def AffineMeasure.wrapLeftIter {k : Nat} {S : CyclicDupSchema k}
    (M : AffineMeasure S) : Nat → Nat
  | 0 => 0
  | n + 1 => M.wrapLeftIter n + M.wrapRightIter n * M.wrap_left

lemma eval_succIter_affine {k : Nat} {S : CyclicDupSchema k} (M : AffineMeasure S) :
    ∀ n t, M.eval (S.succIter n t) = M.succConst n + M.succ_scale ^ n * M.eval t
  | 0, t => by simp [CyclicDupSchema.succIter, AffineMeasure.succConst]
  | n + 1, t => by
      rw [CyclicDupSchema.succIter, M.eval_succ, eval_succIter_affine M n t,
        AffineMeasure.succConst, Nat.pow_succ]
      ring

lemma eval_wrapNest_affine {k : Nat} {S : CyclicDupSchema k} (M : AffineMeasure S) :
    ∀ n s t,
      M.eval (S.wrapNest s n t) =
        M.wrapConstIter n + M.wrapLeftIter n * M.eval s + M.wrapRightIter n * M.eval t
  | 0, s, t => by
      simp [CyclicDupSchema.wrapNest, AffineMeasure.wrapConstIter, AffineMeasure.wrapLeftIter,
        AffineMeasure.wrapRightIter]
  | n + 1, s, t => by
      rw [CyclicDupSchema.wrapNest, eval_wrapNest_affine M n s (S.wrap s t), M.eval_wrap]
      simp [AffineMeasure.wrapConstIter, AffineMeasure.wrapLeftIter, AffineMeasure.wrapRightIter,
        Nat.mul_add, Nat.add_mul]
      ring

lemma wrapRightIter_pos {k : Nat} {S : CyclicDupSchema k} (M : AffineMeasure S) :
    ∀ n, 1 ≤ M.wrapRightIter n
  | 0 => by simp [AffineMeasure.wrapRightIter]
  | n + 1 => by
      simp [AffineMeasure.wrapRightIter]
      exact Nat.mul_le_mul (wrapRightIter_pos M n) M.h_wrap_right_pos

lemma wrapLeftIter_pos {k : Nat} {S : CyclicDupSchema k} (M : AffineMeasure S) :
    ∀ n, 0 < n → 1 ≤ M.wrapLeftIter n
  | 0, h => by cases Nat.not_lt_zero _ h
  | n + 1, _ => by
      have hterm : 1 ≤ M.wrapRightIter n * M.wrap_left := by
        exact Nat.mul_le_mul (wrapRightIter_pos M n) M.h_wrap_left_pos
      have hsum : 1 ≤ M.wrapLeftIter n + M.wrapRightIter n * M.wrap_left := by
        exact le_trans hterm (Nat.le_add_left _ _)
      simpa [AffineMeasure.wrapLeftIter] using hsum

/-- Transport a cyclic affine measure to the one-cycle derived schema at node `i`. -/
def AffineMeasure.toDupKMeasureAt {k : Nat} {S : CyclicDupSchema k}
    (M : AffineMeasure S) (i : Fin (k + 1)) :
    StepDuplicatingSchema.AffineMeasure (S.toDupKSchemaAt i) where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succConst (k + 1)
  succ_scale := M.succ_scale ^ (k + 1)
  wrap_const := M.wrapConstIter (k + 1)
  wrap_left := M.wrapLeftIter (k + 1)
  wrap_right := M.wrapRightIter (k + 1)
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := by
    intro t
    simpa [CyclicDupSchema.toDupKSchemaAt, CyclicDupSchema.cycleSucc] using
      eval_succIter_affine M (k + 1) t
  eval_wrap := by
    intro x y
    simpa [CyclicDupSchema.toDupKSchemaAt, CyclicDupSchema.cycleWrap] using
      eval_wrapNest_affine M (k + 1) x y
  eval_recur := by
    intro b s n
    simpa [CyclicDupSchema.toDupKSchemaAt] using M.eval_recur i b s n
  h_wrap_left_pos := by
    exact wrapLeftIter_pos M (k + 1) (Nat.succ_pos _)
  h_wrap_right_pos := by
    exact wrapRightIter_pos M (k + 1)

/-- One full cyclic duplicate already defeats any additive direct orienter on the
derived composite profile. -/
theorem no_additive_orients_cyclic_dup_composite
    {k : Nat} {S : CyclicDupSchema k} (M : AdditiveMeasure S) :
    ¬ (∀ (i : Fin (k + 1)) (b s n : S.T),
      M.eval (S.cycleWrap s (S.recur i b s n)) <
        M.eval (S.recur i b s (S.cycleSucc n))) := by
  intro h
  let nodes := k + 1
  let sval := M.eval (S.wrapIter M.w_succ)
  have hspec := h 0 S.base (S.wrapIter M.w_succ) S.base
  have hspec' :
      nodes * M.w_wrap + nodes * sval +
          (M.w_recur + M.w_base + sval + M.w_base) <
        nodes * M.w_succ + (M.w_recur + M.w_base + sval + M.w_base) := by
    simpa [nodes, sval, CyclicDupSchema.cycleWrap, CyclicDupSchema.cycleSucc,
      M.eval_base, M.eval_recur, eval_wrapNest, eval_succIter,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hspec
  have hdrop : nodes * M.w_wrap + nodes * sval < nodes * M.w_succ := by
    exact Nat.lt_of_add_lt_add_right hspec'
  have hsval : M.w_succ ≤ sval := by
    simpa [sval] using eval_wrapIter_ge M M.w_succ
  have hnodes : 1 ≤ nodes := by
    omega
  have hmul : nodes * M.w_succ ≤ nodes * sval := by
    exact Nat.mul_le_mul_left _ hsval
  have hwrap : 1 ≤ nodes * M.w_wrap := by
    have hmul' : 1 * 1 ≤ nodes * M.w_wrap := Nat.mul_le_mul hnodes M.h_wrap_pos
    simpa using hmul'
  have hstrict : nodes * M.w_succ < nodes * M.w_wrap + nodes * sval := by
    have hplus : nodes * sval < nodes * M.w_wrap + nodes * sval := by
      exact Nat.lt_add_of_pos_left hwrap
    exact lt_of_le_of_lt hmul hplus
  exact Nat.not_lt_of_ge (Nat.le_of_lt hstrict) hdrop

/-- One full cyclic duplicate also defeats any affine direct orienter on the
derived composite profile at a fixed SCC node, provided the derived one-cycle
schema admits the usual unbounded pump. -/
theorem no_affine_orients_cyclic_dup_composite_of_unbounded
    {k : Nat} {S : CyclicDupSchema k} (M : AffineMeasure S) (i : Fin (k + 1))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (M.toDupKMeasureAt i)) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.cycleWrap s (S.recur i b s n)) <
        M.eval (S.recur i b s (S.cycleSucc n))) := by
  simpa [CyclicDupSchema.toDupKSchemaAt, CyclicDupSchema.cycleWrap, CyclicDupSchema.cycleSucc,
    AffineMeasure.toDupKMeasureAt] using
    (StepDuplicatingSchema.no_affine_orients_dup_step_of_unbounded
      (S := S.toDupKSchemaAt i) (M := M.toDupKMeasureAt i) hunbounded)

/-- A finite cyclic system whose delayed duplication appears only after one full SCC cycle. -/
structure CyclicDupSystem (k : Nat) extends CyclicDupSchema k where
  Step : T → T → Prop
  step_succ :
    ∀ (i : Fin (k + 1)) b s n,
      Step (recur i b s (succ n)) (wrap s (recur (toCyclicDupSchema.advance i 1) b s n))

/-- Minimal context closure needed for the SCC-cycle realization:
root steps plus reduction under the right wrapper argument. -/
inductive StepCtx {k : Nat} (Sys : CyclicDupSystem k) : Sys.T → Sys.T → Prop
| root : ∀ {a b}, Sys.Step a b → StepCtx Sys a b
| wrap_right : ∀ s {a b}, StepCtx Sys a b → StepCtx Sys (Sys.wrap s a) (Sys.wrap s b)

/-- Orientation of the finite cyclic relation under the minimal context closure. -/
def GlobalOrientsCtx {n : Nat} {α : Type} (Sys : CyclicDupSystem n) (m : Sys.T → α)
    (lt : α → α → Prop) : Prop :=
  ∀ {a b : Sys.T}, StepCtx Sys a b → lt (m b) (m a)

namespace CyclicDupSystem

lemma StepCtx.wrapNest_right {k : Nat} {Sys : CyclicDupSystem k}
    (s : Sys.T) :
    ∀ n {a b : Sys.T}, StepCtx Sys a b → StepCtx Sys (Sys.wrapNest s n a) (Sys.wrapNest s n b)
  | 0, a, b, h => h
  | n + 1, a, b, h => by
      simpa [CyclicDupSchema.wrapNest] using
        StepCtx.wrapNest_right (Sys := Sys) s n (StepCtx.wrap_right s h)

/-- The `r`-step residual phase of one cyclic SCC pass. -/
def phase {k : Nat} (Sys : CyclicDupSystem k) (i : Fin (k + 1))
    (b s n : Sys.T) (r : Nat) : Sys.T :=
  Sys.wrapNest s ((k + 1) - r)
    (Sys.recur (Sys.advance i ((k + 1) - r)) b s (Sys.succIter r n))

lemma phase_step {k : Nat} {Sys : CyclicDupSystem k} (i : Fin (k + 1))
    (b s n : Sys.T) {r : Nat} (hr : r < k + 1) :
    StepCtx Sys (phase Sys i b s n (r + 1)) (phase Sys i b s n r) := by
  have hroot :
      StepCtx Sys
        (Sys.recur (Sys.advance i ((k + 1) - (r + 1))) b s (Sys.succ (Sys.succIter r n)))
        (Sys.wrap s
          (Sys.recur (Sys.advance i (((k + 1) - (r + 1)) + 1)) b s (Sys.succIter r n))) := by
    apply StepCtx.root
    simpa [CyclicDupSchema.advance_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Sys.step_succ (Sys.advance i ((k + 1) - (r + 1))) b s (Sys.succIter r n)
  have hlift :=
      StepCtx.wrapNest_right (Sys := Sys) s ((k + 1) - (r + 1)) hroot
  have hcount : (k + 1) - r = (k - r) + 1 := by
    omega
  simpa [phase, CyclicDupSchema.wrapNest, CyclicDupSchema.succIter, hcount,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlift

/-- One full SCC cycle realizes the delayed duplicate for any starting node. -/
theorem cycle_realized {k : Nat} (Sys : CyclicDupSystem k) (i : Fin (k + 1))
    (b s n : Sys.T) :
    Relation.TransGen (StepCtx Sys)
      (Sys.recur i b s (Sys.cycleSucc n))
      (Sys.cycleWrap s (Sys.recur i b s n)) := by
  have hpath :
      ∀ m, m < k + 1 →
        Relation.TransGen (StepCtx Sys)
          (phase Sys i b s n (m + 1))
          (phase Sys i b s n 0) := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hstep : StepCtx Sys (phase Sys i b s n 1) (phase Sys i b s n 0) := by
          exact phase_step (Sys := Sys) i b s n (r := 0) hm
        simpa using Relation.TransGen.single hstep
    | succ m ih =>
        intro hm
        have hstep : StepCtx Sys (phase Sys i b s n (m + 2)) (phase Sys i b s n (m + 1)) := by
          exact phase_step (Sys := Sys) i b s n (r := m + 1) hm
        have htail :
            Relation.TransGen (StepCtx Sys)
              (phase Sys i b s n (m + 1))
              (phase Sys i b s n 0) := by
          exact ih (by omega)
        exact Relation.TransGen.trans (Relation.TransGen.single hstep) htail
  simpa [phase, CyclicDupSchema.cycleSucc, CyclicDupSchema.cycleWrap,
    CyclicDupSchema.advance_zero, CyclicDupSchema.advance_cycleLen] using
    hpath k (Nat.lt_succ_self k)

/-- The finite cyclic SCC theorem rules out any additive orientation of the whole
minimal-context relation, because that would force the composite duplicate to decrease. -/
theorem no_global_orients_ctx_additive
    {k : Nat} {Sys : CyclicDupSystem k} (M : AdditiveMeasure Sys.toCyclicDupSchema) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (i : Fin (k + 1)) (b s n : Sys.T),
        M.eval (Sys.cycleWrap s (Sys.recur i b s n)) <
          M.eval (Sys.recur i b s (Sys.cycleSucc n)) := by
    intro i b s n
    have horient : DependencyPairsFragment.GlobalOrients (StepCtx Sys) M.eval (· < ·) := by
      intro a b hstep
      exact h hstep
    exact
      DependencyPairsFragment.transGen_drop
        (R := StepCtx Sys) (m := M.eval) horient
        (cycle_realized Sys i b s n)
  exact no_additive_orients_cyclic_dup_composite (S := Sys.toCyclicDupSchema) M hcomp

/-- The finite cyclic SCC theorem also rules out affine orientation of the whole
minimal-context relation, provided the derived one-cycle schema at node `0`
admits the usual unbounded pump. -/
theorem no_global_orients_ctx_affine_of_unbounded
    {k : Nat} {Sys : CyclicDupSystem k} (M : AffineMeasure Sys.toCyclicDupSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (M.toDupKMeasureAt 0)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have hcomp :
      ∀ (b s n : Sys.T),
        M.eval (Sys.cycleWrap s (Sys.recur 0 b s n)) <
          M.eval (Sys.recur 0 b s (Sys.cycleSucc n)) := by
    intro b s n
    have horient : DependencyPairsFragment.GlobalOrients (StepCtx Sys) M.eval (· < ·) := by
      intro a b hstep
      exact h hstep
    exact
      DependencyPairsFragment.transGen_drop
        (R := StepCtx Sys) (m := M.eval) horient
        (cycle_realized Sys 0 b s n)
  exact
    no_affine_orients_cyclic_dup_composite_of_unbounded
      (S := Sys.toCyclicDupSchema) M 0 hunbounded hcomp

end CyclicDupSystem

end CyclicDupSchema

end OperatorKO7.MutualDuplicationKNode
