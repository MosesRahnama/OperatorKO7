import Mathlib.SetTheory.Ordinal.Notation

/-!
# Ordinal hierarchy prelude

This file provides the hierarchy definitions needed for a genuine
Moser--Weiermann-style extraction below `ε₀`. It is intentionally generic and
does not yet connect the hierarchies to the KO7 relations.
-/

namespace OperatorKO7.OrdinalHierarchy

open ONote

/-- Slow-growing hierarchy on ordinal notations below `ε₀`. -/
def slowGrowing : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), h =>
      have : a < o := by
        rw [lt_def, h.1]
        exact Order.lt_succ (ONote.repr a)
      fun i => slowGrowing a i + 1
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      slowGrowing (f i) i
  termination_by o => o

@[nolint unusedHavesSuffices]
theorem slowGrowing_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    slowGrowing o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => fun _ => 0
      | Sum.inl (some a), _ => fun i => slowGrowing a i + 1
      | Sum.inr f, _ => fun i => slowGrowing (f i) i := by
  subst x
  rw [slowGrowing]

theorem slowGrowing_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    slowGrowing o = fun _ => 0 := by
  rw [slowGrowing_def h]

theorem slowGrowing_succ (o : ONote) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    slowGrowing o = fun i => slowGrowing a i + 1 := by
  rw [slowGrowing_def h]

theorem slowGrowing_limit (o : ONote) {f} (h : fundamentalSequence o = Sum.inr f) :
    slowGrowing o = fun i => slowGrowing (f i) i := by
  rw [slowGrowing_def h]

@[simp] theorem slowGrowing_zero : slowGrowing 0 = fun _ => 0 :=
  slowGrowing_zero' _ rfl

@[simp] theorem slowGrowing_one : slowGrowing 1 = fun _ => 1 := by
  rw [@slowGrowing_succ 1 0 rfl]
  funext i
  simp

@[simp] theorem slowGrowing_two : slowGrowing 2 = fun _ => 2 := by
  rw [@slowGrowing_succ 2 1 rfl]
  funext i
  simp

/-- Cichon hierarchy on ordinal notations below `ε₀`. -/
def cichon : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), h =>
      have : a < o := by
        rw [lt_def, h.1]
        exact Order.lt_succ (ONote.repr a)
      fun i => Nat.succ (cichon a (i + 1))
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      Nat.succ (cichon (f i) (i + 1))
  termination_by o => o

@[nolint unusedHavesSuffices]
theorem cichon_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    cichon o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => fun _ => 0
      | Sum.inl (some a), _ => fun i => Nat.succ (cichon a (i + 1))
      | Sum.inr f, _ => fun i => Nat.succ (cichon (f i) (i + 1)) := by
  subst x
  rw [cichon]

theorem cichon_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    cichon o = fun _ => 0 := by
  rw [cichon_def h]

theorem cichon_succ (o : ONote) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    cichon o = fun i => Nat.succ (cichon a (i + 1)) := by
  rw [cichon_def h]

theorem cichon_limit (o : ONote) {f} (h : fundamentalSequence o = Sum.inr f) :
    cichon o = fun i => Nat.succ (cichon (f i) (i + 1)) := by
  rw [cichon_def h]

@[simp] theorem cichon_zero : cichon 0 = fun _ => 0 :=
  cichon_zero' _ rfl

@[simp] theorem cichon_one : cichon 1 = fun _ => 1 := by
  rw [@cichon_succ 1 0 rfl]
  funext i
  simp

@[simp] theorem cichon_two : cichon 2 = fun _ => 2 := by
  rw [@cichon_succ 2 1 rfl]
  funext i
  simp

end OperatorKO7.OrdinalHierarchy
