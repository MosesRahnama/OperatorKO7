import OperatorKO7.Kernel
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.WellFounded

/-!
Core SafeStep infrastructure used by the canonical computable termination path.

This file is intentionally minimal and self-contained:
- `MetaSN_DM`: computable multiset toolkit (`weight`, `kappaM`, DM lemmas)
- `MetaSN_KO7`: `deltaFlag`, guarded relation `SafeStep`, and `SafeStepRev`

No ordinal payloads or external termination frameworks are imported here.
-/

open OperatorKO7 Trace Multiset

namespace MetaSN_DM

local infix:70 " <ₘ " => Multiset.IsDershowitzMannaLT

/-- Weight of a trace: recursion-depth payload at `recΔ` heads. -/
@[simp] def weight : Trace → Nat
| recΔ _ _ n => weight n + 1
| _          => 0

/-- DM multiset payload for KO7 traces. -/
@[simp] def kappaM : Trace → Multiset Nat
| void            => 0
| delta t         => kappaM t
| integrate t     => kappaM t
| merge a b       => kappaM a ∪ kappaM b
| app   a b       => kappaM a ∪ kappaM b
| recΔ b s n      => (weight n + 1) ::ₘ (kappaM n ∪ kappaM s) + kappaM b
| eqW  a b        => kappaM a ∪ kappaM b

instance : WellFoundedLT Nat := inferInstance

/-- Well-foundedness of Dershowitz-Manna order on multisets of naturals. -/
lemma wf_dm : WellFounded (fun a b : Multiset Nat => a <ₘ b) :=
  Multiset.wellFounded_isDershowitzMannaLT

@[simp] lemma kappaM_int_delta (t : Trace) :
    kappaM (integrate (delta t)) = kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_merge_void_left (t : Trace) :
    kappaM (merge void t) = kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_merge_void_right (t : Trace) :
    kappaM (merge t void) = kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_merge_cancel (t : Trace) :
    kappaM (merge t t) = kappaM t ∪ kappaM t := by
  simp [kappaM]

@[simp] lemma kappaM_rec_zero (b s : Trace) :
    kappaM (recΔ b s void) = (1 ::ₘ kappaM s) + kappaM b := by
  simp [kappaM]

@[simp] lemma kappaM_eq_refl (a : Trace) :
    kappaM (eqW a a) = kappaM a ∪ kappaM a := by
  simp [kappaM]

@[simp] lemma kappaM_eq_diff (a b : Trace) :
    kappaM (integrate (merge a b)) = kappaM (eqW a b) := by
  simp [kappaM]

lemma dm_lt_add_of_ne_zero (X Z : Multiset Nat) (h : Z ≠ 0) :
    X <ₘ (X + Z) := by
  classical
  refine ⟨X, (0 : Multiset Nat), Z, ?hZ, ?hM, rfl, ?hY⟩
  · simpa using h
  · simp
  · simp

lemma dm_lt_add_of_ne_zero' (X Z : Multiset Nat) (h : Z ≠ 0) :
    Multiset.IsDershowitzMannaLT X (X + Z) := by
  classical
  refine ⟨X, (0 : Multiset Nat), Z, ?hZ, ?hM, rfl, ?hY⟩
  · simpa using h
  · simp
  · simp

lemma dm_drop_R_rec_zero (b s : Trace) :
    kappaM b <ₘ kappaM (recΔ b s void) := by
  classical
  have hdm : Multiset.IsDershowitzMannaLT (kappaM b) (kappaM b + (1 ::ₘ kappaM s)) :=
    dm_lt_add_of_ne_zero' (kappaM b) (1 ::ₘ kappaM s) (by simp)
  simpa [kappaM, add_comm, add_left_comm, add_assoc] using hdm

lemma union_self_ne_zero_of_ne_zero {X : Multiset Nat} (h : X ≠ 0) :
    X ∪ X ≠ (0 : Multiset Nat) := by
  classical
  intro hU
  have hUU : X ∪ X = X := by
    ext a
    simp [Multiset.count_union, max_self]
  exact h (by simpa [hUU] using hU)

end MetaSN_DM

namespace MetaSN_KO7

open MetaSN_DM

@[simp] def deltaFlag : Trace → Nat
| recΔ _ _ (delta _) => 1
| _                  => 0

@[simp] lemma deltaFlag_void : deltaFlag void = 0 := rfl
@[simp] lemma deltaFlag_integrate (t : Trace) : deltaFlag (integrate t) = 0 := rfl
@[simp] lemma deltaFlag_merge (a b : Trace) : deltaFlag (merge a b) = 0 := rfl
@[simp] lemma deltaFlag_eqW (a b : Trace) : deltaFlag (eqW a b) = 0 := rfl
@[simp] lemma deltaFlag_app (a b : Trace) : deltaFlag (app a b) = 0 := rfl
@[simp] lemma deltaFlag_rec_zero (b s : Trace) : deltaFlag (recΔ b s void) = 0 := by
  simp [deltaFlag]
@[simp] lemma deltaFlag_rec_delta (b s n : Trace) : deltaFlag (recΔ b s (delta n)) = 1 := by
  simp [deltaFlag]

lemma deltaFlag_range (t : Trace) : deltaFlag t = 0 ∨ deltaFlag t = 1 := by
  cases t with
  | void => simp
  | delta t => simp
  | integrate t => simp
  | merge a b => simp
  | app a b => simp
  | recΔ b s n =>
      cases n with
      | void => simp [deltaFlag]
      | delta n => simp [deltaFlag]
      | integrate t => simp [deltaFlag]
      | merge a b => simp [deltaFlag]
      | app a b => simp [deltaFlag]
      | eqW a b => simp [deltaFlag]
      | recΔ b s n => simp [deltaFlag]
  | eqW a b => simp

/-- Guarded subrelation used by the canonical termination development. -/
inductive SafeStep : Trace → Trace → Prop
| R_int_delta (t) : SafeStep (integrate (delta t)) void
| R_merge_void_left (t) (hδ : deltaFlag t = 0) : SafeStep (merge void t) t
| R_merge_void_right (t) (hδ : deltaFlag t = 0) : SafeStep (merge t void) t
| R_merge_cancel (t) (hδ : deltaFlag t = 0) (h0 : kappaM t = 0) : SafeStep (merge t t) t
| R_rec_zero (b s) (hδ : deltaFlag b = 0) : SafeStep (recΔ b s void) b
| R_rec_succ (b s n) : SafeStep (recΔ b s (delta n)) (app s (recΔ b s n))
| R_eq_refl (a) (h0 : kappaM a = 0) : SafeStep (eqW a a) void
| R_eq_diff (a b) (hne : a ≠ b) : SafeStep (eqW a b) (integrate (merge a b))

/-- Reverse relation for strong-normalization statements. -/
def SafeStepRev : Trace → Trace → Prop := fun a b => SafeStep b a

end MetaSN_KO7

