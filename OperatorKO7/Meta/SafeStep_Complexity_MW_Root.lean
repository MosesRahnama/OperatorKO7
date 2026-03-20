import OperatorKO7.Meta.NormalizeSafe_LowerBound
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal
import OperatorKO7.Meta.DM_OrderType
import OperatorKO7.Meta.DM_OrderType_LowerBound
import OperatorKO7.Meta.ContextClosed_SN
import OperatorKO7.Meta.OrdinalHierarchy
import OperatorKO7.Meta.OrdinalHierarchy_Control
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Multiset.Sort

/-!
# Root ordinal-notation bridge and Cichon bound for strict S142

This file builds the notation-level bridge from the existing ordinal calibration
`lex3cToOrd` to `ONote`/`NONote`, then closes the guarded root side with a genuine
`cichon` theorem on that note family.
-/

open OperatorKO7
open OperatorKO7.Trace
open scoped Classical
open Ordinal

namespace MetaSN_KO7

open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.OrdinalHierarchy
open ONote
open NONote

private noncomputable def dmAddOpOrd (n : Nat) (acc : Ordinal) : Ordinal :=
  (ω : Ordinal) ^ (n : Ordinal) + acc

@[simp] theorem repr_NONote_ofNat (n : Nat) :
    NONote.repr (NONote.ofNat n) = (n : Ordinal) := by
  change (ONote.ofNat n).repr = (n : Ordinal)
  exact ONote.repr_ofNat n

/-- A normal-form notation for `ω`. -/
def omegaNote : NONote :=
  ⟨ONote.oadd 1 1 0, by infer_instance⟩

/-- A normal-form notation for `ω^ω`. -/
def omegaPowOmegaNote : NONote :=
  NONote.opow omegaNote omegaNote

@[simp] theorem repr_omegaNote :
    NONote.repr omegaNote = (ω : Ordinal) := by
  change (ONote.oadd 1 1 0).repr = (ω : Ordinal)
  simp [ONote.repr]

@[simp] theorem repr_omegaPowOmegaNote :
    NONote.repr omegaPowOmegaNote = (ω : Ordinal) ^ (ω : Ordinal) := by
  unfold omegaPowOmegaNote
  rw [NONote.repr_opow, repr_omegaNote]

/-- Sorted-list notation for the DM multiset ordinal payload. -/
def dmNoteList : List Nat → NONote
  | [] => 0
  | n :: ns => NONote.opow omegaNote (NONote.ofNat n) + dmNoteList ns

/-- Canonical notation for the DM multiset payload. -/
def dmNote (m : Multiset Nat) : NONote :=
  dmNoteList (Multiset.sort (· ≥ ·) m)

@[simp] theorem repr_dmNoteList : ∀ l : List Nat,
    NONote.repr (dmNoteList l) = l.foldr dmAddOpOrd 0
  | [] => by
      rfl
  | n :: ns => by
      simp [dmNoteList, repr_dmNoteList ns, dmAddOpOrd, NONote.repr_add, NONote.repr_opow,
        repr_omegaNote, repr_NONote_ofNat]

theorem repr_dmNote (m : Multiset Nat) :
    NONote.repr (dmNote m) = dmOrdEmbed m := by
  let l : List Nat := Multiset.sort (fun x y : Nat => x ≥ y) m
  unfold dmNote
  rw [repr_dmNoteList]
  unfold MetaDM.dmOrdEmbed
  change List.foldr dmAddOpOrd 0 l =
    List.foldr (fun (n : Nat) (acc : Ordinal) => (ω : Ordinal) ^ (n : Ordinal) + acc) 0 l
  induction l with
  | nil =>
      rfl
  | cons n ns ih =>
      simp [dmAddOpOrd, ih]

/-- Notation for the middle lexicographic layer `ω * dmOrdEmbed κ + τ`. -/
def lexDMNote (p : Multiset Nat × Nat) : NONote :=
  omegaNote * dmNote p.1 + NONote.ofNat p.2

theorem repr_lexDMNote (p : Multiset Nat × Nat) :
    NONote.repr (lexDMNote p) = lexDMToOrd p := by
  rcases p with ⟨κ, τ⟩
  simp [lexDMNote, lexDMToOrd, repr_dmNote, NONote.repr_add, NONote.repr_mul,
    repr_NONote_ofNat, repr_omegaNote]

/-- Notation for the full triple-lex ordinal `ω^ω * δ + lexDM`. -/
def lex3Note (x : Nat × (Multiset Nat × Nat)) : NONote :=
  omegaPowOmegaNote * NONote.ofNat x.1 + lexDMNote x.2

theorem repr_lex3Note (x : Nat × (Multiset Nat × Nat)) :
    NONote.repr (lex3Note x) = lex3cToOrd x := by
  rcases x with ⟨δ, p⟩
  simp [lex3Note, lex3cToOrd, repr_lexDMNote, NONote.repr_add, NONote.repr_mul,
    repr_NONote_ofNat, repr_omegaPowOmegaNote]

/-- Root-side note used by the guarded MW extraction. -/
def mwRootNote (t : Trace) : NONote :=
  lex3Note (mu3c t)

theorem repr_mwRootNote (t : Trace) :
    NONote.repr (mwRootNote t) = lex3cToOrd (mu3c t) := by
  simp [mwRootNote, repr_lex3Note]

/-- The guarded root note remains inside the calibrated `ω^ω * 2` block. -/
theorem mwRootNote_lt_opow_omega_mul_two (t : Trace) :
    NONote.repr (mwRootNote t) < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) := by
  rw [repr_mwRootNote]
  have hδ : deltaFlag t ≤ 1 := by
    rcases deltaFlag_range t with h0 | h1 <;> omega
  exact lex3cToOrd_lt_opow_omega_mul_two hδ

/-- If a normal-form note denotes a successor ordinal, its fundamental sequence exposes
    the corresponding predecessor note. -/
private theorem fundamentalSequence_eq_succ_of_repr_succ {o a : ONote}
    (ho : o.NF) (ha : a.NF) (h : o.repr = Order.succ a.repr) :
    fundamentalSequence o = Sum.inl (some a) := by
  cases hfs : fundamentalSequence o with
  | inl opt =>
      cases opt with
      | none =>
          exfalso
          have hprop := fundamentalSequence_has_prop o
          rw [hfs, fundamentalSequenceProp_inl_none] at hprop
          subst hprop
          exact Ordinal.succ_ne_zero _ h.symm
      | some b =>
          have hprop := fundamentalSequence_has_prop o
          rw [hfs, fundamentalSequenceProp_inl_some] at hprop
          rcases hprop with ⟨hb, hbNF⟩
          have hEqRepr : b.repr = a.repr := by
            apply Order.succ_injective
            simpa [h] using hb.symm
          have hbNF' : b.NF := hbNF ho
          have hb' : b = a := (ONote.repr_inj (a := b) (b := a)).1 hEqRepr
          cases hb'
          rfl
  | inr f =>
      exfalso
      have hprop := fundamentalSequence_has_prop o
      rw [hfs, fundamentalSequenceProp_inr] at hprop
      exact hprop.1.succ_ne _ h.symm

/-- The finite `τ` payload makes every note in the `lex3Note` family with tail `τ+1`
    a successor ordinal with predecessor obtained by decreasing that tail by one. -/
theorem fundamentalSequence_lex3Note_succ (δ τ : Nat) (κ : Multiset Nat) :
    fundamentalSequence (lex3Note (δ, (κ, τ + 1))).1 =
      Sum.inl (some (lex3Note (δ, (κ, τ))).1) := by
  apply fundamentalSequence_eq_succ_of_repr_succ
  · infer_instance
  · infer_instance
  · change NONote.repr (lex3Note (δ, (κ, τ + 1))) =
        Order.succ (NONote.repr (lex3Note (δ, (κ, τ))))
    rw [repr_lex3Note, repr_lex3Note]
    simp [lex3cToOrd, lexDMToOrd, Ordinal.add_succ]

/-- Every `SafeStep` source has positive finite `τ` payload. -/
theorem tau_pos_of_safeStep_source {a b : Trace} (h : SafeStep a b) : 0 < tau a := by
  cases h <;> simp [tau]

/-- The note attached to any guarded root source is a successor note whose predecessor
    is obtained by decreasing the `τ` tail by one. -/
theorem safeStep_source_fundamentalSequence {a b : Trace} (h : SafeStep a b) :
    fundamentalSequence (lex3Note (mu3c a)).1 =
      Sum.inl (some (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1) := by
  have hτ : 0 < tau a := tau_pos_of_safeStep_source h
  have hs : tau a = (tau a - 1) + 1 := by
    simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hτ).symm
  change fundamentalSequence (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a))).1 =
    Sum.inl (some (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1)
  rw [hs]
  simpa using
    fundamentalSequence_lex3Note_succ (deltaFlag a) (tau a - 1) (MetaSN_DM.kappaM a)

/-- One exact controlled-descent step from a guarded root source to its explicit predecessor. -/
theorem safeStep_source_exact_pred_step {a b : Trace} (h : SafeStep a b) :
    ExactControlledPow (lex3Note (mu3c a)).1 (ctxFuel a) 1
      (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1) := by
  refine ExactControlledPow.succ (hfs := safeStep_source_fundamentalSequence h) ?_
  simpa using
    ExactControlledPow.refl (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))).1 (ctxFuel a + 1)

/-- Every guarded root target lies at or below the explicit predecessor note of its source. -/
theorem safeStep_target_repr_le_source_pred {a b : Trace} (h : SafeStep a b) :
    NONote.repr (lex3Note (mu3c b)) ≤
      NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))) := by
  have hτ : 0 < tau a := tau_pos_of_safeStep_source h
  have hs : NONote.repr (lex3Note (mu3c a)) =
      Order.succ (NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1)))) := by
    change NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a))) =
      Order.succ (NONote.repr (lex3Note (deltaFlag a, (MetaSN_DM.kappaM a, tau a - 1))))
    have htau : tau a = (tau a - 1) + 1 := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hτ).symm
    rw [htau, repr_lex3Note, repr_lex3Note]
    simp [lex3cToOrd, lexDMToOrd, Ordinal.add_succ]
  have hlt : NONote.repr (lex3Note (mu3c b)) < NONote.repr (lex3Note (mu3c a)) := by
    rw [repr_lex3Note, repr_lex3Note]
    exact safeMeasure_strictMono_explicit h
  rw [hs] at hlt
  exact (Order.lt_succ_iff).mp hlt

/-- Repeated exact predecessor descent through the finite `τ` tail of a `lex3Note`. -/
theorem exactControlledPow_tau_drop (δ τ m k : Nat) (κ : Multiset Nat) :
    ExactControlledPow (lex3Note (δ, (κ, τ + m))).1 k m
      (lex3Note (δ, (κ, τ))).1 (k + m) := by
  induction m generalizing k with
  | zero =>
      simpa using ExactControlledPow.refl (lex3Note (δ, (κ, τ))).1 k
  | succ m ih =>
      have hfs :
          fundamentalSequence (lex3Note (δ, (κ, τ + m + 1))).1 =
            Sum.inl (some (lex3Note (δ, (κ, τ + m))).1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          fundamentalSequence_lex3Note_succ δ (τ + m) κ
      refine ExactControlledPow.succ (hfs := hfs) ?_
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k := k + 1)

/-- The notation-level root bound candidate for the strict MW extraction. -/
def mwRootBound (t : Trace) : Nat :=
  OperatorKO7.OrdinalHierarchy.cichon (mwRootNote t).1 (ctxFuel t)

/-- Any exact-length root chain is bounded by the computable tail measure `τ`.

For root reduction, the only constructor that can increase `τ` is `rec_succ`,
but its target is an `app` term, and `app` admits no further root reduction.
All other constructors either end immediately or strictly decrease `τ`. -/
theorem safeStepPow_length_le_tau :
    ∀ {t u : Trace} {n : Nat}, SafeStepPow t n u → n ≤ tau t
  | _, _, _, SafeStepPow.refl t => by
      simp
  | _, _, _, SafeStepPow.tail hab hbc => by
      cases hab with
      | R_int_delta t =>
          cases hbc with
          | refl _ =>
              simp [tau]
          | tail hnext _ =>
              cases hnext
      | R_merge_void_left t hδ =>
          have ih := safeStepPow_length_le_tau hbc
          simp [tau] at ih ⊢
          omega
      | R_merge_void_right t hδ =>
          have ih := safeStepPow_length_le_tau hbc
          simp [tau] at ih ⊢
          omega
      | R_merge_cancel t hδ h0 =>
          have ih := safeStepPow_length_le_tau hbc
          simp [tau] at ih ⊢
          omega
      | R_rec_zero b s hδ =>
          have ih := safeStepPow_length_le_tau hbc
          simp [tau] at ih ⊢
          omega
      | R_rec_succ b s n =>
          cases hbc with
          | refl _ =>
              simp [tau]
              omega
          | tail hnext _ =>
              cases hnext
      | R_eq_refl a h0 =>
          cases hbc with
          | refl _ =>
              simp [tau]
              omega
          | tail hnext _ =>
              cases hnext
      | R_eq_diff a b hne =>
          cases hbc with
          | refl _ =>
              simp [tau]
              omega
          | tail hnext _ =>
              cases hnext

/-- The finite `τ` tail already furnishes an exact controlled descent of length `τ`. -/
theorem tau_le_mwRootBound (t : Trace) :
    tau t ≤ mwRootBound t := by
  unfold mwRootBound
  simpa [mu3c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (OperatorKO7.OrdinalHierarchy.exactControlledPow_length_le_cichon
      (exactControlledPow_tau_drop
        (δ := deltaFlag t) (τ := 0) (m := tau t) (k := ctxFuel t) (κ := MetaSN_DM.kappaM t)))

/-- Root derivation lengths are bounded by the notation-level MW candidate already in the repo.

This does not solve the full strict S142 route for the context-closed relation, but it does
close the root side with a genuine `cichon` theorem. -/
theorem safeStepPow_length_le_mwRootBound {t u : Trace} {n : Nat}
    (h : SafeStepPow t n u) :
    n ≤ mwRootBound t := by
  exact le_trans (safeStepPow_length_le_tau h) (tau_le_mwRootBound t)

end MetaSN_KO7
