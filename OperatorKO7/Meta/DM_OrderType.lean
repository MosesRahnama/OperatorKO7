import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Data.Finset.Max
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.UnionInter
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.NaturalOps
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Veblen

/-!
# DM Order-Type Calibration

This file provides an ordinal calibration layer for the KO7 computable measure stack.
It proves strict monotonicity, order reflection, and the `ω^ω` upper bound for the
DM multiset embedding `dmOrdEmbed`, together with the `ω^ω · 2` trace-level bound
and the `ε₀` bridge for the triple-lex measure `mu3c`. The exact `ω^ω` order-type
isomorphism (surjectivity + reflection) is completed in `DM_OrderType_LowerBound.lean`.
-/

namespace OperatorKO7.MetaDM

set_option linter.unnecessarySimpa false

open OperatorKO7
open OperatorKO7.MetaCM
open Trace
open MetaSN_DM
open MetaSN_KO7
open scoped Classical
open Ordinal

/-! ## DM embedding (computable ordinal payload) -/

/-- Fold operator for sorted CNF-style embedding. -/
private noncomputable def dmAddOp (n : Nat) (acc : Ordinal.{0}) : Ordinal.{0} :=
  ((ω : Ordinal) ^ (n : Ordinal)) + acc

/-- Embed a multiset of naturals as a finite sorted ordinal sum of `ω^n` terms. -/
noncomputable def dmOrdEmbed (m : Multiset Nat) : Ordinal.{0} :=
  (Multiset.sort (· ≥ ·) m).foldr dmAddOp 0

private lemma dmOrdEmbed_list_foldr_add (l : List Nat) (b : Ordinal.{0}) :
    l.foldr dmAddOp b = l.foldr dmAddOp 0 + b := by
  induction l with
  | nil =>
      simp
  | cons n l ih =>
      simpa [dmAddOp, ih, add_assoc]

private lemma sort_ge_append_of_all_ge {s t : Multiset Nat}
    (hsep : ∀ a ∈ s, ∀ b ∈ t, a ≥ b) :
    Multiset.sort (· ≥ ·) (s + t) =
      Multiset.sort (· ≥ ·) s ++ Multiset.sort (· ≥ ·) t := by
  refine List.eq_of_perm_of_sorted (r := (· ≥ ·)) ?_ ?_ ?_
  · apply (Multiset.coe_eq_coe).1
    calc
      ((Multiset.sort (· ≥ ·) (s + t) : List Nat) : Multiset Nat)
          = s + t := Multiset.sort_eq (r := (· ≥ ·)) (s + t)
      _ = ((Multiset.sort (· ≥ ·) s : List Nat) : Multiset Nat) +
            ((Multiset.sort (· ≥ ·) t : List Nat) : Multiset Nat) := by
            simpa [Multiset.sort_eq]
      _ = ((Multiset.sort (· ≥ ·) s ++ Multiset.sort (· ≥ ·) t : List Nat) : Multiset Nat) := by
            simpa using
              (Multiset.coe_add (Multiset.sort (· ≥ ·) s) (Multiset.sort (· ≥ ·) t))
  · exact Multiset.sort_sorted (r := (· ≥ ·)) (s + t)
  ·
    exact (List.pairwise_append.2 ⟨
      Multiset.sort_sorted (r := (· ≥ ·)) s,
      Multiset.sort_sorted (r := (· ≥ ·)) t,
      by
        intro a ha b hb
        exact hsep a ((Multiset.mem_sort (r := (· ≥ ·))).1 ha)
          b ((Multiset.mem_sort (r := (· ≥ ·))).1 hb)⟩)

private lemma dmOrdEmbed_add_of_separated {s t : Multiset Nat}
    (hsep : ∀ a ∈ s, ∀ b ∈ t, a ≥ b) :
    dmOrdEmbed (s + t) = dmOrdEmbed s + dmOrdEmbed t := by
  unfold dmOrdEmbed
  rw [sort_ge_append_of_all_ge hsep, List.foldr_append, dmOrdEmbed_list_foldr_add]

private lemma dmOrdEmbed_cons_of_ge_all {a : Nat} {s : Multiset Nat}
    (h : ∀ b ∈ s, a ≥ b) :
    dmOrdEmbed (a ::ₘ s) = (ω : Ordinal) ^ (a : Ordinal) + dmOrdEmbed s := by
  unfold dmOrdEmbed
  rw [Multiset.sort_cons (r := (· ≥ ·)) a s h]
  simp [dmAddOp]

lemma dmOrdEmbed_replicate (z c : Nat) :
    dmOrdEmbed (Multiset.replicate c z) =
      (ω : Ordinal) ^ (z : Ordinal) * (c : Ordinal) := by
  induction c with
  | zero =>
      simp [dmOrdEmbed]
  | succ c ih =>
      have hge : ∀ b ∈ Multiset.replicate c z, z ≥ b := by
        intro b hb
        simpa [Multiset.eq_of_mem_replicate hb]
      calc
        dmOrdEmbed (Multiset.replicate (Nat.succ c) z)
            = dmOrdEmbed (z ::ₘ Multiset.replicate c z) := by
                simp [Multiset.replicate_succ]
        _ = (ω : Ordinal) ^ (z : Ordinal) + dmOrdEmbed (Multiset.replicate c z) :=
              dmOrdEmbed_cons_of_ge_all hge
        _ = (ω : Ordinal) ^ (z : Ordinal) +
              ((ω : Ordinal) ^ (z : Ordinal) * (c : Ordinal)) := by
                rw [ih]
        _ = (ω : Ordinal) ^ (z : Ordinal) * (Nat.succ c : Ordinal) := by
                calc
                  (ω : Ordinal) ^ (z : Ordinal) +
                      ((ω : Ordinal) ^ (z : Ordinal) * (c : Ordinal))
                      = (ω : Ordinal) ^ (z : Ordinal) + c • ((ω : Ordinal) ^ (z : Ordinal)) := by
                          rw [Ordinal.smul_eq_mul]
                  _ = (Nat.succ c) • ((ω : Ordinal) ^ (z : Ordinal)) := by
                        simpa using (succ_nsmul' ((ω : Ordinal) ^ (z : Ordinal)) c).symm
                  _ = (ω : Ordinal) ^ (z : Ordinal) * (Nat.succ c : Ordinal) := by
                        rw [Ordinal.smul_eq_mul]

lemma dmOrdEmbed_replicate_add_of_all_lt {z c : Nat} {low : Multiset Nat}
    (hlow : ∀ n ∈ low, n < z) :
    dmOrdEmbed (Multiset.replicate c z + low) =
      (ω : Ordinal) ^ (z : Ordinal) * (c : Ordinal) + dmOrdEmbed low := by
  have hsep : ∀ a ∈ Multiset.replicate c z, ∀ b ∈ low, a ≥ b := by
    intro a ha b hb
    have ha' : a = z := Multiset.eq_of_mem_replicate ha
    subst ha'
    exact Nat.le_of_lt (hlow b hb)
  calc
    dmOrdEmbed (Multiset.replicate c z + low)
        = dmOrdEmbed (Multiset.replicate c z) + dmOrdEmbed low :=
          dmOrdEmbed_add_of_separated hsep
    _ = (ω : Ordinal) ^ (z : Ordinal) * (c : Ordinal) + dmOrdEmbed low := by
          rw [dmOrdEmbed_replicate]

private lemma dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le
    {m : Multiset Nat} {z : Nat} (hle : ∀ n ∈ m, n ≤ z) :
    dmOrdEmbed m =
      (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m : Ordinal) +
        dmOrdEmbed (m.filter (fun n => n < z)) := by
  have hDecomp :
      m = m.filter (Eq z) + m.filter (fun n => ¬ z = n) := by
    simpa [add_comm] using (Multiset.filter_add_not (p := Eq z) m).symm
  have hNeEqLt :
      m.filter (fun n => ¬ z = n) = m.filter (fun n => n < z) := by
    refine Multiset.filter_congr ?_
    intro n hn
    constructor
    · intro hne
      exact lt_of_le_of_ne (hle n hn) (by simpa [eq_comm] using hne)
    · intro hlt
      exact (by simpa [eq_comm] using (ne_of_lt hlt))
  have hEqRep : m.filter (Eq z) = Multiset.replicate (Multiset.count z m) z := by
    simpa using (Multiset.filter_eq m z)
  have hLow : ∀ n ∈ m.filter (fun n => n < z), n < z := by
    intro n hn
    exact (Multiset.mem_filter.1 hn).2
  calc
    dmOrdEmbed m
        = dmOrdEmbed (m.filter (Eq z) + m.filter (fun n => ¬ z = n)) := by
            exact congrArg dmOrdEmbed hDecomp
    _ = dmOrdEmbed (Multiset.replicate (Multiset.count z m) z + m.filter (fun n => n < z)) := by
          rw [hEqRep, hNeEqLt]
    _ = (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m : Ordinal) +
          dmOrdEmbed (m.filter (fun n => n < z)) :=
          dmOrdEmbed_replicate_add_of_all_lt hLow

private lemma dmOrdEmbed_list_lt_opow_omega :
    ∀ l : List Nat, l.foldr dmAddOp 0 < (ω : Ordinal) ^ (ω : Ordinal)
  | [] => by
      simpa [dmAddOp] using
        (Ordinal.opow_pos (a := (ω : Ordinal)) (b := (ω : Ordinal)) Ordinal.omega0_pos)
  | n :: l => by
      have ih : l.foldr dmAddOp 0 < (ω : Ordinal) ^ (ω : Ordinal) :=
        dmOrdEmbed_list_lt_opow_omega l
      have hpow : (ω : Ordinal) ^ (n : Ordinal) < (ω : Ordinal) ^ (ω : Ordinal) := by
        exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
          (Ordinal.nat_lt_omega0 n)
      have hlt :
          (ω : Ordinal) ^ (n : Ordinal) + l.foldr dmAddOp 0 <
            (ω : Ordinal) ^ (n : Ordinal) + (ω : Ordinal) ^ (ω : Ordinal) := by
        exact add_lt_add_left ih ((ω : Ordinal) ^ (n : Ordinal))
      exact lt_of_lt_of_eq hlt (Ordinal.add_omega0_opow hpow)

private lemma dmOrdEmbed_list_lt_opow_of_forall_lt :
    ∀ (k : Nat) (l : List Nat),
      (∀ n ∈ l, n < k) → l.foldr dmAddOp 0 < (ω : Ordinal) ^ (k : Ordinal)
  | k, [], _ => by
      simpa [dmAddOp] using
        (Ordinal.opow_pos (a := (ω : Ordinal)) (b := (k : Ordinal)) Ordinal.omega0_pos)
  | k, n :: l, hltAll => by
      have hn : n < k := hltAll n (by simp)
      have hltTail : ∀ m ∈ l, m < k := by
        intro m hm
        exact hltAll m (by simp [hm])
      have ih : l.foldr dmAddOp 0 < (ω : Ordinal) ^ (k : Ordinal) :=
        dmOrdEmbed_list_lt_opow_of_forall_lt k l hltTail
      have hkOrd : (n : Ordinal) < (k : Ordinal) := by
        exact_mod_cast hn
      have hpow : (ω : Ordinal) ^ (n : Ordinal) < (ω : Ordinal) ^ (k : Ordinal) := by
        exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 hkOrd
      have hlt :
          (ω : Ordinal) ^ (n : Ordinal) + l.foldr dmAddOp 0 <
            (ω : Ordinal) ^ (n : Ordinal) + (ω : Ordinal) ^ (k : Ordinal) := by
        exact add_lt_add_left ih ((ω : Ordinal) ^ (n : Ordinal))
      exact lt_of_lt_of_eq hlt (Ordinal.add_omega0_opow hpow)

private lemma dmOrdEmbed_lt_opow_of_forall_lt
    {m : Multiset Nat} {k : Nat} (h : ∀ n ∈ m, n < k) :
    dmOrdEmbed m < (ω : Ordinal) ^ (k : Ordinal) := by
  have hsort : ∀ n ∈ Multiset.sort (· ≥ ·) m, n < k := by
    intro n hn
    exact h n ((Multiset.mem_sort (r := (· ≥ ·))).1 hn)
  simpa [dmOrdEmbed] using
    dmOrdEmbed_list_lt_opow_of_forall_lt k (Multiset.sort (· ≥ ·) m) hsort

private lemma dmOrdEmbed_lt_of_all_le_and_count_lt
    {m₁ m₂ : Multiset Nat} {z : Nat}
    (h₁le : ∀ n ∈ m₁, n ≤ z)
    (h₂le : ∀ n ∈ m₂, n ≤ z)
    (hcount : Multiset.count z m₁ < Multiset.count z m₂) :
    dmOrdEmbed m₁ < dmOrdEmbed m₂ := by
  rw [dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le h₁le,
    dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le h₂le]
  have hLow :
      dmOrdEmbed (m₁.filter (fun n => n < z)) < (ω : Ordinal) ^ (z : Ordinal) := by
    apply dmOrdEmbed_lt_opow_of_forall_lt
    intro n hn
    exact (Multiset.mem_filter.1 hn).2
  have hstep :
      (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m₁ : Ordinal) +
          dmOrdEmbed (m₁.filter (fun n => n < z)) <
        (ω : Ordinal) ^ (z : Ordinal) * Order.succ (Multiset.count z m₁ : Ordinal) := by
    simpa using
      (Ordinal.opow_mul_add_lt_opow_mul_succ
        (b := (ω : Ordinal)) (u := (z : Ordinal))
        (v := (Multiset.count z m₁ : Ordinal))
        (w := dmOrdEmbed (m₁.filter (fun n => n < z))) hLow)
  have hcountOrd : (Multiset.count z m₁ : Ordinal) < (Multiset.count z m₂ : Ordinal) := by
    exact_mod_cast hcount
  have hsucc :
      Order.succ (Multiset.count z m₁ : Ordinal) ≤ (Multiset.count z m₂ : Ordinal) := by
    exact (Order.succ_le_iff).2 hcountOrd
  have hmul :
      (ω : Ordinal) ^ (z : Ordinal) * Order.succ (Multiset.count z m₁ : Ordinal) ≤
        (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m₂ : Ordinal) := by
    exact mul_le_mul_left' hsucc ((ω : Ordinal) ^ (z : Ordinal))
  have hle :
      (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m₂ : Ordinal) ≤
        (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m₂ : Ordinal) +
          dmOrdEmbed (m₂.filter (fun n => n < z)) := by
    exact Ordinal.le_add_right
      ((ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m₂ : Ordinal))
      (dmOrdEmbed (m₂.filter (fun n => n < z)))
  exact lt_of_lt_of_le hstep (hmul.trans hle)

lemma dmOrdEmbed_lt_opow_omega (m : Multiset Nat) :
    dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal) := by
  simpa [dmOrdEmbed] using dmOrdEmbed_list_lt_opow_omega (Multiset.sort (· ≥ ·) m)

private lemma dmOrdEmbed_foldr_le_of_sublist {l₁ l₂ : List Nat}
    (h : List.Sublist l₁ l₂) :
    l₁.foldr dmAddOp 0 ≤ l₂.foldr dmAddOp 0 := by
  induction h with
  | slnil =>
      rfl
  | cons a h ih =>
      exact ih.trans (by
        simp [dmAddOp, Ordinal.le_add_left])
  | cons₂ a h ih =>
      simpa [dmAddOp] using add_le_add_left ih ((ω : Ordinal) ^ (a : Ordinal))

/--
Monotonicity of `dmOrdEmbed` under multiset inclusion.

This is enough for the explicit `rec_zero` strictness argument, where the DM payload grows by
adding a nonempty multiset to the RHS.
-/
lemma dmOrdEmbed_mono {m n : Multiset Nat} (h : m ≤ n) :
    dmOrdEmbed m ≤ dmOrdEmbed n := by
  have hSubperm :
      List.Subperm (Multiset.sort (· ≥ ·) m) (Multiset.sort (· ≥ ·) n) := by
    rw [List.subperm_iff_count]
    intro a
    have hm :
        (Multiset.sort (· ≥ ·) m).count a = Multiset.count a m := by
      simpa using (Multiset.coe_count a (Multiset.sort (· ≥ ·) m)).symm
    have hn :
        (Multiset.sort (· ≥ ·) n).count a = Multiset.count a n := by
      simpa using (Multiset.coe_count a (Multiset.sort (· ≥ ·) n)).symm
    calc
      (Multiset.sort (· ≥ ·) m).count a = Multiset.count a m := hm
      _ ≤ Multiset.count a n := Multiset.count_le_of_le a h
      _ = (Multiset.sort (· ≥ ·) n).count a := hn.symm
  have hSublist :
      List.Sublist (Multiset.sort (· ≥ ·) m) (Multiset.sort (· ≥ ·) n) := by
    exact List.sublist_of_subperm_of_sorted hSubperm
      (Multiset.sort_sorted (r := (· ≥ ·)) m)
      (Multiset.sort_sorted (r := (· ≥ ·)) n)
  exact (dmOrdEmbed_foldr_le_of_sublist hSublist)

@[simp] lemma dmOrdEmbed_zero : dmOrdEmbed (0 : Multiset Nat) = 0 := by
  simp [dmOrdEmbed]

@[simp] lemma dmOrdEmbed_singleton (n : Nat) :
    dmOrdEmbed ({n} : Multiset Nat) = (ω : Ordinal) ^ (n : Ordinal) := by
  simp [dmOrdEmbed, dmAddOp]

private lemma dmOrdEmbed_lt_of_dominated_nonempty
    {Y Z : Multiset Nat}
    (hZ : Z ≠ 0)
    (hDom : ∀ y ∈ Y, ∃ z ∈ Z, y < z) :
    dmOrdEmbed Y < dmOrdEmbed Z := by
  let zMax : Nat := Z.toFinset.max' (Multiset.toFinset_nonempty.2 hZ)
  have hzMax_mem : zMax ∈ Z := by
    exact (Multiset.mem_toFinset).1
      (Finset.max'_mem _ _)
  have hz_le_max : ∀ z ∈ Z, z ≤ zMax := by
    intro z hz
    exact Finset.le_max' _ _ ((Multiset.mem_toFinset).2 hz)
  have hYltMax : ∀ y ∈ Y, y < zMax := by
    intro y hy
    rcases hDom y hy with ⟨z, hz, hyz⟩
    exact lt_of_lt_of_le hyz (hz_le_max z hz)
  have hYlt :
      dmOrdEmbed Y < (ω : Ordinal) ^ (zMax : Ordinal) :=
    dmOrdEmbed_lt_opow_of_forall_lt hYltMax
  have hSingleLe : ({zMax} : Multiset Nat) ≤ Z := by
    exact (Multiset.singleton_le).2 hzMax_mem
  have hZge :
      (ω : Ordinal) ^ (zMax : Ordinal) ≤ dmOrdEmbed Z := by
    calc
      (ω : Ordinal) ^ (zMax : Ordinal)
          = dmOrdEmbed ({zMax} : Multiset Nat) := by
              simpa using (dmOrdEmbed_singleton zMax).symm
      _ ≤ dmOrdEmbed Z := dmOrdEmbed_mono hSingleLe
  exact lt_of_lt_of_le hYlt hZge

lemma dmOrdEmbed_strictMono {m₁ m₂ : Multiset Nat} (hDM : DM m₁ m₂) :
    dmOrdEmbed m₁ < dmOrdEmbed m₂ := by
  rcases hDM with ⟨X, Y, Z, hZ, hm₁, hm₂, hDom⟩
  let zMax : Nat := Z.toFinset.max' (Multiset.toFinset_nonempty.2 hZ)
  have hzMem : zMax ∈ Z := by
    exact (Multiset.mem_toFinset).1 (Finset.max'_mem _ _)
  have hzLe : ∀ z ∈ Z, z ≤ zMax := by
    intro z hz
    exact Finset.le_max' _ _ ((Multiset.mem_toFinset).2 hz)
  have hYlt : ∀ y ∈ Y, y < zMax := by
    intro y hy
    rcases hDom y hy with ⟨z, hz, hyz⟩
    exact lt_of_lt_of_le hyz (hzLe z hz)

  let Xhi : Multiset Nat := X.filter (fun n => zMax < n)
  let Xlo : Multiset Nat := X.filter (fun n => n ≤ zMax)

  have hXsplit : X = Xhi + Xlo := by
    have hNotEq :
        X.filter (fun n => ¬ zMax < n) = X.filter (fun n => n ≤ zMax) := by
      refine Multiset.filter_congr ?_
      intro n hn
      exact (Nat.not_lt)
    calc
      X = X.filter (fun n => zMax < n) + X.filter (fun n => ¬ zMax < n) := by
            simpa [add_comm] using
              (Multiset.filter_add_not (p := fun n => zMax < n) X).symm
      _ = Xhi + Xlo := by rw [hNotEq]

  have hSep₁ : ∀ a ∈ Xhi, ∀ b ∈ Xlo + Y, a ≥ b := by
    intro a ha b hb
    have haGt : zMax < a := (Multiset.mem_filter.1 ha).2
    rcases Multiset.mem_add.1 hb with hb | hb
    · exact le_trans ((Multiset.mem_filter.1 hb).2) haGt.le
    · exact (hYlt b hb).le.trans haGt.le
  have hSep₂ : ∀ a ∈ Xhi, ∀ b ∈ Xlo + Z, a ≥ b := by
    intro a ha b hb
    have haGt : zMax < a := (Multiset.mem_filter.1 ha).2
    rcases Multiset.mem_add.1 hb with hb | hb
    · exact le_trans ((Multiset.mem_filter.1 hb).2) haGt.le
    · exact (hzLe b hb).trans haGt.le

  have h₁le : ∀ n ∈ Xlo + Y, n ≤ zMax := by
    intro n hn
    rcases Multiset.mem_add.1 hn with hn | hn
    · exact (Multiset.mem_filter.1 hn).2
    · exact (hYlt n hn).le
  have h₂le : ∀ n ∈ Xlo + Z, n ≤ zMax := by
    intro n hn
    rcases Multiset.mem_add.1 hn with hn | hn
    · exact (Multiset.mem_filter.1 hn).2
    · exact hzLe n hn

  have hCountY0 : Multiset.count zMax Y = 0 := by
    refine Multiset.count_eq_zero_of_notMem ?_
    intro hzY
    exact (lt_irrefl zMax) (hYlt zMax hzY)
  have hCountZpos : 0 < Multiset.count zMax Z := Multiset.count_pos.2 hzMem
  have hCount :
      Multiset.count zMax (Xlo + Y) < Multiset.count zMax (Xlo + Z) := by
    calc
      Multiset.count zMax (Xlo + Y)
          = Multiset.count zMax Xlo + Multiset.count zMax Y := by simp [Multiset.count_add]
      _ = Multiset.count zMax Xlo := by simp [hCountY0]
      _ < Multiset.count zMax Xlo + Multiset.count zMax Z := Nat.lt_add_of_pos_right hCountZpos
      _ = Multiset.count zMax (Xlo + Z) := by simp [Multiset.count_add]

  have hInner :
      dmOrdEmbed (Xlo + Y) < dmOrdEmbed (Xlo + Z) :=
    dmOrdEmbed_lt_of_all_le_and_count_lt h₁le h₂le hCount

  have h₁ :
      dmOrdEmbed m₁ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Y) := by
    calc
      dmOrdEmbed m₁ = dmOrdEmbed (X + Y) := by simpa [hm₁]
      _ = dmOrdEmbed (Xhi + Xlo + Y) := by rw [hXsplit]
      _ = dmOrdEmbed (Xhi + (Xlo + Y)) := by simp [add_assoc]
      _ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Y) :=
          dmOrdEmbed_add_of_separated hSep₁
  have h₂ :
      dmOrdEmbed m₂ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Z) := by
    calc
      dmOrdEmbed m₂ = dmOrdEmbed (X + Z) := by simpa [hm₂]
      _ = dmOrdEmbed (Xhi + Xlo + Z) := by rw [hXsplit]
      _ = dmOrdEmbed (Xhi + (Xlo + Z)) := by simp [add_assoc]
      _ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Z) :=
          dmOrdEmbed_add_of_separated hSep₂
  calc
    dmOrdEmbed m₁ = dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Y) := h₁
    _ < dmOrdEmbed Xhi + dmOrdEmbed (Xlo + Z) := add_lt_add_left hInner (dmOrdEmbed Xhi)
    _ = dmOrdEmbed m₂ := h₂.symm

/--
Order reflection for the multiset-to-ordinal embedding:
if `dmOrdEmbed m₁ < dmOrdEmbed m₂`, then `DM m₁ m₂`.
-/
lemma dmOrdEmbed_reflects {m₁ m₂ : Multiset Nat}
    (hlt : dmOrdEmbed m₁ < dmOrdEmbed m₂) :
    DM m₁ m₂ := by
  classical
  let X : Multiset Nat := m₁ ∩ m₂
  let Y : Multiset Nat := m₁ - m₂
  let Z : Multiset Nat := m₂ - m₁

  have hZne : Z ≠ 0 := by
    intro hZ0
    have hm2le : m₂ ≤ m₁ := by
      refine (Multiset.le_iff_count).2 ?_
      intro a
      have hZa : Multiset.count a Z = 0 := by simpa [hZ0]
      have hsub : Multiset.count a m₂ - Multiset.count a m₁ = 0 := by
        simpa [Z, Multiset.count_sub] using hZa
      exact Nat.sub_eq_zero_iff_le.mp hsub
    exact (not_lt_of_ge (dmOrdEmbed_mono hm2le)) hlt

  have hm1 : m₁ = X + Y := by
    have hYX : Y + X = m₁ := by
      simpa [X, Y, add_comm] using (Multiset.sub_add_inter m₁ m₂)
    calc
      m₁ = Y + X := hYX.symm
      _ = X + Y := by simp [add_comm]

  have hm2 : m₂ = X + Z := by
    have hZX : Z + X = m₂ := by
      simpa [X, Z, add_comm, Multiset.inter_comm] using (Multiset.sub_add_inter m₂ m₁)
    calc
      m₂ = Z + X := hZX.symm
      _ = X + Z := by simp [add_comm]

  let zMax : Nat := Z.toFinset.max' (Multiset.toFinset_nonempty.2 hZne)
  have hzMem : zMax ∈ Z := by
    exact (Multiset.mem_toFinset).1 (Finset.max'_mem _ _)
  have hzLe : ∀ z ∈ Z, z ≤ zMax := by
    intro z hz
    exact Finset.le_max' _ _ ((Multiset.mem_toFinset).2 hz)

  have hDom : ∀ y ∈ Y, ∃ z ∈ Z, y < z := by
    intro y hy
    by_contra hyNot
    have hyGe : zMax ≤ y := by
      by_contra hyLt
      exact hyNot ⟨zMax, hzMem, lt_of_not_ge hyLt⟩

    let m1hi : Multiset Nat := m₁.filter (fun n => y < n)
    let m1lo : Multiset Nat := m₁.filter (fun n => n ≤ y)
    let m2hi : Multiset Nat := m₂.filter (fun n => y < n)
    let m2lo : Multiset Nat := m₂.filter (fun n => n ≤ y)

    have h1split : m₁ = m1hi + m1lo := by
      have hNot :
          m₁.filter (fun n => ¬ y < n) = m₁.filter (fun n => n ≤ y) := by
        refine Multiset.filter_congr ?_
        intro n hn
        exact Nat.not_lt
      calc
        m₁ = m₁.filter (fun n => y < n) + m₁.filter (fun n => ¬ y < n) := by
              simpa [add_comm] using
                (Multiset.filter_add_not (p := fun n => y < n) m₁).symm
        _ = m1hi + m1lo := by rw [hNot]

    have h2split : m₂ = m2hi + m2lo := by
      have hNot :
          m₂.filter (fun n => ¬ y < n) = m₂.filter (fun n => n ≤ y) := by
        refine Multiset.filter_congr ?_
        intro n hn
        exact Nat.not_lt
      calc
        m₂ = m₂.filter (fun n => y < n) + m₂.filter (fun n => ¬ y < n) := by
              simpa [add_comm] using
                (Multiset.filter_add_not (p := fun n => y < n) m₂).symm
        _ = m2hi + m2lo := by rw [hNot]

    have hHiLe : m2hi ≤ m1hi := by
      refine (Multiset.le_iff_count).2 ?_
      intro a
      by_cases hya : y < a
      · have hNoZ : a ∉ Z := by
          intro haZ
          have hAle : a ≤ zMax := hzLe a haZ
          exact (not_lt_of_ge (hAle.trans hyGe)) hya
        have hZa0 : Multiset.count a Z = 0 := Multiset.count_eq_zero_of_notMem hNoZ
        have hsub : Multiset.count a m₂ - Multiset.count a m₁ = 0 := by
          simpa [Z, Multiset.count_sub] using hZa0
        have hle : Multiset.count a m₂ ≤ Multiset.count a m₁ := Nat.sub_eq_zero_iff_le.mp hsub
        simpa [m2hi, m1hi, Multiset.count_filter, hya] using hle
      · simpa [m2hi, m1hi, Multiset.count_filter, hya]

    have hHigh : dmOrdEmbed m2hi ≤ dmOrdEmbed m1hi := dmOrdEmbed_mono hHiLe

    have hCountY : Multiset.count y m₂ < Multiset.count y m₁ := by
      have hYpos : 0 < Multiset.count y Y := Multiset.count_pos.2 hy
      have hsub : Multiset.count y m₁ - Multiset.count y m₂ > 0 := by
        simpa [Y, Multiset.count_sub] using hYpos
      exact Nat.sub_pos_iff_lt.mp hsub

    have hLow : dmOrdEmbed m2lo < dmOrdEmbed m1lo := by
      have h2le : ∀ n ∈ m2lo, n ≤ y := by
        intro n hn
        exact (Multiset.mem_filter.1 hn).2
      have h1le : ∀ n ∈ m1lo, n ≤ y := by
        intro n hn
        exact (Multiset.mem_filter.1 hn).2
      have hcount :
          Multiset.count y m2lo < Multiset.count y m1lo := by
        simpa [m2lo, m1lo, Multiset.count_filter, Nat.le_refl y] using hCountY
      exact dmOrdEmbed_lt_of_all_le_and_count_lt h2le h1le hcount

    have hSep1 : ∀ a ∈ m1hi, ∀ b ∈ m1lo, a ≥ b := by
      intro a ha b hb
      exact (Multiset.mem_filter.1 hb).2.trans (Nat.le_of_lt (Multiset.mem_filter.1 ha).2)

    have hSep2 : ∀ a ∈ m2hi, ∀ b ∈ m2lo, a ≥ b := by
      intro a ha b hb
      exact (Multiset.mem_filter.1 hb).2.trans (Nat.le_of_lt (Multiset.mem_filter.1 ha).2)

    have hEmb1 : dmOrdEmbed m₁ = dmOrdEmbed m1hi + dmOrdEmbed m1lo := by
      calc
        dmOrdEmbed m₁ = dmOrdEmbed (m1hi + m1lo) := by rw [h1split]
        _ = dmOrdEmbed m1hi + dmOrdEmbed m1lo := dmOrdEmbed_add_of_separated hSep1

    have hEmb2 : dmOrdEmbed m₂ = dmOrdEmbed m2hi + dmOrdEmbed m2lo := by
      calc
        dmOrdEmbed m₂ = dmOrdEmbed (m2hi + m2lo) := by rw [h2split]
        _ = dmOrdEmbed m2hi + dmOrdEmbed m2lo := dmOrdEmbed_add_of_separated hSep2

    have hrev : dmOrdEmbed m₂ < dmOrdEmbed m₁ := by
      calc
        dmOrdEmbed m₂ = dmOrdEmbed m2hi + dmOrdEmbed m2lo := hEmb2
        _ ≤ dmOrdEmbed m1hi + dmOrdEmbed m2lo := add_le_add_right hHigh _
        _ < dmOrdEmbed m1hi + dmOrdEmbed m1lo := add_lt_add_left hLow _
        _ = dmOrdEmbed m₁ := hEmb1.symm
    exact (lt_asymm hlt hrev)

  exact ⟨X, Y, Z, hZne, hm1, hm2, hDom⟩

/-! ## ε₀ bridge facts -/

lemma opow_omega_lt_epsilon0 : (ω : Ordinal) ^ (ω : Ordinal) < ε₀ := by
  -- `(fun a => ω^a)^[3] 0 = ω^ω`
  simpa [Function.iterate_succ_apply, opow_zero, opow_one] using
    (iterate_omega0_opow_lt_epsilon0 3)

/-- Inner lex block embedding `(κ,τ) ↦ ω*κ + τ`. -/
noncomputable def lexDMToOrd (p : Multiset Nat × Nat) : Ordinal.{0} :=
  ω * dmOrdEmbed p.1 + (p.2 : Ordinal)

/-- Outer triple embedding `(δ,(κ,τ)) ↦ ω^ω*δ + (ω*κ + τ)`. -/
noncomputable def lex3cToOrd (x : Nat × (Multiset Nat × Nat)) : Ordinal.{0} :=
  (ω ^ ω) * (x.1 : Ordinal) + lexDMToOrd x.2

/-- If `dmOrdEmbed κ < ω^ω`, then the inner block is also `< ω^ω`. -/
private lemma lexDMToOrd_lt_opow_omega_of_dmBound
    (hBound : ∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal))
    (p : Multiset Nat × Nat) :
    lexDMToOrd p < (ω : Ordinal) ^ (ω : Ordinal) := by
  rcases p with ⟨κ, τ⟩
  have hτ : (τ : Ordinal) < (ω : Ordinal) := Ordinal.nat_lt_omega0 τ
  have hτ1 : (τ : Ordinal) < (ω : Ordinal) ^ (1 : Ordinal) := by
    simpa [Ordinal.opow_one] using hτ
  have hstep :
      (ω : Ordinal) * dmOrdEmbed κ + (τ : Ordinal) <
        (ω : Ordinal) * Order.succ (dmOrdEmbed κ) := by
    simpa using
      (Ordinal.opow_mul_add_lt_opow_mul_succ
        (b := (ω : Ordinal)) (u := (1 : Ordinal))
        (v := dmOrdEmbed κ) (w := (τ : Ordinal)) hτ1)
  have hsucc : Order.succ (dmOrdEmbed κ) ≤ (ω : Ordinal) ^ (ω : Ordinal) := by
    exact (Order.succ_le_iff).2 (hBound κ)
  have hmul :
      (ω : Ordinal) * Order.succ (dmOrdEmbed κ) ≤
        (ω : Ordinal) * ((ω : Ordinal) ^ (ω : Ordinal)) := by
    exact mul_le_mul_left' hsucc (ω : Ordinal)
  have hωω :
      (ω : Ordinal) * ((ω : Ordinal) ^ (ω : Ordinal)) =
        (ω : Ordinal) ^ (ω : Ordinal) := by
    calc
      (ω : Ordinal) * ((ω : Ordinal) ^ (ω : Ordinal))
          = (ω : Ordinal) ^ (1 + (ω : Ordinal)) := by
              simpa [Ordinal.opow_one] using
                (Ordinal.opow_add (ω : Ordinal) 1 (ω : Ordinal)).symm
      _ = (ω : Ordinal) ^ (ω : Ordinal) := by simp
  calc
    lexDMToOrd (κ, τ) = (ω : Ordinal) * dmOrdEmbed κ + (τ : Ordinal) := by rfl
    _ < (ω : Ordinal) * Order.succ (dmOrdEmbed κ) := hstep
    _ ≤ (ω : Ordinal) * ((ω : Ordinal) ^ (ω : Ordinal)) := hmul
    _ = (ω : Ordinal) ^ (ω : Ordinal) := hωω

/-- Unconditional inner-block bound, using `dmOrdEmbed_lt_opow_omega`. -/
lemma lexDMToOrd_lt_opow_omega (p : Multiset Nat × Nat) :
    lexDMToOrd p < (ω : Ordinal) ^ (ω : Ordinal) :=
  lexDMToOrd_lt_opow_omega_of_dmBound dmOrdEmbed_lt_opow_omega p

/-- Calibration cap used for the safe triple (`δ∈{0,1}`): `ω^ω * 2 < ε₀`. -/
lemma opow_omega_mul_two_lt_epsilon0 :
    ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) < ε₀ := by
  have hωlt : (ω : Ordinal) < ε₀ := by
    simpa using (Ordinal.omega0_lt_epsilon 0)
  have hmul :
      ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) <
        (ω : Ordinal) ^ ε₀ := by
    simpa using
      (Ordinal.omega0_opow_mul_nat_lt
        (a := (ω : Ordinal)) (b := ε₀) hωlt 2)
  simpa [Ordinal.omega0_opow_epsilon] using hmul

/-- If `δ ≤ 1` and `dmOrdEmbed` is bounded by `ω^ω`, then `lex3cToOrd` is `< ω^ω*2`. -/
private lemma lex3cToOrd_lt_opow_omega_mul_two_of_dmBound
    (hBound : ∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal))
    {x : Nat × (Multiset Nat × Nat)} (hδ : x.1 ≤ 1) :
    lex3cToOrd x < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) := by
  have hInner : lexDMToOrd x.2 < (ω : Ordinal) ^ (ω : Ordinal) :=
    lexDMToOrd_lt_opow_omega_of_dmBound hBound x.2
  have hstep :
      ((ω : Ordinal) ^ (ω : Ordinal)) * (x.1 : Ordinal) + lexDMToOrd x.2 <
        ((ω : Ordinal) ^ (ω : Ordinal)) * Order.succ (x.1 : Ordinal) := by
    simpa [Ordinal.opow_mul] using
      (Ordinal.opow_mul_add_lt_opow_mul_succ
        (b := (ω : Ordinal)) (u := (ω : Ordinal))
        (v := (x.1 : Ordinal)) (w := lexDMToOrd x.2) hInner)
  have hsuccNat : Nat.succ x.1 ≤ 2 := Nat.succ_le_succ hδ
  have hltTwoNat : x.1 < 2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self x.1) hsuccNat
  have hltTwoOrd : (x.1 : Ordinal) < (2 : Ordinal) := by
    exact_mod_cast hltTwoNat
  have hsuccOrd : Order.succ (x.1 : Ordinal) ≤ (2 : Ordinal) := by
    exact (Order.succ_le_iff).2 hltTwoOrd
  have hmul :
      ((ω : Ordinal) ^ (ω : Ordinal)) * Order.succ (x.1 : Ordinal) ≤
        ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Ordinal) := by
    exact mul_le_mul_left' hsuccOrd ((ω : Ordinal) ^ (ω : Ordinal))
  simpa [lex3cToOrd] using lt_of_lt_of_le hstep hmul

/-- Unconditional triple bound under the safe binary-phase side condition `δ ≤ 1`. -/
lemma lex3cToOrd_lt_opow_omega_mul_two
    {x : Nat × (Multiset Nat × Nat)} (hδ : x.1 ≤ 1) :
    lex3cToOrd x < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) :=
  lex3cToOrd_lt_opow_omega_mul_two_of_dmBound dmOrdEmbed_lt_opow_omega hδ

/-- If `dmOrdEmbed` is bounded by `ω^ω`, then all safe triples are `< ε₀`. -/
private lemma safeMeasure_below_epsilon0_of_dmBound
    (hBound : ∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal))
    (t : Trace) :
    lex3cToOrd (mu3c t) < ε₀ := by
  have hδFlag : MetaSN_KO7.deltaFlag t ≤ 1 := by
    rcases MetaSN_KO7.deltaFlag_range t with h0 | h1
    · omega
    · omega
  have hδ : (mu3c t).1 ≤ 1 := by
    simpa [mu3c] using hδFlag
  have hlt :
      lex3cToOrd (mu3c t) < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) :=
    lex3cToOrd_lt_opow_omega_mul_two_of_dmBound hBound hδ
  exact lt_of_lt_of_le hlt (opow_omega_mul_two_lt_epsilon0.le)

/-- Unconditional `ε₀` calibration for `mu3c`, via the mechanized `dmOrdEmbed` bound. -/
lemma safeMeasure_below_epsilon0 (t : Trace) :
    lex3cToOrd (mu3c t) < ε₀ :=
  safeMeasure_below_epsilon0_of_dmBound dmOrdEmbed_lt_opow_omega t

/-- Conditional strict monotonicity for the inner lex block. -/
private lemma lexDMToOrd_strictMono_of_dmMono
    (hMono : ∀ {m₁ m₂ : Multiset Nat}, DM m₁ m₂ → dmOrdEmbed m₁ < dmOrdEmbed m₂)
    {p q : Multiset Nat × Nat} (h : LexDM_c p q) :
    lexDMToOrd p < lexDMToOrd q := by
  rcases p with ⟨κ₁, τ₁⟩
  rcases q with ⟨κ₂, τ₂⟩
  cases h with
  | left _ _ hDM =>
      have hκ : dmOrdEmbed κ₁ < dmOrdEmbed κ₂ := hMono hDM
      have hτ : (τ₁ : Ordinal) < (ω : Ordinal) := Ordinal.nat_lt_omega0 τ₁
      have hτ1 : (τ₁ : Ordinal) < (ω : Ordinal) ^ (1 : Ordinal) := by
        simpa [Ordinal.opow_one] using hτ
      have hstep :
          (ω : Ordinal) * dmOrdEmbed κ₁ + (τ₁ : Ordinal) <
            (ω : Ordinal) * Order.succ (dmOrdEmbed κ₁) := by
        simpa using
          (Ordinal.opow_mul_add_lt_opow_mul_succ
            (b := (ω : Ordinal)) (u := (1 : Ordinal))
            (v := dmOrdEmbed κ₁) (w := (τ₁ : Ordinal)) hτ1)
      have hsucc : Order.succ (dmOrdEmbed κ₁) ≤ dmOrdEmbed κ₂ := by
        exact (Order.succ_le_iff).2 hκ
      have hmul :
          (ω : Ordinal) * Order.succ (dmOrdEmbed κ₁) ≤
            (ω : Ordinal) * dmOrdEmbed κ₂ := by
        exact mul_le_mul_left' hsucc (ω : Ordinal)
      have hle : (ω : Ordinal) * dmOrdEmbed κ₂ ≤ lexDMToOrd (κ₂, τ₂) := by
        simpa [lexDMToOrd] using
          (Ordinal.le_add_right ((ω : Ordinal) * dmOrdEmbed κ₂) (τ₂ : Ordinal))
      have hstep' :
          lexDMToOrd (κ₁, τ₁) < (ω : Ordinal) * Order.succ (dmOrdEmbed κ₁) := by
        simpa [lexDMToOrd] using hstep
      calc
        lexDMToOrd (κ₁, τ₁) < (ω : Ordinal) * Order.succ (dmOrdEmbed κ₁) := hstep'
        _ ≤ (ω : Ordinal) * dmOrdEmbed κ₂ := hmul
        _ ≤ lexDMToOrd (κ₂, τ₂) := hle
  | right _ hτNat =>
      have hτOrd : (τ₁ : Ordinal) < (τ₂ : Ordinal) := by
        exact_mod_cast hτNat
      simpa [lexDMToOrd] using
        (add_lt_add_left hτOrd ((ω : Ordinal) * dmOrdEmbed κ₁))

/-- Conditional strict monotonicity for the full triple embedding. -/
private lemma lex3cToOrd_strictMono_of_dmBoundMono
    (hBound : ∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal))
    (hMono : ∀ {m₁ m₂ : Multiset Nat}, DM m₁ m₂ → dmOrdEmbed m₁ < dmOrdEmbed m₂)
    {x y : Nat × (Multiset Nat × Nat)} (h : Lex3c x y) :
    lex3cToOrd x < lex3cToOrd y := by
  rcases x with ⟨δ₁, p₁⟩
  rcases y with ⟨δ₂, p₂⟩
  cases h with
  | left _ _ hδNat =>
      have hInner : lexDMToOrd p₁ < (ω : Ordinal) ^ (ω : Ordinal) :=
        lexDMToOrd_lt_opow_omega_of_dmBound hBound p₁
      have hstep :
          ((ω : Ordinal) ^ (ω : Ordinal)) * (δ₁ : Ordinal) + lexDMToOrd p₁ <
            ((ω : Ordinal) ^ (ω : Ordinal)) * Order.succ (δ₁ : Ordinal) := by
        simpa [Ordinal.opow_mul] using
          (Ordinal.opow_mul_add_lt_opow_mul_succ
            (b := (ω : Ordinal)) (u := (ω : Ordinal))
            (v := (δ₁ : Ordinal)) (w := lexDMToOrd p₁) hInner)
      have hδOrd : (δ₁ : Ordinal) < (δ₂ : Ordinal) := by
        exact_mod_cast hδNat
      have hsucc : Order.succ (δ₁ : Ordinal) ≤ (δ₂ : Ordinal) := by
        exact (Order.succ_le_iff).2 hδOrd
      have hmul :
          ((ω : Ordinal) ^ (ω : Ordinal)) * Order.succ (δ₁ : Ordinal) ≤
            ((ω : Ordinal) ^ (ω : Ordinal)) * (δ₂ : Ordinal) := by
        exact mul_le_mul_left' hsucc ((ω : Ordinal) ^ (ω : Ordinal))
      have hle :
          ((ω : Ordinal) ^ (ω : Ordinal)) * (δ₂ : Ordinal) ≤
            lex3cToOrd (δ₂, p₂) := by
        simpa [lex3cToOrd] using
          (Ordinal.le_add_right
            (((ω : Ordinal) ^ (ω : Ordinal)) * (δ₂ : Ordinal))
            (lexDMToOrd p₂))
      exact lt_of_lt_of_le hstep (hmul.trans hle)
  | right _ hInner =>
      have hInnerOrd : lexDMToOrd p₁ < lexDMToOrd p₂ :=
        lexDMToOrd_strictMono_of_dmMono hMono hInner
      simpa [lex3cToOrd] using
        (add_lt_add_left hInnerOrd (((ω : Ordinal) ^ (ω : Ordinal)) * (δ₁ : Ordinal)))

/-- Conditional strict decrease along safe steps via the KO7 computable measure theorem. -/
private lemma safeMeasure_strictMono_of_dmBoundMono
    (hBound : ∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal))
    (hMono : ∀ {m₁ m₂ : Multiset Nat}, DM m₁ m₂ → dmOrdEmbed m₁ < dmOrdEmbed m₂)
    {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c a) := by
  exact lex3cToOrd_strictMono_of_dmBoundMono hBound hMono (measure_decreases_safe_c h)

lemma lexDMToOrd_strictMono {p q : Multiset Nat × Nat} (h : LexDM_c p q) :
    lexDMToOrd p < lexDMToOrd q :=
  lexDMToOrd_strictMono_of_dmMono
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) h

lemma lex3cToOrd_strictMono {x y : Nat × (Multiset Nat × Nat)} (h : Lex3c x y) :
    lex3cToOrd x < lex3cToOrd y :=
  lex3cToOrd_strictMono_of_dmBoundMono
    dmOrdEmbed_lt_opow_omega
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) h

lemma safeMeasure_strictMono_embed {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c a) :=
  safeMeasure_strictMono_of_dmBoundMono
    dmOrdEmbed_lt_opow_omega
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) h

/-- Explicit `lex3cToOrd` strictness for the `rec_zero` safe rule. -/
lemma lex3cToOrd_drop_R_rec_zero (b s : Trace) (hδ : MetaSN_KO7.deltaFlag b = 0) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c (recΔ b s void)) := by
  have hκleMs : kappaM b ≤ kappaM (recΔ b s void) := by
    have hbase : kappaM b ≤ kappaM b + (1 ::ₘ kappaM s) := by
      simpa using (Multiset.le_add_right (kappaM b) (1 ::ₘ kappaM s))
    simpa [MetaSN_DM.kappaM_rec_zero, add_comm, add_left_comm, add_assoc] using hbase
  have hκle : dmOrdEmbed (kappaM b) ≤ dmOrdEmbed (kappaM (recΔ b s void)) :=
    dmOrdEmbed_mono hκleMs
  have hmul :
      (ω : Ordinal) * dmOrdEmbed (kappaM b) ≤
        (ω : Ordinal) * dmOrdEmbed (kappaM (recΔ b s void)) := by
    exact mul_le_mul_left' hκle (ω : Ordinal)
  have hτNat : tau b < tau (recΔ b s void) := by
    simp [tau]; omega
  have hτ : (tau b : Ordinal) < (tau (recΔ b s void) : Ordinal) := by
    exact_mod_cast hτNat
  have hinner₁ :
      lexDMToOrd (kappaM b, tau b) <
        (ω : Ordinal) * dmOrdEmbed (kappaM b) + (tau (recΔ b s void) : Ordinal) := by
    simpa [lexDMToOrd] using
      (add_lt_add_left hτ ((ω : Ordinal) * dmOrdEmbed (kappaM b)))
  have hinner₂ :
      (ω : Ordinal) * dmOrdEmbed (kappaM b) + (tau (recΔ b s void) : Ordinal) ≤
        lexDMToOrd (kappaM (recΔ b s void), tau (recΔ b s void)) := by
    simpa [lexDMToOrd] using add_le_add_right hmul (tau (recΔ b s void) : Ordinal)
  have hinner :
      lexDMToOrd (kappaM b, tau b) <
        lexDMToOrd (kappaM (recΔ b s void), tau (recΔ b s void)) :=
    lt_of_lt_of_le hinner₁ hinner₂
  have hδrec : MetaSN_KO7.deltaFlag (recΔ b s void) = 0 := by
    simp
  have hδord : ((MetaSN_KO7.deltaFlag b : Nat) : Ordinal) = 0 := by
    exact_mod_cast hδ
  have hδrecOrd : ((MetaSN_KO7.deltaFlag (recΔ b s void) : Nat) : Ordinal) = 0 := by
    exact_mod_cast hδrec
  have hleft :
      lex3cToOrd (mu3c b) = lexDMToOrd (kappaM b, tau b) := by
    unfold lex3cToOrd mu3c
    rw [hδord]
    simp
  have hright :
      lex3cToOrd (mu3c (recΔ b s void)) =
        lexDMToOrd (kappaM (recΔ b s void), tau (recΔ b s void)) := by
    unfold lex3cToOrd mu3c
    rw [hδrecOrd]
    simp
  calc
    lex3cToOrd (mu3c b) = lexDMToOrd (kappaM b, tau b) := hleft
    _ < lexDMToOrd (kappaM (recΔ b s void), tau (recΔ b s void)) := hinner
    _ = lex3cToOrd (mu3c (recΔ b s void)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `integrate (delta t) → void`. -/
lemma lex3cToOrd_drop_R_int_delta (t : Trace) :
    lex3cToOrd (mu3c void) < lex3cToOrd (mu3c (integrate (delta t))) := by
  have hτNat : 0 < tau (integrate (delta t)) := by simp [tau]
  have hτ : (0 : Ordinal) < (tau (integrate (delta t)) : Ordinal) := by
    exact_mod_cast hτNat
  have hτle :
      (tau (integrate (delta t)) : Ordinal) ≤
        lexDMToOrd (kappaM (integrate (delta t)), tau (integrate (delta t))) := by
    simpa [lexDMToOrd] using
      (Ordinal.le_add_left (tau (integrate (delta t)) : Ordinal)
        ((ω : Ordinal) * dmOrdEmbed (kappaM (integrate (delta t)))))
  have hright :
      lex3cToOrd (mu3c (integrate (delta t))) =
        lexDMToOrd (kappaM (integrate (delta t)), tau (integrate (delta t))) := by
    simp [lex3cToOrd, mu3c]
  have hleft : lex3cToOrd (mu3c void) = 0 := by
    simp [lex3cToOrd, mu3c, lexDMToOrd, tau, kappaM]
  calc
    lex3cToOrd (mu3c void) = 0 := hleft
    _ < (tau (integrate (delta t)) : Ordinal) := hτ
    _ ≤ lexDMToOrd (kappaM (integrate (delta t)), tau (integrate (delta t))) := hτle
    _ = lex3cToOrd (mu3c (integrate (delta t))) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `merge void t → t` (guarded). -/
lemma lex3cToOrd_drop_R_merge_void_left (t : Trace) (hδ : MetaSN_KO7.deltaFlag t = 0) :
    lex3cToOrd (mu3c t) < lex3cToOrd (mu3c (merge void t)) := by
  have hτNat : tau t < tau (merge void t) := by simp [tau]
  have hτ : (tau t : Ordinal) < (tau (merge void t) : Ordinal) := by
    exact_mod_cast hτNat
  have hκ : kappaM (merge void t) = kappaM t := MetaSN_DM.kappaM_merge_void_left t
  have hinner :
      lexDMToOrd (kappaM t, tau t) <
        lexDMToOrd (kappaM (merge void t), tau (merge void t)) := by
    simpa [lexDMToOrd, hκ] using
      (add_lt_add_left hτ ((ω : Ordinal) * dmOrdEmbed (kappaM t)))
  have hδord : ((MetaSN_KO7.deltaFlag t : Nat) : Ordinal) = 0 := by
    exact_mod_cast hδ
  have hleft :
      lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := by
    unfold lex3cToOrd mu3c
    rw [hδord]
    simp
  have hright :
      lex3cToOrd (mu3c (merge void t)) =
        lexDMToOrd (kappaM (merge void t), tau (merge void t)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := hleft
    _ < lexDMToOrd (kappaM (merge void t), tau (merge void t)) := hinner
    _ = lex3cToOrd (mu3c (merge void t)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `merge t void → t` (guarded). -/
lemma lex3cToOrd_drop_R_merge_void_right (t : Trace) (hδ : MetaSN_KO7.deltaFlag t = 0) :
    lex3cToOrd (mu3c t) < lex3cToOrd (mu3c (merge t void)) := by
  have hτNat : tau t < tau (merge t void) := by simp [tau]
  have hτ : (tau t : Ordinal) < (tau (merge t void) : Ordinal) := by
    exact_mod_cast hτNat
  have hκ : kappaM (merge t void) = kappaM t := MetaSN_DM.kappaM_merge_void_right t
  have hinner :
      lexDMToOrd (kappaM t, tau t) <
        lexDMToOrd (kappaM (merge t void), tau (merge t void)) := by
    simpa [lexDMToOrd, hκ] using
      (add_lt_add_left hτ ((ω : Ordinal) * dmOrdEmbed (kappaM t)))
  have hδord : ((MetaSN_KO7.deltaFlag t : Nat) : Ordinal) = 0 := by
    exact_mod_cast hδ
  have hleft :
      lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := by
    unfold lex3cToOrd mu3c
    rw [hδord]
    simp
  have hright :
      lex3cToOrd (mu3c (merge t void)) =
        lexDMToOrd (kappaM (merge t void), tau (merge t void)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := hleft
    _ < lexDMToOrd (kappaM (merge t void), tau (merge t void)) := hinner
    _ = lex3cToOrd (mu3c (merge t void)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `merge t t → t` (guarded). -/
lemma lex3cToOrd_drop_R_merge_cancel (t : Trace)
    (hδ : MetaSN_KO7.deltaFlag t = 0) (h0 : kappaM t = 0) :
    lex3cToOrd (mu3c t) < lex3cToOrd (mu3c (merge t t)) := by
  have hτNat : tau t < tau (merge t t) := by simp [tau]
  have hτ : (tau t : Ordinal) < (tau (merge t t) : Ordinal) := by
    exact_mod_cast hτNat
  have hκmerge : kappaM (merge t t) = 0 := by
    simpa [MetaSN_DM.kappaM_merge_cancel, h0]
  have hinner :
      lexDMToOrd (kappaM t, tau t) <
        lexDMToOrd (kappaM (merge t t), tau (merge t t)) := by
    simpa [lexDMToOrd, h0, hκmerge] using
      (add_lt_add_left hτ ((ω : Ordinal) * (0 : Ordinal)))
  have hδord : ((MetaSN_KO7.deltaFlag t : Nat) : Ordinal) = 0 := by
    exact_mod_cast hδ
  have hleft :
      lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := by
    unfold lex3cToOrd mu3c
    rw [hδord]
    simp
  have hright :
      lex3cToOrd (mu3c (merge t t)) =
        lexDMToOrd (kappaM (merge t t), tau (merge t t)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c t) = lexDMToOrd (kappaM t, tau t) := hleft
    _ < lexDMToOrd (kappaM (merge t t), tau (merge t t)) := hinner
    _ = lex3cToOrd (mu3c (merge t t)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `recΔ b s (delta n) → app s (recΔ b s n)`. -/
lemma lex3cToOrd_drop_R_rec_succ (b s n : Trace) :
    lex3cToOrd (mu3c (app s (recΔ b s n))) < lex3cToOrd (mu3c (recΔ b s (delta n))) := by
  have hinner :
      lexDMToOrd (kappaM (app s (recΔ b s n)), tau (app s (recΔ b s n))) <
        (ω : Ordinal) ^ (ω : Ordinal) := by
    exact lexDMToOrd_lt_opow_omega
      (kappaM (app s (recΔ b s n)), tau (app s (recΔ b s n)))
  have hleft :
      lex3cToOrd (mu3c (app s (recΔ b s n))) =
        lexDMToOrd (kappaM (app s (recΔ b s n)), tau (app s (recΔ b s n))) := by
    simp [lex3cToOrd, mu3c]
  have hrightLe :
      (ω : Ordinal) ^ (ω : Ordinal) ≤
        lex3cToOrd (mu3c (recΔ b s (delta n))) := by
    have :
        (ω : Ordinal) ^ (ω : Ordinal) ≤
          ((ω : Ordinal) ^ (ω : Ordinal)) +
            lexDMToOrd (kappaM (recΔ b s (delta n)), tau (recΔ b s (delta n))) := by
      simpa using
        (Ordinal.le_add_right ((ω : Ordinal) ^ (ω : Ordinal))
          (lexDMToOrd (kappaM (recΔ b s (delta n)), tau (recΔ b s (delta n)))))
    simpa [lex3cToOrd, mu3c, MetaSN_KO7.deltaFlag_rec_delta] using this
  calc
    lex3cToOrd (mu3c (app s (recΔ b s n)))
        = lexDMToOrd (kappaM (app s (recΔ b s n)), tau (app s (recΔ b s n))) := hleft
    _ < (ω : Ordinal) ^ (ω : Ordinal) := hinner
    _ ≤ lex3cToOrd (mu3c (recΔ b s (delta n))) := hrightLe

/-- Explicit `lex3cToOrd` strictness for `eqW a a → void` (guarded). -/
lemma lex3cToOrd_drop_R_eq_refl (a : Trace) (h0 : kappaM a = 0) :
    lex3cToOrd (mu3c void) < lex3cToOrd (mu3c (eqW a a)) := by
  have hτNat : tau void < tau (eqW a a) := by simp [tau]
  have hτ : (tau void : Ordinal) < (tau (eqW a a) : Ordinal) := by
    exact_mod_cast hτNat
  have hκ : kappaM (eqW a a) = 0 := by
    simpa [MetaSN_DM.kappaM_eq_refl, h0]
  have hinner :
      lexDMToOrd (kappaM void, tau void) <
        lexDMToOrd (kappaM (eqW a a), tau (eqW a a)) := by
    simpa [lexDMToOrd, hκ, h0] using
      (add_lt_add_left hτ ((ω : Ordinal) * (0 : Ordinal)))
  have hleft : lex3cToOrd (mu3c void) = lexDMToOrd (kappaM void, tau void) := by
    simp [lex3cToOrd, mu3c]
  have hright : lex3cToOrd (mu3c (eqW a a)) = lexDMToOrd (kappaM (eqW a a), tau (eqW a a)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c void) = lexDMToOrd (kappaM void, tau void) := hleft
    _ < lexDMToOrd (kappaM (eqW a a), tau (eqW a a)) := hinner
    _ = lex3cToOrd (mu3c (eqW a a)) := hright.symm

/-- Explicit `lex3cToOrd` strictness for `eqW a b → integrate (merge a b)`. -/
lemma lex3cToOrd_drop_R_eq_diff (a b : Trace) :
    lex3cToOrd (mu3c (integrate (merge a b))) < lex3cToOrd (mu3c (eqW a b)) := by
  have hκ : kappaM (integrate (merge a b)) = kappaM (eqW a b) := MetaSN_DM.kappaM_eq_diff a b
  have hτNat : tau (integrate (merge a b)) < tau (eqW a b) := by
    simp [tau]; omega
  have hτ : (tau (integrate (merge a b)) : Ordinal) < (tau (eqW a b) : Ordinal) := by
    exact_mod_cast hτNat
  have hinner :
      lexDMToOrd (kappaM (integrate (merge a b)), tau (integrate (merge a b))) <
        lexDMToOrd (kappaM (eqW a b), tau (eqW a b)) := by
    simpa [lexDMToOrd, hκ] using
      (add_lt_add_left hτ ((ω : Ordinal) * dmOrdEmbed (kappaM (eqW a b))))
  have hleft :
      lex3cToOrd (mu3c (integrate (merge a b))) =
        lexDMToOrd (kappaM (integrate (merge a b)), tau (integrate (merge a b))) := by
    simp [lex3cToOrd, mu3c]
  have hright :
      lex3cToOrd (mu3c (eqW a b)) = lexDMToOrd (kappaM (eqW a b), tau (eqW a b)) := by
    simp [lex3cToOrd, mu3c]
  calc
    lex3cToOrd (mu3c (integrate (merge a b)))
        = lexDMToOrd (kappaM (integrate (merge a b)), tau (integrate (merge a b))) := hleft
    _ < lexDMToOrd (kappaM (eqW a b), tau (eqW a b)) := hinner
    _ = lex3cToOrd (mu3c (eqW a b)) := hright.symm

/-- Explicit strict decrease of `lex3cToOrd` along every guarded `SafeStep` constructor. -/
lemma safeMeasure_strictMono_explicit {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cToOrd (mu3c b) < lex3cToOrd (mu3c a) := by
  induction h with
  | R_int_delta t =>
      simpa using lex3cToOrd_drop_R_int_delta t
  | R_merge_void_left t hδ =>
      simpa using lex3cToOrd_drop_R_merge_void_left t hδ
  | R_merge_void_right t hδ =>
      simpa using lex3cToOrd_drop_R_merge_void_right t hδ
  | R_merge_cancel t hδ h0 =>
      simpa using lex3cToOrd_drop_R_merge_cancel t hδ h0
  | R_rec_zero b s hδ =>
      simpa using lex3cToOrd_drop_R_rec_zero b s hδ
  | R_rec_succ b s n =>
      simpa using lex3cToOrd_drop_R_rec_succ b s n
  | R_eq_refl a h0 =>
      simpa using lex3cToOrd_drop_R_eq_refl a h0
  | R_eq_diff a b _ =>
      simpa using lex3cToOrd_drop_R_eq_diff a b

/-! ## Unconditional rank fallback (no DM embedding assumptions) -/

local instance instIsWellFoundedDM : IsWellFounded (Multiset Nat) DM :=
  ⟨MetaSN_DM.wf_dm⟩

/-- Ordinal rank of DM, available unconditionally from DM well-foundedness. -/
noncomputable def dmRankOrd (m : Multiset Nat) : Ordinal.{0} :=
  IsWellFounded.rank (r := DM) m

lemma dmRankOrd_strictMono {m₁ m₂ : Multiset Nat} (h : DM m₁ m₂) :
    dmRankOrd m₁ < dmRankOrd m₂ :=
  IsWellFounded.rank_lt_of_rel h

/--
Rank-vs-embedding transfer principle for `DM`.

If an ordinal-valued map strictly increases along `DM` edges, then `DM`-rank is pointwise bounded
by that map.
-/
lemma dmRankOrd_le_dmOrdEmbed_of_strictMono
    (hMono : ∀ {m₁ m₂ : Multiset Nat}, DM m₁ m₂ → dmOrdEmbed m₁ < dmOrdEmbed m₂)
    (m : Multiset Nat) :
    dmRankOrd m ≤ dmOrdEmbed m := by
  induction m using MetaSN_DM.wf_dm.induction with
  | h x ih =>
      rw [dmRankOrd, IsWellFounded.rank_eq (r := DM) x]
      change (⨆ y : { y // DM y x }, Order.succ (dmRankOrd y.1)) ≤ dmOrdEmbed x
      refine Ordinal.iSup_le ?_
      intro y
      exact (Order.succ_le_iff).2 <|
        (lt_of_le_of_lt (ih y.1 y.2) (hMono y.2))

/--
Conditional `ω^ω` upper bound for `DM`-rank.

This is the Phase A bridge: once global strict monotonicity of `dmOrdEmbed` along `DM` is proved,
the rank bound follows immediately.
-/
lemma dmRankOrd_lt_opow_omega_of_dmOrdEmbed_strictMono
    (hMono : ∀ {m₁ m₂ : Multiset Nat}, DM m₁ m₂ → dmOrdEmbed m₁ < dmOrdEmbed m₂)
    (m : Multiset Nat) :
    dmRankOrd m < (ω : Ordinal) ^ (ω : Ordinal) := by
  exact lt_of_le_of_lt
    (dmRankOrd_le_dmOrdEmbed_of_strictMono hMono m)
    (dmOrdEmbed_lt_opow_omega m)

lemma dmRankOrd_lt_opow_omega (m : Multiset Nat) :
    dmRankOrd m < (ω : Ordinal) ^ (ω : Ordinal) :=
  dmRankOrd_lt_opow_omega_of_dmOrdEmbed_strictMono
    (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) m

local instance instIsWellFoundedLex3c :
    IsWellFounded (Nat × (Multiset Nat × Nat)) Lex3c :=
  ⟨wf_Lex3c⟩

/-- Ordinal rank of `Lex3c`, available unconditionally from `wf_Lex3c`. -/
noncomputable def lex3cRankOrd (x : Nat × (Multiset Nat × Nat)) : Ordinal.{0} :=
  IsWellFounded.rank (r := Lex3c) x

lemma lex3cRankOrd_strictMono {x y : Nat × (Multiset Nat × Nat)} (h : Lex3c x y) :
    lex3cRankOrd x < lex3cRankOrd y :=
  IsWellFounded.rank_lt_of_rel h

/-- Fully assumption-free strict decrease along safe steps (rank formulation). -/
lemma safeMeasure_rank_strictMono {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cRankOrd (mu3c b) < lex3cRankOrd (mu3c a) :=
  lex3cRankOrd_strictMono (measure_decreases_safe_c h)

/-- Assumption-free strict decrease theorem (rank-calibrated form). -/
lemma safeMeasure_strictMono {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cRankOrd (mu3c b) < lex3cRankOrd (mu3c a) :=
  safeMeasure_rank_strictMono h

/--
Combined unconditional statement used in the paper narrative:
- strict per-step decrease is certified by well-founded rank;
- explicit ordinal calibration gives `< ε₀` for both endpoints.
-/
lemma safeMeasure_step_rank_and_epsilon0
    {a b : Trace} (h : MetaSN_KO7.SafeStep a b) :
    lex3cRankOrd (mu3c b) < lex3cRankOrd (mu3c a) ∧
      lex3cToOrd (mu3c b) < ε₀ ∧ lex3cToOrd (mu3c a) < ε₀ := by
  exact ⟨safeMeasure_rank_strictMono h, safeMeasure_below_epsilon0 b, safeMeasure_below_epsilon0 a⟩

end OperatorKO7.MetaDM
