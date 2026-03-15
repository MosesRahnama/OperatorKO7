import OperatorKO7.Kernel
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.Veblen

/-!
KO7 MPO orientation for the full root relation `Step`.

This module is KO7-specialized (not a generic library formalization):
- subterm clause;
- precedence clause;
- same-head multiset-style clause for `recΔ` (third argument drop).

It proves that all eight full-kernel rules are oriented.
-/

namespace OperatorKO7.MetaMPO

open Trace
open scoped Ordinal

/-! ## Symbols, heads, arguments -/

inductive Sym : Type
| void
| delta
| integrate
| merge
| app
| recΔ
| eqW
deriving DecidableEq, Repr

@[simp] def sym : Trace → Sym
  | void => .void
  | delta _ => .delta
  | integrate _ => .integrate
  | merge _ _ => .merge
  | app _ _ => .app
  | recΔ _ _ _ => .recΔ
  | eqW _ _ => .eqW

@[simp] def args : Trace → List Trace
  | void => []
  | delta t => [t]
  | integrate t => [t]
  | merge a b => [a, b]
  | app a b => [a, b]
  | recΔ b s n => [b, s, n]
  | eqW a b => [a, b]

/-! ## Fixed precedence -/

@[simp] def rank : Sym → Nat
  | .void => 0
  | .delta => 1
  | .merge => 2
  | .integrate => 3
  | .app => 4
  | .eqW => 5
  | .recΔ => 6

def symPrec (f g : Sym) : Prop := rank f < rank g

/-! ## KO7 MPO relation -/

/--
`MPO s t` means `s` strictly dominates `t`.

Constructors:
- `subEq`: direct subterm.
- `subGt`: transitive subterm descent through an argument.
- `byPrec`: precedence domination with recursive domination of RHS arguments.
- `recArg`: same-head multiset-style clause on `recΔ` (decrease in the third argument).
-/
inductive MPO : Trace → Trace → Prop
| subEq : ∀ {s u : Trace}, u ∈ args s → MPO s u
| subGt : ∀ {s u t : Trace}, u ∈ args s → MPO u t → MPO s t
| byPrec : ∀ {s t : Trace},
    symPrec (sym t) (sym s) →
    (∀ u, u ∈ args t → MPO s u) →
    MPO s t
| recArg : ∀ {b s n n' : Trace},
    MPO n' n →
    MPO (recΔ b s n') (recΔ b s n)

/-! ## Helpers -/

theorem mpo_subterm {s t : Trace} (h : t ∈ args s) : MPO s t :=
  MPO.subEq h

theorem mpo_subterm_of {s u t : Trace} (hmem : u ∈ args s) (hgt : MPO u t) : MPO s t :=
  MPO.subGt hmem hgt

theorem mpo_delta_arg (n : Trace) : MPO (delta n) n :=
  mpo_subterm (s := delta n) (t := n) (by simp [args])

/-! ## Rule orientation lemmas -/

theorem mpo_R_int_delta (t : Trace) : MPO (integrate (delta t)) void :=
  MPO.byPrec
    (s := integrate (delta t)) (t := void)
    (by simp [symPrec, rank, sym])
    (by intro u hu; cases hu)

theorem mpo_R_merge_void_left (t : Trace) : MPO (merge void t) t :=
  mpo_subterm (s := merge void t) (t := t) (by simp [args])

theorem mpo_R_merge_void_right (t : Trace) : MPO (merge t void) t :=
  mpo_subterm (s := merge t void) (t := t) (by simp [args])

theorem mpo_R_merge_cancel (t : Trace) : MPO (merge t t) t :=
  mpo_subterm (s := merge t t) (t := t) (by simp [args])

theorem mpo_R_rec_zero (base step : Trace) : MPO (recΔ base step void) base :=
  mpo_subterm (s := recΔ base step void) (t := base) (by simp [args])

theorem mpo_R_rec_inner (base step n : Trace) :
    MPO (recΔ base step (delta n)) (recΔ base step n) :=
  MPO.recArg (b := base) (s := step) (n' := delta n) (n := n) (mpo_delta_arg n)

theorem mpo_R_rec_succ (base step n : Trace) :
    MPO (recΔ base step (delta n)) (app step (recΔ base step n)) :=
  MPO.byPrec
    (s := recΔ base step (delta n)) (t := app step (recΔ base step n))
    (by simp [symPrec, rank, sym])
    (by
      intro u hu
      have hu' : u = step ∨ u = recΔ base step n := by
        simpa [args] using hu
      rcases hu' with rfl | rfl
      · exact MPO.subEq (by simp [args])
      · exact mpo_R_rec_inner base step n)

theorem mpo_R_eq_refl (x : Trace) : MPO (eqW x x) void :=
  MPO.byPrec
    (s := eqW x x) (t := void)
    (by simp [symPrec, rank, sym])
    (by intro u hu; cases hu)

theorem mpo_R_eq_to_merge (x y : Trace) : MPO (eqW x y) (merge x y) :=
  MPO.byPrec
    (s := eqW x y) (t := merge x y)
    (by simp [symPrec, rank, sym])
    (by
      intro u hu
      have hu' : u = x ∨ u = y := by
        simpa [args] using hu
      rcases hu' with rfl | rfl
      · exact MPO.subEq (by simp [args])
      · exact MPO.subEq (by simp [args]))

theorem mpo_R_eq_diff (x y : Trace) : MPO (eqW x y) (integrate (merge x y)) :=
  MPO.byPrec
    (s := eqW x y) (t := integrate (merge x y))
    (by simp [symPrec, rank, sym])
    (by
      intro u hu
      have hu' : u = merge x y := by simpa [args] using hu
      subst hu'
      exact mpo_R_eq_to_merge x y)

/-! ## Master theorem -/

theorem mpo_orients_step : ∀ {a b : Trace}, Step a b → MPO a b
  | _, _, Step.R_int_delta t => mpo_R_int_delta t
  | _, _, Step.R_merge_void_left t => mpo_R_merge_void_left t
  | _, _, Step.R_merge_void_right t => mpo_R_merge_void_right t
  | _, _, Step.R_merge_cancel t => mpo_R_merge_cancel t
  | _, _, Step.R_rec_zero b s => mpo_R_rec_zero b s
  | _, _, Step.R_rec_succ b s n => mpo_R_rec_succ b s n
  | _, _, Step.R_eq_refl a => mpo_R_eq_refl a
  | _, _, Step.R_eq_diff a b => mpo_R_eq_diff a b

/-! ## Ordinal ranking and well-foundedness -/

/-- Payload used for binary constructors. The outer successor guarantees the payload is never
itself a fixed point of `ω^·`, so positive-rank Veblen values strictly dominate it. -/
@[simp] noncomputable def pairPayload (a b : Ordinal.{0}) : Ordinal.{0} :=
  Order.succ ((ω : Ordinal) ^ (Order.succ a) + b)

/-- Payload used for the `recΔ` constructor. The nested `ω`-powers give a strict code for the
base and step arguments, and the outer successor keeps the payload non-limit. -/
@[simp] noncomputable def triplePayload (a b c : Ordinal.{0}) : Ordinal.{0} :=
  Order.succ ((ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) + c)

/-- Ordinal ranking for the specialized KO7 MPO. -/
@[simp] noncomputable def mpoOrd : Trace → Ordinal.{0}
  | void => Ordinal.veblen 0 0
  | delta t => Ordinal.veblen 1 (Order.succ (mpoOrd t))
  | integrate t => Ordinal.veblen 3 (Order.succ (mpoOrd t))
  | merge a b => Ordinal.veblen 2 (pairPayload (mpoOrd a) (mpoOrd b))
  | app a b => Ordinal.veblen 4 (pairPayload (mpoOrd a) (mpoOrd b))
  | recΔ b s n => Ordinal.veblen 6 (triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n))
  | eqW a b => Ordinal.veblen 5 (pairPayload (mpoOrd a) (mpoOrd b))

/-- The raw payload sitting under the Veblen head. -/
@[simp] noncomputable def payloadOrd : Trace → Ordinal.{0}
  | void => 0
  | delta t => Order.succ (mpoOrd t)
  | integrate t => Order.succ (mpoOrd t)
  | merge a b => pairPayload (mpoOrd a) (mpoOrd b)
  | app a b => pairPayload (mpoOrd a) (mpoOrd b)
  | recΔ b s n => triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n)
  | eqW a b => pairPayload (mpoOrd a) (mpoOrd b)

lemma mpoOrd_eq_veblen_payload (t : Trace) :
    mpoOrd t = Ordinal.veblen (rank (sym t)) (payloadOrd t) := by
  cases t <;> simp [mpoOrd, payloadOrd, sym, rank]

lemma ordNat_pos {n : Nat} (h : 0 < n) : (0 : Ordinal.{0}) < (n : Ordinal.{0}) := by
  exact_mod_cast h

lemma veblen_fixed_of_pos {k x : Ordinal.{0}} (hk : 0 < k) :
    (ω : Ordinal.{0}) ^ (Ordinal.veblen k x) = Ordinal.veblen k x := by
  simpa [Ordinal.veblen_zero_apply] using (Ordinal.veblen_veblen_of_lt hk x)

lemma veblen_gt_one_of_pos {k x : Ordinal.{0}} (hk : 0 < k) :
    (1 : Ordinal.{0}) < Ordinal.veblen k x := by
  have hk1 : (1 : Ordinal.{0}) ≤ k := by
    simpa using (Order.succ_le_of_lt hk : Order.succ (0 : Ordinal.{0}) ≤ k)
  have hε : Ordinal.veblen 1 0 ≤ Ordinal.veblen k 0 :=
    (Ordinal.veblen_zero_le_veblen_zero).2 hk1
  have hx : Ordinal.veblen k 0 ≤ Ordinal.veblen k x :=
    (Ordinal.veblen_right_strictMono k).monotone (Ordinal.zero_le x)
  have h1ε : (1 : Ordinal.{0}) < Ordinal.veblen 1 0 := by
    exact Ordinal.one_lt_omega0.trans <|
      (by simpa [Ordinal.epsilon] using (Ordinal.omega0_lt_epsilon 0))
  exact h1ε.trans_le (hε.trans hx)

lemma veblen_isSuccLimit_of_pos {k x : Ordinal.{0}} (hk : 0 < k) :
    Order.IsSuccLimit (Ordinal.veblen k x) := by
  have hprin : Ordinal.Principal (· + ·) (Ordinal.veblen k x) := by
    simpa [veblen_fixed_of_pos hk] using
      (Ordinal.principal_add_omega0_opow (Ordinal.veblen k x))
  exact Ordinal.isSuccLimit_of_principal_add (veblen_gt_one_of_pos hk) hprin

lemma lt_veblen_of_nonlimit {k p : Ordinal.{0}} (hk : 0 < k) (hp : ¬ Order.IsSuccLimit p) :
    p < Ordinal.veblen k p := by
  have hle : p ≤ Ordinal.veblen k p := Ordinal.right_le_veblen k p
  exact lt_of_le_of_ne hle (fun hEq => hp (hEq ▸ veblen_isSuccLimit_of_pos hk))

lemma mpoOrd_gt_one_of_rank_pos {t : Trace} (h : 0 < rank (sym t)) : (1 : Ordinal.{0}) < mpoOrd t := by
  rw [mpoOrd_eq_veblen_payload]
  exact veblen_gt_one_of_pos (ordNat_pos h)

lemma mpoOrd_fixed_of_rank_pos {t : Trace} (h : 0 < rank (sym t)) :
    (ω : Ordinal.{0}) ^ mpoOrd t = mpoOrd t := by
  rw [mpoOrd_eq_veblen_payload]
  exact veblen_fixed_of_pos (ordNat_pos h)

lemma mpoOrd_isSuccLimit_of_rank_pos {t : Trace} (h : 0 < rank (sym t)) :
    Order.IsSuccLimit (mpoOrd t) := by
  rw [mpoOrd_eq_veblen_payload]
  exact veblen_isSuccLimit_of_pos (ordNat_pos h)

lemma left_lt_pairPayload (a b : Ordinal.{0}) : a < pairPayload a b := by
  have hcore : a < (ω : Ordinal) ^ (Order.succ a) + b := by
    have hpow : Order.succ a ≤ (ω : Ordinal) ^ (Order.succ a) :=
      Ordinal.right_le_opow (Order.succ a) Ordinal.one_lt_omega0
    exact lt_of_lt_of_le (Order.lt_succ a) (hpow.trans (Ordinal.le_add_right _ _))
  exact hcore.trans (Order.lt_succ _)

lemma right_lt_pairPayload (a b : Ordinal.{0}) : b < pairPayload a b := by
  exact lt_of_le_of_lt (Ordinal.le_add_left b ((ω : Ordinal) ^ (Order.succ a))) (Order.lt_succ _)

lemma pairPayload_lt_of_lt {a b α : Ordinal.{0}}
    (ha : a < α) (hb : b < α)
    (hlim : Order.IsSuccLimit α) (hfix : (ω : Ordinal) ^ α = α) :
    pairPayload a b < α := by
  have hsucc : Order.succ a < α := hlim.succ_lt ha
  have hpow : (ω : Ordinal) ^ (Order.succ a) < α := by
    rw [← hfix]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 hsucc
  have hprin : Ordinal.Principal (· + ·) α := by
    simpa [hfix] using (Ordinal.principal_add_omega0_opow α)
  have hcore : (ω : Ordinal) ^ (Order.succ a) + b < α := hprin hpow hb
  exact hlim.succ_lt hcore

lemma first_lt_triplePayload (a b c : Ordinal.{0}) : a < triplePayload a b c := by
  have hexp : Order.succ a ≤ (ω : Ordinal) ^ (Order.succ a) + Order.succ b := by
    exact (Ordinal.right_le_opow (Order.succ a) Ordinal.one_lt_omega0).trans
      (Ordinal.le_add_right _ _)
  have hpow : a < (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) := by
    have hexp' : (ω : Ordinal) ^ (Order.succ a) + Order.succ b ≤
        (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) :=
      Ordinal.right_le_opow ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) Ordinal.one_lt_omega0
    exact lt_of_lt_of_le (Order.lt_succ a) (hexp.trans hexp')
  have hcore :
      a < (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) + c := by
    exact lt_of_lt_of_le hpow (Ordinal.le_add_right _ _)
  exact hcore.trans (Order.lt_succ _)

lemma second_lt_triplePayload (a b c : Ordinal.{0}) : b < triplePayload a b c := by
  have hexp : Order.succ b ≤ (ω : Ordinal) ^ (Order.succ a) + Order.succ b := by
    exact Ordinal.le_add_left (Order.succ b) ((ω : Ordinal) ^ (Order.succ a))
  have hpow : b < (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) := by
    have hexp' : (ω : Ordinal) ^ (Order.succ a) + Order.succ b ≤
        (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) :=
      Ordinal.right_le_opow ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) Ordinal.one_lt_omega0
    exact lt_of_lt_of_le (Order.lt_succ b) (hexp.trans hexp')
  have hcore :
      b < (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) + c := by
    exact lt_of_lt_of_le hpow (Ordinal.le_add_right _ _)
  exact hcore.trans (Order.lt_succ _)

lemma third_lt_triplePayload (a b c : Ordinal.{0}) : c < triplePayload a b c := by
  exact lt_of_le_of_lt
    (Ordinal.le_add_left c ((ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b)))
    (Order.lt_succ _)

lemma triplePayload_lt_of_lt {a b c α : Ordinal.{0}}
    (ha : a < α) (hb : b < α) (hc : c < α)
    (hlim : Order.IsSuccLimit α) (hfix : (ω : Ordinal) ^ α = α) :
    triplePayload a b c < α := by
  have hsuccA : Order.succ a < α := hlim.succ_lt ha
  have hsuccB : Order.succ b < α := hlim.succ_lt hb
  have hpowA : (ω : Ordinal) ^ (Order.succ a) < α := by
    rw [← hfix]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 hsuccA
  have hprin : Ordinal.Principal (· + ·) α := by
    simpa [hfix] using (Ordinal.principal_add_omega0_opow α)
  have hexp : (ω : Ordinal) ^ (Order.succ a) + Order.succ b < α := hprin hpowA hsuccB
  have hpow : (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) < α := by
    rw [← hfix]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 hexp
  have hcore :
      (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) + c < α := hprin hpow hc
  exact hlim.succ_lt hcore

lemma triplePayload_strictMono_right (a b : Ordinal.{0}) {c c' : Ordinal.{0}} (hc : c < c') :
    triplePayload a b c < triplePayload a b c' := by
  dsimp [triplePayload]
  have hcore :
      (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) + c <
      (ω : Ordinal) ^ ((ω : Ordinal) ^ (Order.succ a) + Order.succ b) + c' := by
    exact add_lt_add_left hc _
  exact (Order.succ_lt_succ_iff).2 hcore

lemma mpoOrd_lt_delta_arg (t : Trace) : mpoOrd t < mpoOrd (delta t) := by
  have hpayload : Order.succ (mpoOrd t) < mpoOrd (delta t) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 1) (p := Order.succ (mpoOrd t))
        (by exact_mod_cast (show 0 < (1 : Nat) by decide))
        (Order.not_isSuccLimit_succ (mpoOrd t)))
  exact (Order.lt_succ _).trans hpayload

lemma mpoOrd_lt_integrate_arg (t : Trace) : mpoOrd t < mpoOrd (integrate t) := by
  have hpayload : Order.succ (mpoOrd t) < mpoOrd (integrate t) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 3) (p := Order.succ (mpoOrd t))
        (by exact_mod_cast (show 0 < (3 : Nat) by decide))
        (Order.not_isSuccLimit_succ (mpoOrd t)))
  exact (Order.lt_succ _).trans hpayload

lemma mpoOrd_lt_merge_left (a b : Trace) : mpoOrd a < mpoOrd (merge a b) := by
  have hpayload : pairPayload (mpoOrd a) (mpoOrd b) < mpoOrd (merge a b) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 2) (p := pairPayload (mpoOrd a) (mpoOrd b))
        (by exact_mod_cast (show 0 < (2 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (left_lt_pairPayload _ _).trans hpayload

lemma mpoOrd_lt_merge_right (a b : Trace) : mpoOrd b < mpoOrd (merge a b) := by
  have hpayload : pairPayload (mpoOrd a) (mpoOrd b) < mpoOrd (merge a b) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 2) (p := pairPayload (mpoOrd a) (mpoOrd b))
        (by exact_mod_cast (show 0 < (2 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (right_lt_pairPayload _ _).trans hpayload

lemma mpoOrd_lt_app_left (a b : Trace) : mpoOrd a < mpoOrd (app a b) := by
  have hpayload : pairPayload (mpoOrd a) (mpoOrd b) < mpoOrd (app a b) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 4) (p := pairPayload (mpoOrd a) (mpoOrd b))
        (by exact_mod_cast (show 0 < (4 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (left_lt_pairPayload _ _).trans hpayload

lemma mpoOrd_lt_app_right (a b : Trace) : mpoOrd b < mpoOrd (app a b) := by
  have hpayload : pairPayload (mpoOrd a) (mpoOrd b) < mpoOrd (app a b) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 4) (p := pairPayload (mpoOrd a) (mpoOrd b))
        (by exact_mod_cast (show 0 < (4 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (right_lt_pairPayload _ _).trans hpayload

lemma mpoOrd_lt_eqW_left (a b : Trace) : mpoOrd a < mpoOrd (eqW a b) := by
  have hpayload : pairPayload (mpoOrd a) (mpoOrd b) < mpoOrd (eqW a b) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 5) (p := pairPayload (mpoOrd a) (mpoOrd b))
        (by exact_mod_cast (show 0 < (5 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (left_lt_pairPayload _ _).trans hpayload

lemma mpoOrd_lt_eqW_right (a b : Trace) : mpoOrd b < mpoOrd (eqW a b) := by
  have hpayload : pairPayload (mpoOrd a) (mpoOrd b) < mpoOrd (eqW a b) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 5) (p := pairPayload (mpoOrd a) (mpoOrd b))
        (by exact_mod_cast (show 0 < (5 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (right_lt_pairPayload _ _).trans hpayload

lemma mpoOrd_lt_rec_base (b s n : Trace) : mpoOrd b < mpoOrd (recΔ b s n) := by
  have hpayload : triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n) < mpoOrd (recΔ b s n) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 6) (p := triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n))
        (by exact_mod_cast (show 0 < (6 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (first_lt_triplePayload _ _ _).trans hpayload

lemma mpoOrd_lt_rec_step (b s n : Trace) : mpoOrd s < mpoOrd (recΔ b s n) := by
  have hpayload : triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n) < mpoOrd (recΔ b s n) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 6) (p := triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n))
        (by exact_mod_cast (show 0 < (6 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (second_lt_triplePayload _ _ _).trans hpayload

lemma mpoOrd_lt_rec_counter (b s n : Trace) : mpoOrd n < mpoOrd (recΔ b s n) := by
  have hpayload : triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n) < mpoOrd (recΔ b s n) := by
    simpa using
      (lt_veblen_of_nonlimit (k := 6) (p := triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n))
        (by exact_mod_cast (show 0 < (6 : Nat) by decide))
        (Order.not_isSuccLimit_succ _))
  exact (third_lt_triplePayload _ _ _).trans hpayload

lemma mpoOrd_arg_lt_of_mem {s u : Trace} (h : u ∈ args s) : mpoOrd u < mpoOrd s := by
  cases s with
  | void => cases h
  | delta t =>
      have hu : u = t := by simpa [args] using h
      simpa [hu] using mpoOrd_lt_delta_arg t
  | integrate t =>
      have hu : u = t := by simpa [args] using h
      simpa [hu] using mpoOrd_lt_integrate_arg t
  | merge a b =>
      have hu : u = a ∨ u = b := by simpa [args] using h
      rcases hu with hu | hu
      · simpa [hu] using mpoOrd_lt_merge_left a b
      · simpa [hu] using mpoOrd_lt_merge_right a b
  | app a b =>
      have hu : u = a ∨ u = b := by simpa [args] using h
      rcases hu with hu | hu
      · simpa [hu] using mpoOrd_lt_app_left a b
      · simpa [hu] using mpoOrd_lt_app_right a b
  | recΔ b step n =>
      have hu : u = b ∨ u = step ∨ u = n := by simpa [args] using h
      rcases hu with hu | hrest
      · simpa [hu] using mpoOrd_lt_rec_base b step n
      · rcases hrest with hu | hu
        · simpa [hu] using mpoOrd_lt_rec_step b step n
        · simpa [hu] using mpoOrd_lt_rec_counter b step n
  | eqW a b =>
      have hu : u = a ∨ u = b := by simpa [args] using h
      rcases hu with hu | hu
      · simpa [hu] using mpoOrd_lt_eqW_left a b
      · simpa [hu] using mpoOrd_lt_eqW_right a b

lemma payloadOrd_lt_of_args_lt {s t : Trace}
    (hs : 0 < rank (sym s))
    (hargs : ∀ u, u ∈ args t → mpoOrd u < mpoOrd s) :
    payloadOrd t < mpoOrd s := by
  have hlim : Order.IsSuccLimit (mpoOrd s) := mpoOrd_isSuccLimit_of_rank_pos hs
  have hfix : (ω : Ordinal) ^ mpoOrd s = mpoOrd s := mpoOrd_fixed_of_rank_pos hs
  cases t with
  | void =>
      exact zero_lt_one.trans (mpoOrd_gt_one_of_rank_pos hs)
  | delta u =>
      have hsmall : mpoOrd u < mpoOrd s := hargs u (by simp [args])
      exact Order.IsSuccLimit.succ_lt (α := Ordinal) hlim hsmall
  | integrate u =>
      have hsmall : mpoOrd u < mpoOrd s := hargs u (by simp [args])
      exact Order.IsSuccLimit.succ_lt (α := Ordinal) hlim hsmall
  | merge a b =>
      have hleft : mpoOrd a < mpoOrd s := hargs a (by simp [args])
      have hright : mpoOrd b < mpoOrd s := hargs b (by simp [args])
      exact pairPayload_lt_of_lt (a := mpoOrd a) (b := mpoOrd b) (α := mpoOrd s)
        hleft hright hlim hfix
  | app a b =>
      have hleft : mpoOrd a < mpoOrd s := hargs a (by simp [args])
      have hright : mpoOrd b < mpoOrd s := hargs b (by simp [args])
      exact pairPayload_lt_of_lt (a := mpoOrd a) (b := mpoOrd b) (α := mpoOrd s)
        hleft hright hlim hfix
  | recΔ b step n =>
      have hbase : mpoOrd b < mpoOrd s := hargs b (by simp [args])
      have hstep : mpoOrd step < mpoOrd s := hargs step (by simp [args])
      have hctr : mpoOrd n < mpoOrd s := hargs n (by simp [args])
      exact triplePayload_lt_of_lt (a := mpoOrd b) (b := mpoOrd step) (c := mpoOrd n) (α := mpoOrd s)
        hbase hstep hctr
        hlim hfix
  | eqW a b =>
      have hleft : mpoOrd a < mpoOrd s := hargs a (by simp [args])
      have hright : mpoOrd b < mpoOrd s := hargs b (by simp [args])
      exact pairPayload_lt_of_lt (a := mpoOrd a) (b := mpoOrd b) (α := mpoOrd s)
        hleft hright hlim hfix

lemma mpoOrd_lt_of_byPrec {s t : Trace}
    (hprec : symPrec (sym t) (sym s))
    (hargs : ∀ u, u ∈ args t → mpoOrd u < mpoOrd s) :
    mpoOrd t < mpoOrd s := by
  have hs : 0 < rank (sym s) := Nat.zero_lt_of_lt hprec
  have hpayload : payloadOrd t < mpoOrd s := payloadOrd_lt_of_args_lt hs hargs
  have hprecOrd : ((rank (sym t)) : Ordinal) < ((rank (sym s)) : Ordinal) := by
    exact_mod_cast hprec
  rw [mpoOrd_eq_veblen_payload t, mpoOrd_eq_veblen_payload s]
  have hpayload' : payloadOrd t < Ordinal.veblen (rank (sym s)) (payloadOrd s) := by
    simpa [mpoOrd_eq_veblen_payload s] using hpayload
  exact (Ordinal.veblen_lt_veblen_iff).2 (Or.inr (Or.inl ⟨hprecOrd, hpayload'⟩))

/-- Every MPO step strictly decreases the ordinal rank `mpoOrd`. -/
theorem mpoOrd_strict_of_mpo {a b : Trace} (h : MPO a b) : mpoOrd b < mpoOrd a := by
  induction h with
  | subEq hmem =>
      exact mpoOrd_arg_lt_of_mem hmem
  | subGt hmem hgt ih =>
      exact ih.trans (mpoOrd_arg_lt_of_mem hmem)
  | byPrec hprec hargs ih =>
      exact mpoOrd_lt_of_byPrec hprec (fun u hu => ih u hu)
  | recArg hgt ih =>
      rw [mpoOrd_eq_veblen_payload (recΔ _ _ _), mpoOrd_eq_veblen_payload (recΔ _ _ _)]
      exact (Ordinal.veblen_lt_veblen_iff_right).2
        (triplePayload_strictMono_right _ _ ih)

/-- Reverse MPO relation. -/
def MPORev : Trace → Trace → Prop := fun a b => MPO b a

/-- The specialized KO7 MPO is well-founded in reverse. -/
theorem wf_MPORev : WellFounded MPORev := by
  let R : Trace → Trace → Prop := fun a b => (mpoOrd a : Ordinal) < mpoOrd b
  have wf_measure : WellFounded R := InvImage.wf mpoOrd Ordinal.lt_wf
  have hsub : Subrelation MPORev R := by
    intro a b hab
    exact mpoOrd_strict_of_mpo hab
  exact Subrelation.wf hsub wf_measure

/-- Full root-step termination derived from the MPO development. -/
theorem wf_StepRev_mpo : WellFounded (fun a b : Trace => Step b a) := by
  have hsub : Subrelation (fun a b : Trace => Step b a) MPORev := by
    intro a b hstep
    exact mpo_orients_step hstep
  exact Subrelation.wf hsub wf_MPORev

end OperatorKO7.MetaMPO
