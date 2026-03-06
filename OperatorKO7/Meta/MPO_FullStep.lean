import OperatorKO7.Kernel

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

end OperatorKO7.MetaMPO
