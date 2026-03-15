import OperatorKO7.Meta.MPO_FullStep

/-!
# Precedence-Sensitive MPO Barrier

This module complements the positive KO7-specialized MPO theorem with one explicit
negative precedence regime.

We keep the same KO7-specific MPO shape as `Meta/MPO_FullStep.lean`:
- subterm clause
- precedence clause
- same-head `recΔ` counter descent

The only change is the precedence order: here `app` is placed above `recΔ`.
Under that bad precedence, the duplicating rule already fails on the smallest
concrete `rec_succ` instance.
-/

namespace OperatorKO7.MPOPrecedenceBarrier

open Trace
open OperatorKO7.MetaMPO

/-- Bad precedence ranking: `app` is placed above `recΔ`. -/
@[simp] def rankBad : Sym → Nat
  | .void => 0
  | .delta => 1
  | .merge => 2
  | .integrate => 3
  | .recΔ => 4
  | .eqW => 5
  | .app => 6

/-- Strict precedence induced by `rankBad`. -/
def symPrecBad (f g : Sym) : Prop := rankBad f < rankBad g

/-- KO7 MPO with the bad precedence `app ≻ recΔ`. -/
inductive MPOBad : Trace → Trace → Prop
| subEq : ∀ {s u : Trace}, u ∈ args s → MPOBad s u
| subGt : ∀ {s u t : Trace}, u ∈ args s → MPOBad u t → MPOBad s t
| byPrec : ∀ {s t : Trace},
    symPrecBad (sym t) (sym s) →
    (∀ u, u ∈ args t → MPOBad s u) →
    MPOBad s t
| recArg : ∀ {b s n n' : Trace},
    MPOBad n' n →
    MPOBad (recΔ b s n') (recΔ b s n)

/-- In the bad precedence, `app` strictly outranks `recΔ`. -/
theorem app_outranks_rec : symPrecBad Sym.recΔ Sym.app := by
  simp [symPrecBad, rankBad]

/-- The smallest `rec_succ` source instance used for the bad-precedence witness. -/
@[simp] def badRecSuccSrc : Trace := recΔ void void (delta void)

/-- The corresponding `rec_succ` target instance. -/
@[simp] def badRecSuccTgt : Trace := app void (recΔ void void void)

theorem not_mpoBad_void_badRecSuccTgt :
    ¬ MPOBad void badRecSuccTgt := by
  intro h
  cases h with
  | subEq hmem =>
      simp [badRecSuccTgt, args] at hmem
  | subGt hmem _ =>
      simp [args] at hmem
  | byPrec hprec _ =>
      simp [symPrecBad, rankBad, sym, badRecSuccTgt] at hprec

theorem not_mpoBad_deltaVoid_badRecSuccTgt :
    ¬ MPOBad (delta void) badRecSuccTgt := by
  intro h
  cases h with
  | subEq hmem =>
      simp [badRecSuccTgt, args] at hmem
  | subGt hmem hinner =>
      simp [args] at hmem
      subst hmem
      exact not_mpoBad_void_badRecSuccTgt hinner
  | byPrec hprec _ =>
      simp [symPrecBad, rankBad, sym, badRecSuccTgt] at hprec

/-- Under the bad precedence `app ≻ recΔ`, the duplicating rule already fails on the
smallest concrete `rec_succ` instance. -/
theorem not_mpoBad_rec_succ_instance :
    ¬ MPOBad badRecSuccSrc badRecSuccTgt := by
  intro h
  cases h with
  | subEq hmem =>
      simp [badRecSuccSrc, badRecSuccTgt, args] at hmem
  | subGt hmem hinner =>
      simp [badRecSuccSrc, args] at hmem
      rcases hmem with rfl | rfl
      · exact not_mpoBad_void_badRecSuccTgt hinner
      · exact not_mpoBad_deltaVoid_badRecSuccTgt hinner
  | byPrec hprec _ =>
      simp [symPrecBad, rankBad, sym, badRecSuccSrc, badRecSuccTgt] at hprec

/-- Consequently, the bad-precedence KO7 MPO cannot orient all root steps. -/
theorem no_global_step_orientation_mpo_bad_prec :
    ¬ (∀ {a b : Trace}, Step a b → MPOBad a b) := by
  intro h
  exact
    not_mpoBad_rec_succ_instance
      (h (Step.R_rec_succ void void void))

end OperatorKO7.MPOPrecedenceBarrier
