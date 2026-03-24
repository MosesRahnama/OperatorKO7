import OperatorKO7.Meta.SafeStepCtx_Complexity_Exponential
import OperatorKO7.Meta.SafeStep_Complexity_MW_Root

/-!
# Finite-note Cichon packaging of the sharpened contextual bound

This module repackages the new single-exponential `SafeStepCtx` bound in the
same ordinal/Cichon vocabulary used elsewhere in the artifact.

Unlike the conservative `mwCtxBound` theorem, this file does not lift an
existing ordinal calibration block. Instead it attaches the already-proved
single-exponential size bound to a finite note and observes that the
corresponding `cichon` value agrees exactly with that finite payload.

So this is a proof-theoretic wrapper around the sharpened contextual theorem,
not a new tighter extraction argument.
-/

open OperatorKO7
open OperatorKO7.Trace
open scoped Classical
open Ordinal

namespace MetaSN_KO7

open OperatorKO7.OrdinalHierarchy
open OperatorKO7.MetaDM
open ONote
open NONote

/-- Finite note carrying the already-proved single-exponential contextual bound. -/
def ctxExpNote (t : Trace) : NONote :=
  lex3Note (0, ((0 : Multiset Nat), contextualExpBound (termSize t)))

/-- Cichon packaging of the sharpened contextual exponential bound. -/
def ctxExpCichonBound (t : Trace) : Nat :=
  OperatorKO7.OrdinalHierarchy.cichon (ctxExpNote t).1 0

theorem repr_ctxExpNote (t : Trace) :
    NONote.repr (ctxExpNote t) = (contextualExpBound (termSize t) : Ordinal) := by
  simp [ctxExpNote, repr_lex3Note, MetaDM.lex3cToOrd, MetaDM.lexDMToOrd]

theorem ctxExpNote_lt_omega (t : Trace) :
    NONote.repr (ctxExpNote t) < (ω : Ordinal) := by
  rw [repr_ctxExpNote]
  exact Ordinal.nat_lt_omega0 (contextualExpBound (termSize t))

theorem contextualExpBound_le_ctxExpCichonBound (t : Trace) :
    contextualExpBound (termSize t) ≤ ctxExpCichonBound t := by
  unfold ctxExpCichonBound ctxExpNote
  simpa [Nat.zero_add] using
    (OperatorKO7.OrdinalHierarchy.exactControlledPow_length_le_cichon
      (exactControlledPow_tau_drop
        (δ := 0) (τ := 0) (m := contextualExpBound (termSize t))
        (k := 0) (κ := (0 : Multiset Nat))))

/-- The new single-exponential contextual theorem packaged through the Cichon hierarchy
on a finite note carrying the already-proved explicit exponential bound. -/
theorem safeStepCtx_length_le_ctxExpCichonBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n + 1 ≤ ctxExpCichonBound t := by
  exact le_trans (safeStepCtx_length_le_contextualExpBound t u n h)
    (contextualExpBound_le_ctxExpCichonBound t)

/-- Paper-facing alias for the finite-note Cichon wrapper around the sharpened
single-exponential contextual theorem. -/
theorem safestepctx_length_le_ctxExpCichonBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n + 1 ≤ ctxExpCichonBound t := by
  exact safeStepCtx_length_le_ctxExpCichonBound t u n h

end MetaSN_KO7
