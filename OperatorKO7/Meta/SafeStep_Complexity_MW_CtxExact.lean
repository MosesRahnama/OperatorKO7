import OperatorKO7.Meta.SafeStep_Complexity_MW_Root
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal

/-!
# Direct exact controlled descent for `SafeStepCtx`

This module gives a direct contextual fundamental-sequence extraction,
but on a new contextual note package rather than on the root-calibrated `mwRootNote`.

The note family is intentionally simple: we use the already-certified contextual
potential `ctxFuel` as the finite tail of a fresh note, and then prove that every
context-closed safe reduction induces an exact predecessor descent on that family.
This yields a direct `cichon` theorem for `SafeStepCtx` without reusing the
root-side note that is known to fail under contexts.
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

/-- Exact contextual note: discard the root calibration payload and keep only the
    finite contextual potential in a fresh exact-descent family. -/
def ctxExactNote (t : Trace) : NONote :=
  lex3Note (0, ((0 : Multiset Nat), ctxFuel t))

/-- Direct contextual hierarchy bound induced by the exact contextual note. -/
def ctxExactBound (t : Trace) : Nat :=
  OperatorKO7.OrdinalHierarchy.cichon (ctxExactNote t).1 0

theorem repr_ctxExactNote (t : Trace) :
    NONote.repr (ctxExactNote t) = (ctxFuel t : Ordinal) := by
  simp [ctxExactNote, repr_lex3Note, MetaDM.lex3cToOrd, MetaDM.lexDMToOrd]

theorem ctxExactNote_lt_omega (t : Trace) :
    NONote.repr (ctxExactNote t) < (ω : Ordinal) := by
  rw [repr_ctxExactNote]
  exact Ordinal.nat_lt_omega0 (ctxFuel t)

/-- Concatenation of exact controlled descent chains. -/
theorem exactControlledPow_append :
    ∀ {o r s : ONote} {k k' k'' n m : Nat},
      ExactControlledPow o k n r k' →
      ExactControlledPow r k' m s k'' →
      ExactControlledPow o k (n + m) s k''
    := by
  intro o r s k k' k'' n m h₁ h₂
  induction h₁ generalizing s k'' m with
  | refl o k =>
      simpa using h₂
  | succ hfs hrest ih =>
      have hcat := ih h₂
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExactControlledPow.succ hfs hcat
  | limit hfs hrest ih =>
      have hcat := ih h₂
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExactControlledPow.limit hfs hcat

/-- Every contextual step strictly decreases `ctxFuel`, hence induces an exact
    predecessor descent on the fresh contextual note family. -/
theorem safeStepCtx_exact_step {a b : Trace} (h : SafeStepCtx a b) (k : Nat) :
    ExactControlledPow (ctxExactNote a).1 k (ctxFuel a - ctxFuel b)
      (ctxExactNote b).1 (k + (ctxFuel a - ctxFuel b)) := by
  have hdrop : ctxFuel b < ctxFuel a := ctxFuel_decreases_ctx h
  have hsplit : ctxFuel a = ctxFuel b + (ctxFuel a - ctxFuel b) := by
    omega
  unfold ctxExactNote
  rw [hsplit]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exactControlledPow_tau_drop
      (δ := 0) (τ := ctxFuel b) (m := ctxFuel a - ctxFuel b)
      (k := k) (κ := (0 : Multiset Nat)))

/-- Along any contextual reduction chain, `ctxFuel` is monotone decreasing. -/
theorem safeStepCtxPow_ctxFuel_antitone (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    ctxFuel u ≤ ctxFuel t := by
  induction n generalizing t with
  | zero =>
      subst u
      exact le_rfl
  | succ n ih =>
      obtain ⟨v, hstep, hrest⟩ := h
      have hrest' := ih v hrest
      exact le_trans hrest' (Nat.le_of_lt (ctxFuel_decreases_ctx hstep))

/-- The exact contextual path length is the total contextual potential drop. -/
theorem safeStepCtxPow_exact_drop :
    ∀ {n : Nat} {t u : Trace} {k : Nat}, SafeStepCtxPow n t u →
      ExactControlledPow (ctxExactNote t).1 k (ctxFuel t - ctxFuel u)
        (ctxExactNote u).1 (k + (ctxFuel t - ctxFuel u))
  | 0, t, u, k, h => by
      subst u
      simpa using ExactControlledPow.refl (ctxExactNote t).1 k
  | n + 1, t, u, k, h => by
      obtain ⟨v, hstep, hrest⟩ := h
      have htv := safeStepCtx_exact_step hstep k
      have hvuMono : ctxFuel u ≤ ctxFuel v :=
        safeStepCtxPow_ctxFuel_antitone v u n hrest
      have hvu :=
        safeStepCtxPow_exact_drop (t := v) (u := u)
          (k := k + (ctxFuel t - ctxFuel v)) hrest
      have hsum : ctxFuel t - ctxFuel u =
          (ctxFuel t - ctxFuel v) + (ctxFuel v - ctxFuel u) := by
        have hstepMono : ctxFuel v ≤ ctxFuel t := Nat.le_of_lt (ctxFuel_decreases_ctx hstep)
        omega
      have hcat := exactControlledPow_append htv hvu
      simpa [hsum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcat

/-- Any `n`-step contextual chain consumes at least `n` units of contextual fuel. -/
theorem safeStepCtx_length_le_ctxFuel_drop (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ ctxFuel t - ctxFuel u := by
  induction n generalizing t with
  | zero =>
      subst u
      simp
  | succ n ih =>
      obtain ⟨v, hstep, hrest⟩ := h
      have hrestLen := ih v hrest
      have hrestMono : ctxFuel u ≤ ctxFuel v :=
        safeStepCtxPow_ctxFuel_antitone v u n hrest
      have hdrop : ctxFuel v < ctxFuel t := ctxFuel_decreases_ctx hstep
      omega

/-- Direct exact-control contextual extraction on the new contextual note family. -/
theorem safeStepCtx_length_le_ctxExactBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ ctxExactBound t := by
  have hlen : n ≤ ctxFuel t - ctxFuel u :=
    safeStepCtx_length_le_ctxFuel_drop t u n h
  have hpath :
      ExactControlledPow (ctxExactNote t).1 0 (ctxFuel t - ctxFuel u)
        (ctxExactNote u).1 (ctxFuel t - ctxFuel u) :=
    by
      simpa using
        (safeStepCtxPow_exact_drop (t := t) (u := u) (k := 0) h)
  have hbound : ctxFuel t - ctxFuel u ≤ ctxExactBound t := by
    unfold ctxExactBound
    exact OperatorKO7.OrdinalHierarchy.exactControlledPow_length_le_cichon hpath
  exact le_trans hlen hbound

/-- Paper-facing alias for the direct contextual exact-control theorem. -/
theorem safestepctx_length_le_ctxExactBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ ctxExactBound t := by
  exact safeStepCtx_length_le_ctxExactBound t u n h

end MetaSN_KO7
