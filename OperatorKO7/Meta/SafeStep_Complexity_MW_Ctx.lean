import OperatorKO7.Meta.SafeStep_Complexity_MW_Root
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal

/-!
# Context-closed MW-style complexity bound

This module packages the existing contextual derivation-length theorem
`safeStepCtx_length_le_ctxFuel` into the same `lex3Note` / `cichon` hierarchy family
used on the root side.

The contextual relation does not reuse the exact root-side ordinal descent directly:
congruence steps can move below the current root while preserving the outer `lex3`
payload. Instead, we lift the already-certified contextual fuel `ctxFuel` into the
finite tail of the same notation family. The resulting bound remains below `ω^ω * 2`
and is expressed by the genuine Cichon hierarchy on `ONote`.
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

/-- Contextual MW note: keep the calibrated `δ` / `κᴹ` payload and replace the finite tail by
    the already-certified contextual fuel. -/
def mwCtxNote (t : Trace) : NONote :=
  lex3Note (deltaFlag t, (MetaSN_DM.kappaM t, ctxFuel t))

/-- Contextual MW bound expressed by the Cichon hierarchy on the contextual note. -/
def mwCtxBound (t : Trace) : Nat :=
  OperatorKO7.OrdinalHierarchy.cichon (mwCtxNote t).1 0

theorem repr_mwCtxNote (t : Trace) :
    NONote.repr (mwCtxNote t) =
      lex3cToOrd (deltaFlag t, (MetaSN_DM.kappaM t, ctxFuel t)) := by
  simp [mwCtxNote, repr_lex3Note]

/-- The contextual MW note still lives below the same `ω^ω * 2` calibration block. -/
theorem mwCtxNote_lt_opow_omega_mul_two (t : Trace) :
    NONote.repr (mwCtxNote t) < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) := by
  rw [repr_mwCtxNote]
  have hδ : deltaFlag t ≤ 1 := by
    rcases deltaFlag_range t with h0 | h1 <;> omega
  exact lex3cToOrd_lt_opow_omega_mul_two hδ

/-- A concrete contextual counterexample showing that the root-side calibrated `μ3c`
    measure does not itself decrease on every `SafeStepCtx` step. -/
def ctxOrdinalObstructionSeed : Trace :=
  recΔ void void void

/-- Source of the contextual obstruction: perform `rec_succ` under `integrate`. -/
def ctxOrdinalObstructionSource : Trace :=
  integrate (recΔ void void (delta ctxOrdinalObstructionSeed))

/-- Target of the contextual obstruction: the inner `rec_succ` step duplicates the
    recursive payload and increases the outer calibrated root note. -/
def ctxOrdinalObstructionTarget : Trace :=
  integrate (app void (recΔ void void ctxOrdinalObstructionSeed))

theorem ctxOrdinalObstruction_step :
    SafeStepCtx ctxOrdinalObstructionSource ctxOrdinalObstructionTarget := by
  exact SafeStepCtx.integrate
    (SafeStepCtx.root (SafeStep.R_rec_succ void void ctxOrdinalObstructionSeed))

private theorem ctxOrdinalObstruction_dm :
    DM (MetaSN_DM.kappaM ctxOrdinalObstructionSource)
      (MetaSN_DM.kappaM ctxOrdinalObstructionTarget) := by
  refine ⟨(1 ::ₘ 0), (1 ::ₘ 0), (2 ::ₘ 0), by simp, ?_, ?_, ?_⟩
  · simp [ctxOrdinalObstructionSource, ctxOrdinalObstructionSeed, MetaSN_DM.kappaM,
      MetaSN_DM.weight]
  · ext x
    by_cases h1 : x = 1
    · subst h1
      simp [ctxOrdinalObstructionTarget, ctxOrdinalObstructionSeed, MetaSN_DM.kappaM,
        MetaSN_DM.weight]
    · by_cases h2 : x = 2
      · subst h2
        simp [ctxOrdinalObstructionTarget, ctxOrdinalObstructionSeed, MetaSN_DM.kappaM,
          MetaSN_DM.weight]
      · simp [ctxOrdinalObstructionTarget, ctxOrdinalObstructionSeed, MetaSN_DM.kappaM,
          MetaSN_DM.weight, h1, h2]
  · intro y hy
    have hy1 : y = 1 := by simpa using hy
    subst hy1
    exact ⟨2, by simp, by decide⟩

/-- The contextual obstruction strictly increases the calibrated root-side triple-lex
    measure, so no direct `μ3c` descent theorem can extend from `SafeStep` to
    `SafeStepCtx`. -/
theorem ctxOrdinalObstruction_measure_increases :
    Lex3c (mu3c ctxOrdinalObstructionSource) (mu3c ctxOrdinalObstructionTarget) := by
  have hinner :
      LexDM_c (MetaSN_DM.kappaM ctxOrdinalObstructionSource, tau ctxOrdinalObstructionSource)
        (MetaSN_DM.kappaM ctxOrdinalObstructionTarget, tau ctxOrdinalObstructionTarget) := by
    exact dm_to_LexDM_c_left
      (τ₁ := tau ctxOrdinalObstructionSource)
      (τ₂ := tau ctxOrdinalObstructionTarget)
      ctxOrdinalObstruction_dm
  have hcore :
      Lex3c (0, (MetaSN_DM.kappaM ctxOrdinalObstructionSource, tau ctxOrdinalObstructionSource))
        (0, (MetaSN_DM.kappaM ctxOrdinalObstructionTarget, tau ctxOrdinalObstructionTarget)) :=
    Prod.Lex.right (a := (0 : Nat)) hinner
  simpa [ctxOrdinalObstructionSource, ctxOrdinalObstructionTarget, mu3c]
    using hcore

theorem ctxOrdinalObstruction_ord_increases :
    lex3cToOrd (mu3c ctxOrdinalObstructionSource) <
      lex3cToOrd (mu3c ctxOrdinalObstructionTarget) :=
  lex3cToOrd_strictMono ctxOrdinalObstruction_measure_increases

theorem ctxOrdinalObstruction_rootNote_increases :
    NONote.repr (mwRootNote ctxOrdinalObstructionSource) <
      NONote.repr (mwRootNote ctxOrdinalObstructionTarget) := by
  rw [repr_mwRootNote, repr_mwRootNote]
  exact ctxOrdinalObstruction_ord_increases

theorem not_ctxOrdinalObstruction_measure_drop :
    ¬ Lex3c (mu3c ctxOrdinalObstructionTarget) (mu3c ctxOrdinalObstructionSource) := by
  intro hdrop
  have hlt₁ := ctxOrdinalObstruction_ord_increases
  have hlt₂ := lex3cToOrd_strictMono hdrop
  exact lt_asymm hlt₁ hlt₂

theorem not_all_safeStepCtx_rootNote_drop :
    ¬ ∀ {a b : Trace}, SafeStepCtx a b →
        NONote.repr (mwRootNote b) < NONote.repr (mwRootNote a) := by
  intro hall
  have hlt₁ := ctxOrdinalObstruction_rootNote_increases
  have hlt₂ := hall ctxOrdinalObstruction_step
  exact lt_asymm hlt₁ hlt₂

/-- The calibrated root-side `μ3c` / `lex3Note` descent cannot by itself certify the
    full contextual relation. This is why the present file packages `ctxFuel` into the
    same note family instead of claiming a direct contextual fundamental-sequence descent. -/
theorem not_all_safeStepCtx_measure_drop :
    ¬ ∀ {a b : Trace}, SafeStepCtx a b → Lex3c (mu3c b) (mu3c a) := by
  intro hall
  exact not_ctxOrdinalObstruction_measure_drop (hall ctxOrdinalObstruction_step)

/-- The finite contextual tail already yields an exact controlled descent of length `ctxFuel t`. -/
theorem ctxFuel_le_mwCtxBound (t : Trace) :
    ctxFuel t ≤ mwCtxBound t := by
  unfold mwCtxBound mwCtxNote
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (OperatorKO7.OrdinalHierarchy.exactControlledPow_length_le_cichon
      (exactControlledPow_tau_drop
        (δ := deltaFlag t) (τ := 0) (m := ctxFuel t) (k := 0) (κ := MetaSN_DM.kappaM t)))

/-- Context-closed derivation lengths are bounded by the contextual MW Cichon value. -/
theorem safeStepCtx_length_le_mwCtxBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ mwCtxBound t := by
  exact le_trans (safeStepCtx_length_le_ctxFuel t u n h) (ctxFuel_le_mwCtxBound t)

/-- Alias matching the paper/roadmap naming convention. -/
theorem safestepctx_length_le_mwCtxBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ mwCtxBound t := by
  exact safeStepCtx_length_le_mwCtxBound t u n h

/-- Convenience corollary in the same style as the older size-based theorem. -/
theorem safestep_length_bounded_by_mwCtxBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ mwCtxBound t := by
  exact safeStepCtx_length_le_mwCtxBound t u n h

end MetaSN_KO7
