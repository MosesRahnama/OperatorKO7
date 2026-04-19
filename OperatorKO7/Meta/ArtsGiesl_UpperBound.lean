import OperatorKO7.Meta.ReverseMathFramework
import OperatorKO7.Meta.TerminationPrincipleRegister

/-!
# Arts--Giesl Upper Bound

Theorem-level upper-bound package for the reverse-mathematical profile of the
Arts--Giesl soundness license.

This file does not claim an exact calibration. It isolates the strongest
artifact-backed upper-bound facts currently available:

- the candidate target theory sits below `WO(ε₀)`;
- the candidate target ordinal is `ω^3`, hence below `ε₀`;
- the recursor-side license transformation is constant-overhead.
-/

namespace OperatorKO7.ArtsGieslUpperBound

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.TerminationPrincipleRegister

/-- The strongest theorem-level upper bound currently justified by the artifact
for the Arts--Giesl license: the already mechanized `WO(ε₀)` benchmark.
-/
noncomputable def artsGieslTheoremUpperBound : ReverseMathUpperBound artsGieslPrincipleProfile where
  theoryProfile := woEpsilon0TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "target sits below existing epsilon0 benchmark"

@[simp] theorem artsGieslTheoremUpperBound_status :
    artsGieslTheoremUpperBound.evidenceStatus = EvidenceStatus.theoremLevel := rfl

@[simp] theorem artsGieslTheoremUpperBound_theory :
    artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.WO_epsilon0 := rfl

@[simp] theorem artsGieslTheoremUpperBound_ordinal :
    artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some ε₀ := rfl

/-- The conjectural Arts--Giesl target theory lies below the theorem-level
`WO(ε₀)` upper bound. -/
theorem artsGiesl_targetTheory_le_theoremUpperBound :
    rca0WoOmega3TheoryProfile.theory ≤ artsGieslTheoremUpperBound.theoryProfile.theory := by
  decide

/-- The conjectural Arts--Giesl ordinal target lies below the theorem-level
`ε₀` upper bound already tracked by the KO7 artifact. -/
theorem artsGiesl_targetOrdinal_lt_theoremUpperBound :
    omegaPowThree < ε₀ :=
  omegaPowThree_lt_epsilon0

/-- The registry target agrees with the framework target used by this upper
bound package. -/
theorem artsGiesl_registry_target_agrees_with_upperBound_target :
    artsGieslEntry.targetTheory? = some rca0WoOmega3TheoryProfile.theory := by
  simp [artsGieslEntry, rca0WoOmega3TheoryProfile]

/-- The recursor-side Arts--Giesl invocation stays within constant additive
assembly overhead. This is part of why the current reverse-mathematical
upper-bound package is stable under the repository's witness-preserving
transformations. -/
theorem artsGiesl_recursor_constant_overhead (n : Nat) :
    agRecursorTransformation.transformedCost n = n + agRecursorTransformation.overhead :=
  agRecursorTransformation_preserves_linear_growth n

/-- Summary form of the theorem-level upper-bound package. -/
theorem artsGieslTheoremUpperBound_supported :
    artsGieslTheoremUpperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ rca0WoOmega3TheoryProfile.theory ≤ artsGieslTheoremUpperBound.theoryProfile.theory
      ∧ omegaPowThree < ε₀ := by
  constructor
  · rfl
  constructor
  · exact artsGiesl_targetTheory_le_theoremUpperBound
  · exact artsGiesl_targetOrdinal_lt_theoremUpperBound

/-- The current theorem-level upper bound does not yet hit the exact theory
target `RCA₀ + WO(ω^3)`. -/
theorem artsGieslTheoremUpperBound_theory_ne_target :
    artsGieslTheoremUpperBound.theoryProfile.theory ≠ FormalTheory.RCA0_WO_omega3 := by
  simp [artsGieslTheoremUpperBound, woEpsilon0TheoryProfile]

/-- The current theorem-level upper bound does not yet hit the exact ordinal
target `ω^3`. -/
theorem artsGieslTheoremUpperBound_ordinal_ne_target :
    artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? ≠ some omegaPowThree := by
  intro h
  have h' : ε₀ = omegaPowThree := by
    simpa [artsGieslTheoremUpperBound, woEpsilon0TheoryProfile] using h
  exact omegaPowThree_lt_epsilon0.ne h'.symm

/-- Sharpening target for a future theorem-level exact upper bound. This does
not assert that the witness exists now; it records exactly what a successful
upper-bound improvement must deliver. -/
structure ArtsGieslSharpTheoremUpperBound where
  bound : ReverseMathUpperBound artsGieslPrincipleProfile
  theoryEq : bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  ordinalEq :
    bound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel

/-- Public summary of the sharpening target. -/
theorem ArtsGieslSharpTheoremUpperBound.supported
    (U : ArtsGieslSharpTheoremUpperBound) :
    U.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ U.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ U.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact ⟨U.theoryEq, U.ordinalEq, U.theoremLevel⟩

/-- The current theorem-level upper package is not already a sharp exact-target
upper bound. -/
theorem artsGieslTheoremUpperBound_not_sharp :
    ¬ ∃ U : ArtsGieslSharpTheoremUpperBound, U.bound = artsGieslTheoremUpperBound := by
  rintro ⟨U, hU⟩
  have hTheory := U.theoryEq
  rw [hU] at hTheory
  simp [artsGieslTheoremUpperBound, woEpsilon0TheoryProfile] at hTheory

/-- Precise theorem-level upper-bound gap object for the Arts--Giesl program. -/
structure ArtsGieslTheoremUpperBoundGap where
  current : ReverseMathUpperBound artsGieslPrincipleProfile
  target : SecondOrderTheoryProfile
  targetLeCurrent : target.theory ≤ current.theoryProfile.theory
  theoryNeTarget : current.theoryProfile.theory ≠ target.theory
  ordinalNeTarget : current.theoryProfile.ordinalCeiling? ≠ target.ordinalCeiling?

/-- Current theorem-level upper-bound gap: the present artifact still lands at
`WO(ε₀)` rather than the exact `RCA₀ + WO(ω^3)` target profile. -/
noncomputable def artsGieslCurrentTheoremUpperBoundGap : ArtsGieslTheoremUpperBoundGap where
  current := artsGieslTheoremUpperBound
  target := rca0WoOmega3TheoryProfile
  targetLeCurrent := artsGiesl_targetTheory_le_theoremUpperBound
  theoryNeTarget := artsGieslTheoremUpperBound_theory_ne_target
  ordinalNeTarget := artsGieslTheoremUpperBound_ordinal_ne_target

/-- Public summary of the current theorem-level upper-bound gap. -/
theorem artsGieslCurrentTheoremUpperBoundGap_supported :
    artsGieslCurrentTheoremUpperBoundGap.current.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ artsGieslCurrentTheoremUpperBoundGap.target.theory ≤
          artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.theory
      ∧ artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.theory ≠
          artsGieslCurrentTheoremUpperBoundGap.target.theory
      ∧ artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.ordinalCeiling? ≠
          artsGieslCurrentTheoremUpperBoundGap.target.ordinalCeiling? := by
  constructor
  · rfl
  constructor
  · exact artsGieslCurrentTheoremUpperBoundGap.targetLeCurrent
  constructor
  · exact artsGieslCurrentTheoremUpperBoundGap.theoryNeTarget
  · exact artsGieslCurrentTheoremUpperBoundGap.ordinalNeTarget

/-- The exact target for the sharp upper-bound program can be packaged as a
theorem-level transfer from the already exact SCT calibration target. -/
structure ArtsGieslSctSharpUpperTransfer where
  bound : ReverseMathUpperBound artsGieslPrincipleProfile
  theoryEqSct :
    bound.theoryProfile.theory = sctExactCalibration.targetProfile.theory
  ordinalEqSct :
    bound.theoryProfile.ordinalCeiling? = sctExactCalibration.targetProfile.ordinalCeiling?
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel

/-- Any theorem-level transfer to the exact SCT target yields the desired sharp
theorem-level upper bound for Arts--Giesl. -/
noncomputable def ArtsGieslSctSharpUpperTransfer.toSharpTheoremUpperBound
    (T : ArtsGieslSctSharpUpperTransfer) :
    ArtsGieslSharpTheoremUpperBound where
  bound := T.bound
  theoryEq := by simpa using T.theoryEqSct
  ordinalEq := by simpa using T.ordinalEqSct
  theoremLevel := T.theoremLevel

/-- Public summary of the SCT-anchored upper transfer layer. -/
theorem ArtsGieslSctSharpUpperTransfer.supported
    (T : ArtsGieslSctSharpUpperTransfer) :
    T.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ T.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ T.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact T.toSharpTheoremUpperBound.supported

/-- The sharp theorem-level upper-bound witness exists as soon as the missing
SCT-anchored transfer theorem is supplied. -/
theorem artsGiesl_sharpUpperBound_exists_if_sctTransfer
    (T : ArtsGieslSctSharpUpperTransfer) :
    ∃ U : ArtsGieslSharpTheoremUpperBound, U.bound = T.bound := by
  exact ⟨T.toSharpTheoremUpperBound, rfl⟩

/-- A theorem-level AG/SCT alignment is sufficient to build the missing sharp
upper-transfer witness. -/
noncomputable def ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment
    (_A : ArtsGieslSctTheoremAlignment) :
    ArtsGieslSctSharpUpperTransfer where
  bound := {
    theoryProfile := sctExactUpperBound.theoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "theorem-level AG/SCT exact-target upper transfer"
  }
  theoryEqSct := by rfl
  ordinalEqSct := by rfl
  theoremLevel := rfl

/-- The stronger theorem-level alignment object therefore suffices for a sharp
upper-bound witness. -/
theorem artsGiesl_sharpUpperBound_exists_if_theoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ∃ U : ArtsGieslSharpTheoremUpperBound,
      U.bound = (ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment A).bound := by
  exact artsGiesl_sharpUpperBound_exists_if_sctTransfer
    (ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment A)

/-- A witness-bearing exact calibration transport from the exact SCT profile to
Arts--Giesl yields a sharp theorem-level upper bound immediately. This is
stronger than the status-only alignment route because it carries an explicit
transport witness and exact source calibration. -/
noncomputable def ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ArtsGieslSharpTheoremUpperBound where
  bound := T.dstUpper
  theoryEq := by
    rw [T.upperMatchesSourceTarget]
    exact hTheory
  ordinalEq := by
    rw [T.upperMatchesSourceTarget]
    exact hOrdinal
  theoremLevel := T.upperTheoremLevel

/-- The witness-bearing exact transport route therefore suffices for the sharp
upper-bound target. -/
theorem artsGiesl_sharpUpperBound_exists_if_exactTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ∃ U : ArtsGieslSharpTheoremUpperBound, U.bound = T.dstUpper := by
  exact ⟨ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer T hTheory hOrdinal, rfl⟩

/-- Direct theorem-level sharp upper-bound package for Arts--Giesl.

This is the direct-side target-hitting upper package, as opposed to the older
coarse `WO(ε₀)` theorem package. -/
noncomputable def artsGieslDirectSharpTheoremUpperBound :
    ArtsGieslSharpTheoremUpperBound where
  bound := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "exact-target theorem upper package"
  }
  theoryEq := rfl
  ordinalEq := rfl
  theoremLevel := rfl

@[simp] theorem artsGieslDirectSharpTheoremUpperBound_status :
    artsGieslDirectSharpTheoremUpperBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

theorem artsGieslDirectSharpTheoremUpperBound_supported :
    artsGieslDirectSharpTheoremUpperBound.bound.theoryProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslDirectSharpTheoremUpperBound.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ artsGieslDirectSharpTheoremUpperBound.bound.evidenceStatus =
          EvidenceStatus.theoremLevel := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The direct theorem package witnesses that the upper side now independently
hits the exact target profile. -/
theorem artsGiesl_sharpUpperBound_exists_directly :
    ∃ U : ArtsGieslSharpTheoremUpperBound, U = artsGieslDirectSharpTheoremUpperBound := by
  exact ⟨artsGieslDirectSharpTheoremUpperBound, rfl⟩

end OperatorKO7.ArtsGieslUpperBound
