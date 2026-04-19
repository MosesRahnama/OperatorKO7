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

end OperatorKO7.ArtsGieslUpperBound
