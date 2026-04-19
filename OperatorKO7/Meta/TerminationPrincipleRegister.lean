import OperatorKO7.Meta.ReverseMathFramework

/-!
# Termination-Principle Register

Registry layer sitting on top of `ReverseMathFramework`.

This file records the named termination principles and soundness principles
used by the paper stack, together with their currently available calibration
profiles. The goal is to make comparisons explicit and machine-visible without
pretending that every calibration is already theorem-level exact.
-/

namespace OperatorKO7.TerminationPrincipleRegister

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework

/-- Named termination / soundness principles tracked by the paper stack. -/
inductive TerminationPrinciple
  | sizeChangeTermination
  | dependencyPairSoundness
  | artsGieslSoundness
  | importedWellFoundedOrder
  deriving DecidableEq, Repr

/-- Public registry entry for one principle. -/
structure TerminationPrincipleEntry where
  principle : TerminationPrinciple
  profile : PrincipleProfile
  calibrationStatus : CalibrationStatus
  targetTheory? : Option FormalTheory := none
  targetOrdinal? : Option Ordinal := none

/-- Registry entry for SCT. -/
noncomputable def sctEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.sizeChangeTermination
  profile := sctPrincipleProfile
  calibrationStatus := CalibrationStatus.exact
  targetTheory? := some FormalTheory.RCA0_WO_omega3
  targetOrdinal? := some omegaPowThree

/-- Registry entry for Arts--Giesl soundness. -/
noncomputable def artsGieslEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.artsGieslSoundness
  profile := artsGieslPrincipleProfile
  calibrationStatus := CalibrationStatus.conjectural
  targetTheory? := some FormalTheory.RCA0_WO_omega3
  targetOrdinal? := some omegaPowThree

/-- Registry entry for the general dependency-pair soundness route. The
artifact currently tracks its proof-theoretic family and formula class, but not
an exact reverse-mathematical target distinct from the Arts--Giesl license.
-/
def dependencyPairEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.dependencyPairSoundness
  profile := artsGieslPrincipleProfile
  calibrationStatus := CalibrationStatus.boundedUpper

/-- Registry entry for imported well-founded order soundness routes. -/
def importedWellFoundedOrderEntry : TerminationPrincipleEntry where
  principle := TerminationPrinciple.importedWellFoundedOrder
  profile := {
    label := "Imported well-founded order"
  }
  calibrationStatus := CalibrationStatus.boundedUpper

/-- Alignment object between two registered principles. -/
structure PrincipleAlignment
    (left right : TerminationPrincipleEntry) where
  sharedTheoryTarget? : Option FormalTheory := none
  sharedOrdinalTarget? : Option Ordinal := none
  evidenceStatus : EvidenceStatus

/-- Current AG/SCT alignment used in the paper's reverse-mathematical
discussion: exact on the SCT side, conjectural on the AG side, with a shared
candidate target. -/
noncomputable def artsGieslSctAlignment :
    PrincipleAlignment artsGieslEntry sctEntry where
  sharedTheoryTarget? := some FormalTheory.RCA0_WO_omega3
  sharedOrdinalTarget? := some omegaPowThree
  evidenceStatus := EvidenceStatus.profileLevel

@[simp] theorem sctEntry_status :
    sctEntry.calibrationStatus = CalibrationStatus.exact := by
  simp [sctEntry]

@[simp] theorem artsGieslEntry_status :
    artsGieslEntry.calibrationStatus = CalibrationStatus.conjectural := by
  simp [artsGieslEntry]

@[simp] theorem artsGieslEntry_family :
    artsGieslEntry.profile.family? = some AscentFamily.reflection := by
  simp [artsGieslEntry, artsGieslPrincipleProfile, artsGieslLicenseProfile]

@[simp] theorem artsGieslEntry_complexity :
    artsGieslEntry.profile.complexity? = some FormulaClass.pi02 := by
  simp [artsGieslEntry, artsGieslPrincipleProfile, artsGieslLicenseProfile]

/-- The registry-level AG/SCT alignment shares the same candidate target
theory. -/
theorem artsGiesl_and_sct_share_registry_target_theory :
    artsGieslEntry.targetTheory? = sctEntry.targetTheory? := by
  simp [artsGieslEntry, sctEntry]

/-- The registry-level AG/SCT alignment shares the same candidate target
ordinal. -/
theorem artsGiesl_and_sct_share_registry_target_ordinal :
    artsGieslEntry.targetOrdinal? = sctEntry.targetOrdinal? := by
  rfl

/-- The alignment object agrees with the two concrete registry entries. -/
theorem artsGieslSctAlignment_sound :
    artsGieslSctAlignment.sharedTheoryTarget? = artsGieslEntry.targetTheory?
      ∧ artsGieslSctAlignment.sharedTheoryTarget? = sctEntry.targetTheory?
      ∧ artsGieslSctAlignment.sharedOrdinalTarget? = artsGieslEntry.targetOrdinal?
      ∧ artsGieslSctAlignment.sharedOrdinalTarget? = sctEntry.targetOrdinal? := by
  constructor
  · simp [artsGieslSctAlignment, artsGieslEntry]
  constructor
  · simp [artsGieslSctAlignment, sctEntry]
  constructor <;> rfl

end OperatorKO7.TerminationPrincipleRegister
