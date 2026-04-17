import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Confession Method Instance: Dependency Pairs + Subterm Criterion

The canonical confession method on the KO7 step-duplicating schema.

Dependency pairs extract the recursive-call relation from the rules,
construct the dependency-pair graph, and apply the subterm criterion with
projection π(recΔ♯) = 3 to certify that the counter coordinate strictly
decreases. The wrapper `app(s, ·)` and the duplicated payload `s` are
dropped from the proof obligation. Soundness is licensed by the
Arts–Giesl 2000 theorem.

The underlying `ProjectionRank` is `dpProjectionRank` from
`CompositionalMeasure_Impossibility.lean`, already fully formalized.
This module packages it as a `ConfessionMethod` instance.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- A route-local dependency-pair witness on the marked recursive symbol.
    On KO7, the marked pair still carries the three original recursor
    coordinates, and the third coordinate is the unique descent-bearing one. -/
structure DPWitness where
  selectedCoordinate : Fin 3
  selectedCoordinate_is_counter : selectedCoordinate = ⟨2, by decide⟩

/-- The concrete dependency-pair witness on the KO7 schema. -/
def schemaDPWitness : DPWitness where
  selectedCoordinate := ⟨2, by decide⟩
  selectedCoordinate_is_counter := rfl

/-- The DP witness packaged as the intermediate confession-core witness. -/
def DPWitness.toConfessionCoreWitness (W : DPWitness) : ConfessionCoreWitness ko7Schema where
  rank := dpProjection
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- Dependency pairs + subterm criterion as a confession method on KO7. -/
def dpConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.artsGiesl2000

/-- The DP confession is the canonical confession-core route on KO7. -/
theorem dpConfession_is_canonical :
    dpConfession.toProjectionRank = dpProjectionRank := rfl

/-- The DP witness selects the counter coordinate as the descent-bearing
    argument on the marked recursive pair. -/
theorem dpWitness_selects_counter_coordinate :
    schemaDPWitness.selectedCoordinate = ⟨2, by decide⟩ :=
  schemaDPWitness.selectedCoordinate_is_counter

/-- The DP route realizes the canonical confession core directly. -/
theorem dpWitness_realizes_projection_core :
    dpConfession.rank = dpProjectionRank.rank := rfl

/-- The DP witness induces the canonical intermediate confession core. -/
theorem dpWitness_toConfessionCoreWitness_eq_core :
    schemaDPWitness.toConfessionCoreWitness.toProjectionRank = dpProjectionRank := by
  rfl

end OperatorKO7.ConfessionMethodFamily
