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

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- Dependency pairs + subterm criterion as a confession method on KO7. -/
def dpConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.artsGiesl2000

end OperatorKO7.ConfessionMethodFamily
