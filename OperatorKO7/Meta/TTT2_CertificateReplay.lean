import OperatorKO7.Meta.DependencyPairs_Works

/-!
# Narrow Lean-side replay of the FAST TTT2 certificate core

This file does not parse CPF. It replays the mathematically substantive core of
the external FAST certificate inside Lean:

- the extracted recursive dependency pair,
- the singleton real SCC,
- the subterm projection on the recursion-counter argument.

That is exactly the fragment reported by `Artifacts/ttt2/KO7_FAST.cpf` and
`KO7_full_step_TTT2_results_FAST.txt`.
-/

open OperatorKO7 Trace

namespace OperatorKO7.TTT2CertificateReplay

open OperatorKO7.DependencyPairsFragment
open OperatorKO7.MetaDependencyPairs

/-- Minimal replay object for the FAST certificate fragment. -/
structure FastDPReplay where
  projectionIndexTool : Nat
  projectionIndexPaper : Nat
  pairCount : Nat
  singletonRealSccCount : Nat
  projectionProblem : DPProjection Trace

/-- Lean-side replay of the mathematical core of the FAST certificate. -/
def ko7FastReplay : FastDPReplay where
  projectionIndexTool := 2
  projectionIndexPaper := 3
  pairCount := 1
  singletonRealSccCount := 1
  projectionProblem := ko7ProjectionProblem

theorem ko7FastReplay_indices :
    ko7FastReplay.projectionIndexTool + 1 = ko7FastReplay.projectionIndexPaper := by
  decide

theorem ko7FastReplay_pairCount :
    ko7FastReplay.pairCount = 1 := rfl

theorem ko7FastReplay_singletonRealScc :
    ko7FastReplay.singletonRealSccCount = 1 := rfl

/-- The Lean replay uses the same extracted recursive pair as the external FAST proof. -/
theorem ko7FastReplay_uses_recSucc_pair :
    ko7FastReplay.projectionProblem.Pair = DPPair := rfl

/-- The Lean replay uses the same projection-rank drop as the external FAST proof. -/
theorem ko7FastReplay_subterm_drop :
    ∀ {a b : Trace}, ko7FastReplay.projectionProblem.Pair a b →
      ko7FastReplay.projectionProblem.rank b < ko7FastReplay.projectionProblem.rank a := by
  intro a b h
  exact ko7FastReplay.projectionProblem.decreases h

/-- Narrow internal replay soundness: the FAST certificate core certifies the reverse
dependency-pair relation as well-founded inside Lean. -/
theorem ko7FastReplay_sound :
    WellFounded ko7FastReplay.projectionProblem.Rev := by
  simpa [ko7FastReplay] using ko7ProjectionProblem.wfRev

/-- The replayed FAST certificate core proves the extracted KO7 pair problem
terminating inside Lean. -/
theorem wf_DPPairRev_replayed : WellFounded DPPairRev := by
  simpa [DPPairRev, ko7FastReplay] using ko7FastReplay_sound

end OperatorKO7.TTT2CertificateReplay
