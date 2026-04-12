import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.DependencyPairs_TPDBExtraction
import OperatorKO7.Meta.DependencyPairs_FirstOrderExtraction
import OperatorKO7.Meta.DependencyPairs_KernelFirstOrder
import OperatorKO7.Meta.TPDB_Export

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

/-- The exported KO7 TPDB problem text matches the checked artifact text
exactly. This is the first half of the external bridge: the Lean exporter and
the file submitted to TTT2 / CeTA are the same concrete problem. -/
theorem ko7FastReplay_export_text_matches_artifact :
    OperatorKO7.ko7_full_step_tpdb = OperatorKO7.ko7_full_step_tpdb_artifact_text :=
  OperatorKO7.ko7_full_step_tpdb_matches_artifact_text

/-- The concrete TPDB extraction surface for the exported KO7 problem already
exhibits the same single recursive self-call head that the replay packages as
the internal dependency-pair problem. -/
theorem ko7FastReplay_export_has_recD_successor :
    ∃ n ∈ OperatorKO7.DependencyPairsFragment.ko7FullStepExtractedNodes.toList,
      n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String) := by
  exact OperatorKO7.DependencyPairsFragment.ko7_full_step_has_recD_successor

/-- Export-side correspondence bundle: the exact exported TPDB text matches the
checked artifact, the extracted TPDB call-graph surface contains the unique
recursive `recD -> recD` successor pattern, and the replay packages that same
pattern as the internal KO7 dependency-pair problem. -/
theorem ko7FastReplay_matches_export_surface :
    OperatorKO7.ko7_full_step_tpdb = OperatorKO7.ko7_full_step_tpdb_artifact_text ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.ko7FullStepExtractedNodes.toList,
        n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String)) ∧
      ko7FastReplay.projectionProblem.Pair = DPPair := by
  exact ⟨ko7FastReplay_export_text_matches_artifact,
    ko7FastReplay_export_has_recD_successor,
    ko7FastReplay_uses_recSucc_pair⟩

/-- Stronger correspondence bundle across the three extraction surfaces already
present in the formal artifact:

* the concrete TPDB-side extraction surface;
* the generic first-order string-symbol surface;
* the internal kernel-symbol first-order surface.

Each surface exhibits the same single recursive `recD -> recD` head pattern,
and the replay packages that pattern as the internal KO7 dependency-pair
problem. -/
theorem ko7FastReplay_matches_all_extraction_surfaces :
    OperatorKO7.ko7_full_step_tpdb = OperatorKO7.ko7_full_step_tpdb_artifact_text ∧
      OperatorKO7.DependencyPairsFragment.tpdbDefinedHeads
        OperatorKO7.ko7FullStepTpdbRules.toArray =
        ({ "integrate", "merge", "recD", "eqW" } : Finset String) ∧
      OperatorKO7.DependencyPairsFragment.foDefinedHeads
        OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7FullStepFORules =
        ({ "integrate", "merge", "recD", "eqW" } : Finset String) ∧
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.definedHeads =
        ({ OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.integrate,
           OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.merge,
           OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD,
           OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.eqW } :
          Finset OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol) ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.ko7FullStepExtractedNodes.toList,
        n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String)) ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7FullStepExtractedNodes.toList,
        n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String)) ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7FullStepExtractedNodes.toList,
        n.nodeKey = OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD ∧
          n.succKeys =
            ({ OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD } :
              Finset OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol)) ∧
      ko7FastReplay.projectionProblem.Pair = DPPair := by
  refine ⟨ko7FastReplay_export_text_matches_artifact, ?_, ?_, ?_, ?_, ?_, ?_, ko7FastReplay_uses_recSucc_pair⟩
  · exact OperatorKO7.DependencyPairsFragment.ko7_full_step_defined_heads
  · exact OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7_full_step_defined_heads
  · exact OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7_full_step_defined_heads
  · exact ko7FastReplay_export_has_recD_successor
  · exact OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7_full_step_has_recD_successor
  · exact OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7_full_step_has_recD_successor

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
