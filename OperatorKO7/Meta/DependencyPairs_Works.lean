import OperatorKO7.Kernel
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import Mathlib.Order.WellFounded

/-!
# Dependency Pairs Work on the KO7 Duplicating Recursor

This module gives a minimal formal witness that the KO7 duplicating recursor is
handled by a dependency-pair style argument:

- Extract the single recursive-call dependency pair from `rec_succ`.
- Use the DP projection rank (track only the recursion counter argument).
- Prove strict decrease on every DP step.
- Conclude well-foundedness of the reverse DP relation via `Nat.lt`.

This is intentionally narrow: it formalizes the DP-chain termination core for
the duplicating rule, not a full generic DP framework library.
-/

namespace OperatorKO7.MetaDependencyPairs

open OperatorKO7 Trace
open OperatorKO7.CompositionalImpossibility

/-- The dependency pair relation extracted from `rec_succ`:
`recΔ b s (delta n) ↦ recΔ b s n`. -/
inductive DPPair : Trace → Trace → Prop
| rec_succ : ∀ b s n, DPPair (recΔ b s (delta n)) (recΔ b s n)

/-- DP rank used for the pair problem:
reuse the projection that keeps only recursion-counter depth. -/
@[simp] def dpRank : Trace → Nat := dpProjection

/-- Each dependency-pair step strictly decreases the DP rank. -/
theorem dpPair_decreases : ∀ {a b : Trace}, DPPair a b → dpRank b < dpRank a
  | _, _, DPPair.rec_succ b s n => by
      simp [dpRank, dpProjection]

/-- Reverse dependency-pair relation (the standard SN orientation). -/
def DPPairRev : Trace → Trace → Prop := fun a b => DPPair b a

/-- Reverse DP relation is a subrelation of `<` on the DP rank. -/
lemma dpPairRev_sub_rank :
    Subrelation DPPairRev (fun x y => dpRank x < dpRank y) := by
  intro a b h
  exact dpPair_decreases h

/-- Well-foundedness of reverse dependency pairs:
no infinite KO7 DP chain is possible for the extracted pair problem. -/
theorem wf_DPPairRev : WellFounded DPPairRev := by
  have hrank : WellFounded (fun x y : Trace => dpRank x < dpRank y) :=
    InvImage.wf (f := dpRank) Nat.lt_wfRel.wf
  exact Subrelation.wf dpPairRev_sub_rank hrank

/-- The extracted pair comes directly from the `rec_succ` rule instance. -/
theorem rec_succ_extracts_dependency_pair (b s n : Trace) :
    Step (recΔ b s (delta n)) (app s (recΔ b s n))
    ∧ DPPair (recΔ b s (delta n)) (recΔ b s n) := by
  exact ⟨Step.R_rec_succ b s n, DPPair.rec_succ b s n⟩

end OperatorKO7.MetaDependencyPairs
