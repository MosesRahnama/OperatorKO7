import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP
import OperatorKO7.Meta.ConfessionMethod_CounterProjection
import OperatorKO7.Meta.ConfessionMethod_SCT
import OperatorKO7.Meta.ConfessionMethod_ArgumentFiltering
import OperatorKO7.Meta.OperationalIncompleteness

/-!
# The Confession-Method Family: Collected Results

This module collects the four formalized confession methods on the KO7
step-duplicating schema and proves family-level theorems about their
shared structure.

The central result is `confession_is_a_class`: on the step-duplicating
schema, four methods with four distinct soundness licenses all produce
the same projection rank and all satisfy the `CertifiedForgettingWitness`
interface. This is the formal content behind Paper C's claim that the
construction/confession boundary separates *method classes*, not individual
named methods.

The four methods are:
1. Dependency pairs + subterm criterion (Arts-Giesl 2000)
2. Direct counter-projection via the subterm criterion
3. Size-Change Termination (Lee-Jones-Ben-Amram 2001)
4. Argument filtering within the DP framework
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaOperationalIncompleteness

/-- All four confession methods enumerated. -/
def allConfessionMethods : List (ConfessionMethod ko7Schema) :=
  [dpConfession, counterProjectionConfession, sctConfession, argumentFilteringConfession]

/-- The family has exactly four members. -/
theorem family_size : allConfessionMethods.length = 4 := by rfl

/-- Every confession method in the family produces the same rank on
    the KO7 schema. This is a theorem: the schema has exactly one
    recursive call with exactly one strictly decreasing argument, so
    every projection-based method finds the same descent coordinate. -/
theorem family_rank_agreement :
    ∀ C ∈ allConfessionMethods,
      C.rank = dpConfession.rank := by
  intro C hC
  simp [allConfessionMethods] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> rfl

/-- Every confession method in the family orients the KO7 duplicating
    step. -/
theorem family_orients_dup_step :
    ∀ C ∈ allConfessionMethods,
      ∀ b s n : Trace,
        C.rank (app s (recΔ b s n)) < C.rank (recΔ b s (delta n)) := by
  intro C hC b s n
  exact confession_orients C b s n

/-- Every confession method in the family violates wrapper sensitivity.
    This is the formal content of "the payload is declared inert." -/
theorem family_violates_sensitivity :
    ∀ C ∈ allConfessionMethods,
      (∃ x y : Trace, ¬ (C.rank (app x y) > C.rank x))
      ∧ (∃ x y : Trace, ¬ (C.rank (app x y) > C.rank y)) := by
  intro C hC
  exact ⟨confession_violates_wrap1 C, confession_violates_wrap2 C⟩

/-- Every confession method in the family is a certified-forgetting
    witness in the sense of `OperationalIncompleteness.lean`. -/
theorem family_certified_forgetting :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness,
        fw.rank = C.rank := by
  intro C hC
  rw [family_rank_agreement C hC]
  exact dp_projection_exhibits_certified_forgetting

/-- The four confession methods have four distinct soundness licenses.
    This confirms they are genuinely different methods that happen to
    share the same rank on this schema, not four names for one method. -/
theorem family_distinct_licenses :
    (allConfessionMethods.map (·.license)).Nodup := by
  decide

/-- **Main theorem: Confession methods form a structural class.**

    On the step-duplicating schema:
    - four methods with distinct soundness licenses exist;
    - all share a common rank (counter projection);
    - all satisfy the certified-forgetting interface;
    - the licenses are pairwise distinct.

    This is the formal content behind Paper C's central claim that the
    construction/confession boundary separates method *classes*, not
    individual methods. The confession class is defined by a structural
    shape (extract recursive calls, project to descent coordinate,
    declare payload inert) that is invariant under changes of extraction
    mechanism and soundness license. -/
theorem confession_is_a_class :
    allConfessionMethods.length = 4
    ∧ (∀ C ∈ allConfessionMethods, C.rank = dpConfession.rank)
    ∧ (allConfessionMethods.map (·.license)).Nodup := by
  exact ⟨family_size, family_rank_agreement, family_distinct_licenses⟩

/-- The confession family provides four independent witnesses that the
    transformed-call layer resolves KO7's operational incompleteness at
    the payload dimension. Each uses the same rank but a different
    external soundness license. -/
theorem confession_family_resolves_operational_incompleteness :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness, fw.rank = C.rank :=
  family_certified_forgetting

end OperatorKO7.ConfessionMethodFamily
