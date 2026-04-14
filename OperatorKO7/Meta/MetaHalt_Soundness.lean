import OperatorKO7.Meta.MetaHalt_Signatures
import OperatorKO7.Meta.MetaHalt_Predicate
import OperatorKO7.Meta.MetaHalt_Regress
import OperatorKO7.Meta.WitnessOrder

/-!
# META-HALT Soundness Asymmetry

This module formalizes the safety-critical observation that only
**catalog-soundness** of the META-HALT predicate is required for safety:
completeness is an efficiency property, not a safety property.

Key identifiers:

- `catalogSound` : decidable predicate on a `metaHalt` instantiation;
- `catalogComplete` : decidable predicate; not required for safety;
- `no_c1_c2_from_blocked_class` : Lemma 5.16 mechanized;
- `below_threshold_only_c3_or_lift` : Proposition 5.14;
- `below_threshold_forces_metahalt` : Proposition 5.33.
-/

namespace OperatorKO7.MetaHalt.Soundness

open OperatorKO7
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaHalt.Signatures
open OperatorKO7.MetaHalt.Predicate
open OperatorKO7.MetaHalt.Regress

/-- Catalog-soundness of a META-HALT predicate instantiation. -/
def catalogSound
    (admiss : AdmissibilityTable) (loops : LoopPatternTable) : Prop :=
  ∀ (O : ObligationSignature) (L : LanguageSignature)
    (T : SearchTraceSignature) (budget catalogRem : Nat),
    metaHalt O L T admiss loops budget catalogRem = none →
    admiss.admits O L = true

/-- Catalog-completeness: every obligation in a pre-declared blocked class
    eventually triggers a META-HALT firing. -/
def catalogComplete
    (admiss : AdmissibilityTable) (loops : LoopPatternTable) : Prop :=
  ∀ (O : ObligationSignature) (L : LanguageSignature)
    (T : SearchTraceSignature) (budget catalogRem : Nat),
    admiss.admits O L = false →
    metaHalt O L T admiss loops budget catalogRem ≠ none

/-- The canonical `metaHalt` predicate is always catalog-sound. -/
theorem metaHalt_is_catalog_sound
    (admiss : AdmissibilityTable) (loops : LoopPatternTable) :
    catalogSound admiss loops := by
  intro O L T budget catalogRem hnone
  cases hAdmits : admiss.admits O L <;> simp [metaHalt, hAdmits] at hnone ⊢

private theorem no_c1_c2_from_blocked_class_aux
    (fuel : Nat)
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (L : LanguageSignature)
    (hblock : admiss.admits O L = false) :
    ∀ (s : SupervisoryLoopState) (auditSoFar : List LanguageAuditEntry) (out : TypedOutput),
      supervisoryLoop fuel C policy admiss loops inner O s auditSoFar ≠
        .acceptedWitness L out := by
  induction fuel with
  | zero =>
      intro s auditSoFar out hEq
      simp [supervisoryLoop] at hEq
  | succ fuel ih =>
      intro s auditSoFar out hEq
      simp [supervisoryLoop] at hEq
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [hchoose] at hEq
      | some current =>
          cases hentry : Catalog.entryOf C current with
          | none =>
              simp [hchoose, hentry] at hEq
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              cases hpre : metaHalt O current preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  have hEq' :
                      supervisoryLoop fuel C policy admiss loops inner O
                        (s.mark_visited current)
                        ({ language := current
                           firedClause := clause
                           allocatedBudget := entry.budget
                           stepsConsumed := preTrace.stepsConsumed
                           candidateCount := preTrace.candidateCount
                           partialTraceTags := preTrace.traceTags
                           loopPatternHit := loops.patterns.find? (fun p => p.fires preTrace) } ::
                          auditSoFar) =
                        .acceptedWitness L out := by
                    simpa [hchoose, hentry, catalogRem, preTrace, hpre] using hEq
                  exact ih (s.mark_visited current) _ _ hEq'
              | none =>
                  cases hinner : inner current SearchTraceSignature.empty entry.budget with
                  | inr pair =>
                      rcases pair with ⟨_returnedLanguage, acceptedOut⟩
                      have hEq' :
                          SupervisoryLoopOutcome.acceptedWitness current acceptedOut =
                            SupervisoryLoopOutcome.acceptedWitness L out := by
                        simpa [hchoose, hentry, catalogRem, preTrace, hpre, hinner] using hEq
                      cases hEq'
                      simp [metaHalt, hblock] at hpre
                  | inl trace' =>
                      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          have hEq' :
                              supervisoryLoop fuel C policy admiss loops inner O
                                (s.mark_visited current)
                                ({ language := current
                                   firedClause := clause
                                   allocatedBudget := entry.budget
                                   stepsConsumed := trace'.stepsConsumed
                                   candidateCount := trace'.candidateCount
                                   partialTraceTags := trace'.traceTags
                                   loopPatternHit := loops.patterns.find? (fun p => p.fires trace') } ::
                                  auditSoFar) =
                                .acceptedWitness L out := by
                            simpa [hchoose, hentry, catalogRem, preTrace, hpre, hinner, hpost] using hEq
                          exact ih (s.mark_visited current) _ _ hEq'
                      | none =>
                          have hEq' :
                              supervisoryLoop fuel C policy admiss loops inner O
                                (s.mark_visited current)
                                ({ language := current
                                   firedClause := MetaHaltClause.budgetExhausted
                                   allocatedBudget := entry.budget
                                   stepsConsumed := trace'.stepsConsumed
                                   candidateCount := trace'.candidateCount
                                   partialTraceTags := trace'.traceTags
                                   loopPatternHit := none } ::
                                  auditSoFar) =
                                .acceptedWitness L out := by
                            simpa [hchoose, hentry, catalogRem, preTrace, hpre, hinner, hpost] using hEq
                          exact ih (s.mark_visited current) _ _ hEq'

/-- Lemma 5.16: no blocked witness class can terminate the supervisory loop
    with an accepted T1/T2-style verdict attributed to that class. -/
theorem no_c1_c2_from_blocked_class
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (L : LanguageSignature)
    (hblock : admiss.admits O L = false) :
    ∀ out,
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] ≠
        .acceptedWitness L out := by
  intro out
  exact no_c1_c2_from_blocked_class_aux (C.size + 1) C policy admiss loops inner O L hblock s [] out

/-- Proposition 5.14: below-threshold confinement licenses only a lift or a
    typed C3 report. Any accepted output below threshold is therefore a
    typed-output-discipline violation in the fully unlicensed context. -/
theorem below_threshold_only_c3_or_lift
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (threshold : WLevel)
    (_hconf : ∀ L ∈ s.visited, L.level.toNat < threshold.toNat)
    (_hnoThresh : ¬ ∃ L ∈ s.visited, threshold.toNat ≤ L.level.toNat) :
    ∀ out L,
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] =
        .acceptedWitness L out →
      (L.level.toNat ≥ threshold.toNat) ∨
      isTypedOutputDisciplineViolation out false false false false false = true := by
  intro out L _hacc
  rcases Nat.lt_or_ge L.level.toNat threshold.toNat with hlt | hge
  · right
    cases out <;> simp [isTypedOutputDisciplineViolation]
  · exact Or.inl hge

/-- Proposition 5.33: for sound outputs, confinement below threshold forces a
    META-HALT-style outcome rather than a below-threshold accepted witness. -/
theorem below_threshold_forces_metahalt
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (threshold : WLevel) (_hth : 0 < threshold.toNat)
    (hconf : ∀ L ∈ s.visited, L.level.toNat < threshold.toNat)
    (hsound : ∀ (L : LanguageSignature) (o : TypedOutput),
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] =
        .acceptedWitness L o →
      isTypedOutputDisciplineViolation o false false false false false = false) :
    let out := supervisoryLoop (C.size + 1) C policy admiss loops inner O s []
    (∃ rec : AuditCompleteC3Record, out = .auditC3 rec) ∨
    (∃ L o, out = .acceptedWitness L o ∧ L.level.toNat ≥ threshold.toNat) := by
  dsimp
  have hterm := supervisoryLoop_emits_c3_or_c1c2 C policy admiss loops inner O s
  rcases hterm with hacc | haudit
  · rcases hacc with ⟨L, o, hacc⟩
    have hnoThresh : ¬ ∃ L' ∈ s.visited, threshold.toNat ≤ L'.level.toNat := by
      intro hExists
      rcases hExists with ⟨L', hMem, hGe⟩
      exact Nat.not_le_of_lt (hconf L' hMem) hGe
    have hsplit :=
      below_threshold_only_c3_or_lift C policy admiss loops inner O s threshold hconf hnoThresh o L hacc
    rcases hsplit with hGe | hViolation
    · exact Or.inr ⟨L, o, hacc, hGe⟩
    · have hSafe := hsound L o hacc
      rw [hSafe] at hViolation
      contradiction
  · rcases haudit with ⟨rec, haudit⟩
    exact Or.inl ⟨rec, haudit⟩

/-- Catalog-soundness is enough to forbid accepted outputs from classes the
    admissibility contract already marks as blocked. -/
theorem catalogSound_suffices_for_safety
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (_hsound : catalogSound admiss loops) :
    ∀ (C : Catalog) (policy : CatalogLiftPolicy) (inner : InnerSearchStep)
      (O : ObligationSignature) (s : SupervisoryLoopState)
      (L : LanguageSignature) (out : TypedOutput),
      admiss.admits O L = false →
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] ≠
        .acceptedWitness L out := by
  intro C policy inner O s L out hblock
  exact no_c1_c2_from_blocked_class C policy admiss loops inner O s L hblock out

end OperatorKO7.MetaHalt.Soundness
