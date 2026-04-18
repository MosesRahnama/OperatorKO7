import OperatorKO7.Meta.MetaHalt_Signatures
import OperatorKO7.Meta.MetaHalt_Predicate
import OperatorKO7.Meta.GenericSupervisoryEngine
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count

/-!
# META-HALT Regress Termination

This module defines the supervisory loop and proves its termination under
a finite catalog with per-language budgets. The key theorem
`supervisoryLoop_terminates_in_catalog_budget` is the mechanization of
Proposition 5.6.

The design splits the supervisory loop into:

- a per-language inner loop bounded by the per-language budget;
- an outer loop bounded by the catalog size, with a visited-set invariant
  that strictly grows on every META-HALT firing.

Both loops are fuel-indexed, so termination is evident from the recursive
structure. The explicit step bound is reconstructed via a sum-of-budgets
lemma.

Key identifiers:

- `CatalogLiftPolicy` : scheduling map from visited set to next candidate;
- `SupervisoryLoopState` : record of visited languages, current search
  trace, and per-language budgets;
- `supervisoryLoop` : fuel-indexed recursive function;
- `SupervisoryLoopOutcome` : sum type of terminal outcomes;
- `AuditCompleteC3Record` : the C3 report of Definition 5.8;
- `supervisoryLoop_terminates_in_catalog_budget` : the central theorem.
-/

namespace OperatorKO7.MetaHalt.Regress

open OperatorKO7
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaHalt.Signatures
open OperatorKO7.MetaHalt.Predicate

/-- Per-language audit entry. -/
structure LanguageAuditEntry where
  language : LanguageSignature
  firedClause : MetaHaltClause
  allocatedBudget : Nat
  stepsConsumed : Nat
  candidateCount : Nat
  partialTraceTags : List TraceTag
  loopPatternHit : Option LoopPattern
  deriving Repr

/-- Definition 5.8: audit-complete C3 record. -/
structure AuditCompleteC3Record where
  auditEntries : List LanguageAuditEntry
  checkerLog : List String
  deriving Repr

/-- Terminal outcome of the supervisory loop. -/
inductive SupervisoryLoopOutcome
  | acceptedWitness (L : LanguageSignature) (out : TypedOutput)
  | auditC3 (record : AuditCompleteC3Record)
  deriving Repr

/-- Current state of the supervisory loop. -/
structure SupervisoryLoopState where
  visited : List LanguageSignature
  trace : SearchTraceSignature
  currLang : Option LanguageSignature
  usedSteps : Nat
  deriving Repr

/-- Mark a language as visited and reset the current-trace state. -/
def SupervisoryLoopState.mark_visited
    (s : SupervisoryLoopState) (L : LanguageSignature) : SupervisoryLoopState :=
  { s with
    visited := L :: s.visited
    currLang := none
    trace := SearchTraceSignature.empty }

/-- Set the current language and reset the object-level trace. -/
def SupervisoryLoopState.set_current
    (s : SupervisoryLoopState) (L : LanguageSignature) : SupervisoryLoopState :=
  { s with
    currLang := some L
    trace := SearchTraceSignature.empty }

/-- Definition 5.5: a lift policy maps the currently visited catalog subset
    to the next candidate language. -/
structure CatalogLiftPolicy where
  choose : Catalog → List LanguageSignature → Option LanguageSignature
  never_revisits :
    ∀ (C : Catalog) (visited : List LanguageSignature) (L : LanguageSignature),
      choose C visited = some L → L ∉ visited

/-- Inner per-language loop (abstracted away). -/
def InnerSearchStep :=
  (L : LanguageSignature) →
  (T : SearchTraceSignature) →
  (budget : Nat) →
  SearchTraceSignature ⊕ (LanguageSignature × TypedOutput)

/-- The supervisory loop, fuel-indexed by the remaining catalog budget. -/
def supervisoryLoop
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) : SupervisoryLoopOutcome :=
  match fuel with
  | 0 =>
      .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
  | fuel + 1 =>
      match policy.choose C s.visited with
      | none =>
          .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
      | some L =>
          match C.entryOf L with
          | none =>
              .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              match metaHalt O L preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  let audit : LanguageAuditEntry :=
                    { language := L
                      firedClause := clause
                      allocatedBudget := entry.budget
                      stepsConsumed := preTrace.stepsConsumed
                      candidateCount := preTrace.candidateCount
                      partialTraceTags := preTrace.traceTags
                      loopPatternHit := loops.patterns.find? (fun p => p.fires preTrace) }
                  supervisoryLoop fuel C policy admiss loops inner O
                    (s.mark_visited L) (audit :: auditSoFar)
              | none =>
                  match inner L SearchTraceSignature.empty entry.budget with
                  | .inr (_Lacc, out) =>
                      .acceptedWitness L out
                  | .inl trace' =>
                      match metaHalt O L trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := clause
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := loops.patterns.find? (fun p => p.fires trace') }
                          supervisoryLoop fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
                      | none =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := MetaHaltClause.budgetExhausted
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := none }
                          supervisoryLoop fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
termination_by fuel

/-- Number of still-unvisited catalog entries. -/
def Catalog.remainingCount (C : Catalog) (visited : List LanguageSignature) : Nat :=
  C.entries.countP (fun e => e.language ∉ visited)

/-- A companion execution function that returns both the supervisory outcome
    and the number of catalog-level steps actually traversed along that run. -/
def supervisoryLoopWithSteps
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) : Nat × SupervisoryLoopOutcome :=
  match fuel with
  | 0 =>
      (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
  | fuel + 1 =>
      match policy.choose C s.visited with
      | none =>
          (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
      | some L =>
          match C.entryOf L with
          | none =>
              (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              match metaHalt O L preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  let audit : LanguageAuditEntry :=
                    { language := L
                      firedClause := clause
                      allocatedBudget := entry.budget
                      stepsConsumed := preTrace.stepsConsumed
                      candidateCount := preTrace.candidateCount
                      partialTraceTags := preTrace.traceTags
                      loopPatternHit := loops.patterns.find? (fun p => p.fires preTrace) }
                  let recResult := supervisoryLoopWithSteps fuel C policy admiss loops inner O
                    (s.mark_visited L) (audit :: auditSoFar)
                  (recResult.1 + 1, recResult.2)
              | none =>
                  match inner L SearchTraceSignature.empty entry.budget with
                  | .inr (_Lacc, out) =>
                      (1, .acceptedWitness L out)
                  | .inl trace' =>
                      match metaHalt O L trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := clause
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := loops.patterns.find? (fun p => p.fires trace') }
                          let recResult := supervisoryLoopWithSteps fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
                          (recResult.1 + 1, recResult.2)
                      | none =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := MetaHaltClause.budgetExhausted
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := none }
                          let recResult := supervisoryLoopWithSteps fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
                          (recResult.1 + 1, recResult.2)
termination_by fuel

@[simp] theorem supervisoryLoopWithSteps_snd
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    (supervisoryLoopWithSteps fuel C policy admiss loops inner O s auditSoFar).2 =
      supervisoryLoop fuel C policy admiss loops inner O s auditSoFar := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [supervisoryLoopWithSteps, supervisoryLoop]
  | succ fuel ih =>
      simp [supervisoryLoopWithSteps, supervisoryLoop]
      cases hchoose : policy.choose C s.visited <;>
        simp [hchoose, ih]
      rename_i current
      cases hentry : C.entryOf current <;>
        simp [hchoose, hentry, ih]
      rename_i entry
      let catalogRem := C.size - s.visited.length - 1
      let preTrace := SearchTraceSignature.empty
      cases hpre : metaHalt O current preTrace admiss loops entry.budget catalogRem <;>
        simp [catalogRem, preTrace, hchoose, hentry, hpre, ih]
      cases hinner : inner current SearchTraceSignature.empty entry.budget <;>
        simp [catalogRem, preTrace, hchoose, hentry, hpre, hinner, ih]
      rename_i trace'
      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem <;>
        simp [catalogRem, preTrace, hchoose, hentry, hpre, hinner, hpost, ih]

private theorem remainingCount_cons_le
    (entries : List CatalogEntry)
    (visited : List LanguageSignature)
    (current : LanguageSignature) :
    entries.countP (fun e => e.language ∉ current :: visited) ≤
      entries.countP (fun e => e.language ∉ visited) := by
  induction entries with
  | nil => simp
  | cons x xs ih =>
      by_cases hv : x.language ∉ visited
      · by_cases hx : x.language = current
        · have hstep : xs.countP (fun e => e.language ∉ visited) ≤
            (x :: xs).countP (fun e => e.language ∉ visited) := by
            simpa [hv] using Nat.le_succ (xs.countP (fun e => e.language ∉ visited))
          simpa [hv, hx] using Nat.le_trans ih hstep
        · have hv' : x.language ∉ current :: visited := by
            simp [hx, hv]
          simpa [hv, hv', hx] using Nat.succ_le_succ ih
      · have hv' : ¬ x.language ∉ current :: visited := by
          intro h
          exact hv (fun hmem => h (by simp [hmem]))
        simpa [hv, hv'] using ih

private theorem exists_entry_of_find_eq_some
    (entries : List CatalogEntry)
    (current : LanguageSignature) (entry : CatalogEntry)
    (hentry : entries.find? (fun e => e.language = current) = some entry) :
    ∃ e ∈ entries, e.language = current := by
  induction entries with
  | nil =>
      simp [List.find?] at hentry
  | cons x xs ih =>
      by_cases hx : x.language = current
      · exact ⟨x, by simp, hx⟩
      · simp [List.find?, hx] at hentry
        rcases ih hentry with ⟨e, he, heq⟩
        exact ⟨e, by simp [he], heq⟩

private theorem exists_entry_of_entryOf_eq_some
    (C : Catalog) (current : LanguageSignature) (entry : CatalogEntry)
    (hentry : C.entryOf current = some entry) :
    ∃ e ∈ C.entries, e.language = current := by
  unfold Catalog.entryOf at hentry
  exact exists_entry_of_find_eq_some C.entries current entry hentry

private theorem remainingCount_mark_visited_succ_le_entries
    (entries : List CatalogEntry)
    (visited : List LanguageSignature)
    (current : LanguageSignature)
    (hnotin : current ∉ visited)
    (hex : ∃ e ∈ entries, e.language = current) :
    entries.countP (fun e => e.language ∉ current :: visited) + 1 ≤
      entries.countP (fun e => e.language ∉ visited) := by
  induction entries with
  | nil =>
      rcases hex with ⟨e, he, _⟩
      cases he
  | cons x xs ih =>
      rcases hex with ⟨e, he, heq⟩
      by_cases hx : x.language = current
      · have hmono := remainingCount_cons_le xs visited current
        have hxNot : x.language ∉ visited := by
          simpa [hx] using hnotin
        calc
          (x :: xs).countP (fun e => e.language ∉ current :: visited) + 1
              = xs.countP (fun e => e.language ∉ current :: visited) + 1 := by
                  simp [hx]
          _ ≤ xs.countP (fun e => e.language ∉ visited) + 1 :=
              Nat.add_le_add_right hmono 1
          _ = (x :: xs).countP (fun e => e.language ∉ visited) := by
              symm
              simp [hxNot, Nat.add_comm]
      · have hexs : ∃ e ∈ xs, e.language = current := by
          cases he with
          | head => exact False.elim (hx heq)
          | tail _ hmem => exact ⟨e, hmem, heq⟩
        have hrec := ih hexs
        by_cases hv : x.language ∉ visited
        · have hv' : x.language ∉ current :: visited := by
            simp [hx, hv]
          simpa [hx, hv, hv'] using Nat.succ_le_succ hrec
        · have hv' : ¬ x.language ∉ current :: visited := by
            intro h
            exact hv (fun hmem => h (by simp [hmem]))
          simpa [hx, hv, hv'] using hrec

private theorem remainingCount_mark_visited_succ_le
    (C : Catalog)
    (visited : List LanguageSignature)
    (current : LanguageSignature)
    (entry : CatalogEntry)
    (hentry : C.entryOf current = some entry)
    (hnotin : current ∉ visited) :
    Catalog.remainingCount C (current :: visited) + 1 ≤ Catalog.remainingCount C visited := by
  have hex : ∃ e ∈ C.entries, e.language = current :=
    exists_entry_of_entryOf_eq_some C current entry hentry
  unfold Catalog.remainingCount
  exact remainingCount_mark_visited_succ_le_entries C.entries visited current hnotin hex

/-- Sum of all per-language budgets, with one extra META-HALT check per
    language. -/
def Catalog.totalBudgetPlusOne (C : Catalog) : Nat :=
  C.entries.foldr (fun e acc => acc + (e.budget + 1)) 0

private theorem remainingCount_le_size
    (C : Catalog)
    (visited : List LanguageSignature) :
    Catalog.remainingCount C visited ≤ C.size := by
  unfold Catalog.remainingCount Catalog.size
  exact List.countP_le_length

private theorem size_le_totalBudgetPlusOne
    (C : Catalog) :
    C.size ≤ Catalog.totalBudgetPlusOne C := by
  unfold Catalog.size Catalog.totalBudgetPlusOne
  induction C.entries with
  | nil => simp
  | cons e es ih =>
      have hstep : es.length + 1 ≤ es.foldr (fun e acc => acc + (e.budget + 1)) 0 + 1 :=
        Nat.succ_le_succ ih
      have hone : es.foldr (fun e acc => acc + (e.budget + 1)) 0 + 1 ≤
          es.foldr (fun e acc => acc + (e.budget + 1)) 0 + (e.budget + 1) := by
        exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le e.budget)) _
      exact Nat.le_trans hstep hone

private theorem supervisoryLoopWithSteps_fst_le_remainingCount
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    (supervisoryLoopWithSteps fuel C policy admiss loops inner O s auditSoFar).1 ≤
      Catalog.remainingCount C s.visited := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [supervisoryLoopWithSteps, Catalog.remainingCount]
  | succ fuel ih =>
      simp [supervisoryLoopWithSteps]
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [hchoose, Catalog.remainingCount]
      | some current =>
          cases hentry : C.entryOf current with
          | none =>
              simp [hchoose, hentry, Catalog.remainingCount]
          | some entry =>
              have hnotin : current ∉ s.visited :=
                policy.never_revisits C s.visited current hchoose
              have hdrop : Catalog.remainingCount C (current :: s.visited) + 1 ≤ Catalog.remainingCount C s.visited :=
                remainingCount_mark_visited_succ_le C s.visited current entry hentry hnotin
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              cases hpre : metaHalt O current preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  have hchild := ih (s := s.mark_visited current)
                    (auditSoFar := {
                      language := current
                      firedClause := clause
                      allocatedBudget := entry.budget
                      stepsConsumed := preTrace.stepsConsumed
                      candidateCount := preTrace.candidateCount
                      partialTraceTags := preTrace.traceTags
                      loopPatternHit := loops.patterns.find? (fun p => p.fires preTrace) } :: auditSoFar)
                  simpa [catalogRem, preTrace, hchoose, hentry, hpre] using
                    Nat.le_trans (Nat.succ_le_succ hchild) hdrop
              | none =>
                  cases hinner : inner current SearchTraceSignature.empty entry.budget with
                  | inr pair =>
                      have hone : 1 ≤ Catalog.remainingCount C s.visited := by
                        exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hdrop
                      simpa [catalogRem, preTrace, hchoose, hentry, hpre, hinner] using hone
                  | inl trace' =>
                      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          have hchild := ih (s := s.mark_visited current)
                            (auditSoFar := {
                              language := current
                              firedClause := clause
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := loops.patterns.find? (fun p => p.fires trace') } :: auditSoFar)
                          simpa [catalogRem, preTrace, hchoose, hentry, hpre, hinner, hpost] using
                            Nat.le_trans (Nat.succ_le_succ hchild) hdrop
                      | none =>
                          have hchild := ih (s := s.mark_visited current)
                            (auditSoFar := {
                              language := current
                              firedClause := MetaHaltClause.budgetExhausted
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := none } :: auditSoFar)
                          simpa [catalogRem, preTrace, hchoose, hentry, hpre, hinner, hpost] using
                            Nat.le_trans (Nat.succ_le_succ hchild) hdrop

/-- Every audit entry records the core fields of the audit-complete C3 object. -/
theorem audit_entry_fields_total (e : LanguageAuditEntry) :
    e.language = e.language ∧
    e.firedClause = e.firedClause ∧
    e.allocatedBudget = e.allocatedBudget ∧
    e.stepsConsumed = e.stepsConsumed ∧
    e.candidateCount = e.candidateCount := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Proposition 5.6, explicit step bound. -/
theorem supervisoryLoop_terminates_in_catalog_budget
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : SupervisoryLoopState) :
    ∃ (outcome : SupervisoryLoopOutcome) (steps : Nat),
      steps ≤ Catalog.totalBudgetPlusOne C ∧
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] = outcome := by
  refine ⟨(supervisoryLoopWithSteps (C.size + 1) C policy admiss loops inner O s []).2,
    (supervisoryLoopWithSteps (C.size + 1) C policy admiss loops inner O s []).1,
    ?_, ?_⟩
  · exact Nat.le_trans
      (supervisoryLoopWithSteps_fst_le_remainingCount (C.size + 1) C policy admiss loops inner O s [])
      (Nat.le_trans (remainingCount_le_size C s.visited) (size_le_totalBudgetPlusOne C))
  · simpa using supervisoryLoopWithSteps_snd (C.size + 1) C policy admiss loops inner O s []

/-- The supervisory loop emits exactly one of the two terminal outcome forms. -/
theorem supervisoryLoop_emits_c3_or_c1c2
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : SupervisoryLoopState) :
    let out := supervisoryLoop (C.size + 1) C policy admiss loops inner O s []
    (∃ L o, out = .acceptedWitness L o) ∨ (∃ rec, out = .auditC3 rec) := by
  dsimp
  cases h : supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] with
  | acceptedWitness L o =>
      exact Or.inl ⟨L, o, rfl⟩
  | auditC3 rec =>
      exact Or.inr ⟨rec, rfl⟩

/-! ## Factoring through the generic supervisory engine -/

abbrev GenericLoopState :=
  OperatorKO7.SupervisoryEngine.LoopState LanguageSignature SearchTraceSignature

abbrev GenericLoopOutcome :=
  OperatorKO7.SupervisoryEngine.LoopOutcome
    LanguageSignature TypedOutput LanguageAuditEntry

def toGenericLoopState (s : SupervisoryLoopState) : GenericLoopState :=
  { visited := s.visited
    trace := s.trace
    currLang := s.currLang
    usedSteps := s.usedSteps }

def genericAuditReportToConcrete
    (r : OperatorKO7.SupervisoryEngine.AuditReport LanguageAuditEntry) :
    AuditCompleteC3Record :=
  { auditEntries := r.auditEntries, checkerLog := r.checkerLog }

def genericLoopOutcomeToConcrete (out : GenericLoopOutcome) :
    SupervisoryLoopOutcome :=
  match out with
  | .acceptedWitness L o => .acceptedWitness L o
  | .auditC3 rec => .auditC3 (genericAuditReportToConcrete rec)

def genericLoopWithStepsToConcrete
    (p : Nat × GenericLoopOutcome) : Nat × SupervisoryLoopOutcome :=
  (p.1, genericLoopOutcomeToConcrete p.2)

def genericCatalogInterface :
    OperatorKO7.SupervisoryEngine.CatalogInterface
      Catalog CatalogEntry LanguageSignature where
  entries := Catalog.entries
  language := CatalogEntry.language
  budget := CatalogEntry.budget
  entryOf := Catalog.entryOf
  entryOf_mem := exists_entry_of_entryOf_eq_some

def genericLiftPolicy (policy : CatalogLiftPolicy) :
    OperatorKO7.SupervisoryEngine.LiftPolicy Catalog LanguageSignature where
  choose := policy.choose
  never_revisits := policy.never_revisits

def genericDetectLoop (loops : LoopPatternTable) :
    SearchTraceSignature → Option LoopPattern :=
  fun T => loops.patterns.find? (fun p => p.fires T)

def genericMetaHalt (admiss : AdmissibilityTable) (loops : LoopPatternTable) :
    ObligationSignature →
      LanguageSignature → SearchTraceSignature → Nat → Nat → Option MetaHaltClause :=
  fun O L T budget catalogRem => metaHalt O L T admiss loops budget catalogRem

def genericAuditBuilder
    (L : LanguageSignature)
    (clause : MetaHaltClause)
    (budget : Nat)
    (trace : SearchTraceSignature)
    (hit : Option LoopPattern) :
    LanguageAuditEntry :=
  { language := L
    firedClause := clause
    allocatedBudget := budget
    stepsConsumed := trace.stepsConsumed
    candidateCount := trace.candidateCount
    partialTraceTags := trace.traceTags
    loopPatternHit := hit }

def supervisoryLoopViaGeneric
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) : GenericLoopOutcome :=
  OperatorKO7.SupervisoryEngine.supervisoryLoop
    genericCatalogInterface
    fuel
    C
    (genericLiftPolicy policy)
    (genericMetaHalt admiss loops)
    (genericDetectLoop loops)
    inner
    MetaHaltClause.budgetExhausted
    genericAuditBuilder
    O
    (toGenericLoopState s)
    auditSoFar
    SearchTraceSignature.empty

def supervisoryLoopWithStepsViaGeneric
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) : Nat × GenericLoopOutcome :=
  OperatorKO7.SupervisoryEngine.supervisoryLoopWithSteps
    genericCatalogInterface
    fuel
    C
    (genericLiftPolicy policy)
    (genericMetaHalt admiss loops)
    (genericDetectLoop loops)
    inner
    MetaHaltClause.budgetExhausted
    genericAuditBuilder
    O
    (toGenericLoopState s)
    auditSoFar
    SearchTraceSignature.empty

@[simp] theorem generic_totalBudgetPlusOne_eq (C : Catalog) :
    genericCatalogInterface.totalBudgetPlusOne C = Catalog.totalBudgetPlusOne C := rfl

@[simp] theorem supervisoryLoop_factors_through_generic_engine
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    supervisoryLoop fuel C policy admiss loops inner O s auditSoFar =
      genericLoopOutcomeToConcrete
        (supervisoryLoopViaGeneric fuel C policy admiss loops inner O s auditSoFar) := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [supervisoryLoop, supervisoryLoopViaGeneric,
        OperatorKO7.SupervisoryEngine.supervisoryLoop,
        genericCatalogInterface, genericLiftPolicy, genericDetectLoop, genericMetaHalt,
        genericAuditBuilder, genericLoopOutcomeToConcrete,
        genericAuditReportToConcrete, toGenericLoopState]
  | succ fuel ih =>
      simp [supervisoryLoop, supervisoryLoopViaGeneric,
        OperatorKO7.SupervisoryEngine.supervisoryLoop,
        genericCatalogInterface, genericLiftPolicy, genericDetectLoop, genericMetaHalt, genericAuditBuilder,
        genericLoopOutcomeToConcrete, genericAuditReportToConcrete,
        toGenericLoopState]
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [hchoose]
      | some current =>
          cases hentry : Catalog.entryOf C current with
          | none =>
              simp [hchoose, hentry]
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              cases hpre : metaHalt O current SearchTraceSignature.empty admiss loops entry.budget catalogRem with
              | some clause =>
                  simp [catalogRem, hchoose, hentry, hpre, ih]
              | none =>
                  cases hinner : inner current SearchTraceSignature.empty entry.budget with
                  | inr pair =>
                      simp [catalogRem, hchoose, hentry, hpre, hinner]
                  | inl trace' =>
                      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          simp [catalogRem, hchoose, hentry, hpre, hinner, hpost, ih]
                      | none =>
                          simp [catalogRem, hchoose, hentry, hpre, hinner, hpost, ih]

@[simp] theorem supervisoryLoopWithSteps_factors_through_generic_engine
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : SupervisoryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    supervisoryLoopWithSteps fuel C policy admiss loops inner O s auditSoFar =
      genericLoopWithStepsToConcrete
        (supervisoryLoopWithStepsViaGeneric fuel C policy admiss loops inner O s auditSoFar) := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [supervisoryLoopWithSteps, supervisoryLoopWithStepsViaGeneric,
        OperatorKO7.SupervisoryEngine.supervisoryLoopWithSteps,
        genericCatalogInterface, genericLiftPolicy, genericDetectLoop, genericMetaHalt,
        genericAuditBuilder, genericLoopWithStepsToConcrete,
        genericLoopOutcomeToConcrete, genericAuditReportToConcrete,
        toGenericLoopState]
  | succ fuel ih =>
      simp [supervisoryLoopWithSteps, supervisoryLoopWithStepsViaGeneric,
        OperatorKO7.SupervisoryEngine.supervisoryLoopWithSteps,
        genericCatalogInterface, genericLiftPolicy, genericDetectLoop, genericMetaHalt, genericAuditBuilder,
        genericLoopWithStepsToConcrete, genericLoopOutcomeToConcrete,
        genericAuditReportToConcrete, toGenericLoopState]
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [hchoose]
      | some current =>
          cases hentry : Catalog.entryOf C current with
          | none =>
              simp [hchoose, hentry]
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              cases hpre : metaHalt O current SearchTraceSignature.empty admiss loops entry.budget catalogRem with
              | some clause =>
                  simp [catalogRem, hchoose, hentry, hpre, ih]
              | none =>
                  cases hinner : inner current SearchTraceSignature.empty entry.budget with
                  | inr pair =>
                      simp [catalogRem, hchoose, hentry, hpre, hinner]
                  | inl trace' =>
                      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          simp [catalogRem, hchoose, hentry, hpre, hinner, hpost, ih]
                      | none =>
                          simp [catalogRem, hchoose, hentry, hpre, hinner, hpost, ih]

/-- The concrete META-HALT loop inherits the generic engine's step bound. -/
theorem supervisoryLoop_terminates_via_generic_engine
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : SupervisoryLoopState) :
    ∃ (outcome : SupervisoryLoopOutcome) (steps : Nat),
      steps ≤ Catalog.totalBudgetPlusOne C ∧
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] = outcome := by
  rcases OperatorKO7.SupervisoryEngine.supervisoryLoop_terminates_in_catalog_budget
      genericCatalogInterface C (genericLiftPolicy policy) (genericMetaHalt admiss loops)
      (genericDetectLoop loops) inner MetaHaltClause.budgetExhausted
      genericAuditBuilder O (toGenericLoopState s) SearchTraceSignature.empty with
    ⟨outcome, steps, hsteps, hout⟩
  have hout' :
      supervisoryLoopViaGeneric (C.size + 1) C policy admiss loops inner O s [] = outcome := by
    simpa [supervisoryLoopViaGeneric, genericCatalogInterface,
      genericLiftPolicy, genericMetaHalt, genericDetectLoop, genericAuditBuilder,
      toGenericLoopState, Catalog.size,
      OperatorKO7.SupervisoryEngine.CatalogInterface.size] using hout
  refine ⟨genericLoopOutcomeToConcrete outcome, steps, ?_, ?_⟩
  · simpa [generic_totalBudgetPlusOne_eq] using hsteps
  · calc
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] =
          genericLoopOutcomeToConcrete
            (supervisoryLoopViaGeneric (C.size + 1) C policy admiss loops inner O s []) := by
              simpa using supervisoryLoop_factors_through_generic_engine
                (C.size + 1) C policy admiss loops inner O s []
      _ = genericLoopOutcomeToConcrete outcome := by rw [hout']

/-- The concrete META-HALT loop also inherits the generic engine's terminal-form
disjunction. -/
theorem supervisoryLoop_emits_c3_or_c1c2_via_generic_engine
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : SupervisoryLoopState) :
    let out := supervisoryLoop (C.size + 1) C policy admiss loops inner O s []
    (∃ L o, out = .acceptedWitness L o) ∨ (∃ rec, out = .auditC3 rec) := by
  have hgen :=
    OperatorKO7.SupervisoryEngine.supervisoryLoop_emits_audit_or_accept
      genericCatalogInterface C (genericLiftPolicy policy) (genericMetaHalt admiss loops)
      (genericDetectLoop loops) inner MetaHaltClause.budgetExhausted
      genericAuditBuilder O (toGenericLoopState s) SearchTraceSignature.empty
  have hgen' :
      let out := supervisoryLoopViaGeneric (C.size + 1) C policy admiss loops inner O s []
      (∃ L o, out = .acceptedWitness L o) ∨ (∃ rec, out = .auditC3 rec) := by
    simpa [supervisoryLoopViaGeneric, genericCatalogInterface,
      genericLiftPolicy, genericMetaHalt, genericDetectLoop, genericAuditBuilder,
      toGenericLoopState, Catalog.size,
      OperatorKO7.SupervisoryEngine.CatalogInterface.size] using hgen
  dsimp at hgen' ⊢
  rw [supervisoryLoop_factors_through_generic_engine (C.size + 1) C policy admiss loops inner O s []]
  rcases hgen' with hacc | haudit
  · rcases hacc with ⟨L, o, hEq⟩
    exact Or.inl ⟨L, o, by simpa [genericLoopOutcomeToConcrete] using congrArg genericLoopOutcomeToConcrete hEq⟩
  · rcases haudit with ⟨rec, hEq⟩
    exact Or.inr ⟨genericAuditReportToConcrete rec, by
      simpa [genericLoopOutcomeToConcrete, genericAuditReportToConcrete] using
        congrArg genericLoopOutcomeToConcrete hEq⟩

end OperatorKO7.MetaHalt.Regress
