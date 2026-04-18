import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Basic

/-!
# Generic Supervisory Engine

Reusable catalog-driven supervisory engine abstracted from the concrete
META-HALT loop.

This module isolates the executable mechanics:

- finite catalog traversal;
- never-revisit scheduling policy;
- per-language budgets;
- pre/post gate checks;
- audit accumulation;
- explicit step-count execution and step-budget theorem.

It does **not** commit to a particular admissibility semantics, loop-pattern
family, witness language, or typed-output algebra. Those are supplied by the
instantiating layer.
-/

namespace OperatorKO7.SupervisoryEngine

/-- Generic catalog interface used by the supervisory engine. -/
structure CatalogInterface (Catalog Entry Lang : Type) [DecidableEq Lang] where
  entries : Catalog → List Entry
  language : Entry → Lang
  budget : Entry → Nat
  entryOf : Catalog → Lang → Option Entry
  entryOf_mem : ∀ (C : Catalog) (L : Lang) (e : Entry),
    entryOf C L = some e → ∃ e' ∈ entries C, language e' = L

namespace CatalogInterface

variable {Catalog Entry Lang : Type} [DecidableEq Lang]

/-- Cardinality of the catalog. -/
def size (I : CatalogInterface Catalog Entry Lang) (C : Catalog) : Nat :=
  (I.entries C).length

/-- Number of still-unvisited catalog entries. -/
def remainingCount (I : CatalogInterface Catalog Entry Lang)
    (C : Catalog) (visited : List Lang) : Nat :=
  (I.entries C).countP (fun e => I.language e ∉ visited)

/-- Sum of all per-language budgets, with one extra supervisory step per
catalog entry. -/
def totalBudgetPlusOne (I : CatalogInterface Catalog Entry Lang) (C : Catalog) : Nat :=
  (I.entries C).foldr (fun e acc => acc + (I.budget e + 1)) 0

end CatalogInterface

/-- Scheduling policy for choosing the next unvisited catalog item. -/
structure LiftPolicy (Catalog Lang : Type) where
  choose : Catalog → List Lang → Option Lang
  never_revisits :
    ∀ (C : Catalog) (visited : List Lang) (L : Lang),
      choose C visited = some L → L ∉ visited

/-- Generic supervisory loop state. -/
structure LoopState (Lang Trace : Type) where
  visited : List Lang
  trace : Trace
  currLang : Option Lang
  usedSteps : Nat

namespace LoopState

variable {Lang Trace : Type}

/-- Mark a language as visited and reset the current trace. -/
def markVisited (s : LoopState Lang Trace) (L : Lang) (emptyTrace : Trace) :
    LoopState Lang Trace :=
  { s with visited := L :: s.visited, currLang := none, trace := emptyTrace }

/-- Set the current language and reset the object-level trace. -/
def setCurrent (s : LoopState Lang Trace) (L : Lang) (emptyTrace : Trace) :
    LoopState Lang Trace :=
  { s with currLang := some L, trace := emptyTrace }

end LoopState

/-- Generic audit-complete report. -/
structure AuditReport (Audit : Type) where
  auditEntries : List Audit
  checkerLog : List String
  deriving Repr

/-- Terminal outcome of the generic supervisory loop. -/
inductive LoopOutcome (Lang Out Audit : Type)
  | acceptedWitness (L : Lang) (out : Out)
  | auditC3 (record : AuditReport Audit)
  deriving Repr

abbrev InnerSearchStep (Lang Trace Out : Type) :=
  Lang → Trace → Nat → Trace ⊕ (Lang × Out)

section Engine

variable {Catalog Entry Lang Trace Obligation Clause LoopMark Out Audit : Type}
variable [DecidableEq Lang]

/-- Generic catalog-driven supervisory loop. -/
def supervisoryLoop
    (I : CatalogInterface Catalog Entry Lang)
    (fuel : Nat)
    (C : Catalog)
    (policy : LiftPolicy Catalog Lang)
    (gate : Obligation → Lang → Trace → Nat → Nat → Option Clause)
    (detectLoop : Trace → Option LoopMark)
    (inner : InnerSearchStep Lang Trace Out)
    (budgetExhausted : Clause)
    (mkAudit : Lang → Clause → Nat → Trace → Option LoopMark → Audit)
    (O : Obligation)
    (s : LoopState Lang Trace)
    (auditSoFar : List Audit)
    (emptyTrace : Trace) : LoopOutcome Lang Out Audit :=
  match fuel with
  | 0 =>
      .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
  | fuel + 1 =>
      match policy.choose C s.visited with
      | none =>
          .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
      | some L =>
          match I.entryOf C L with
          | none =>
              .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
          | some entry =>
              let catalogRem := I.size C - s.visited.length - 1
              match gate O L emptyTrace (I.budget entry) catalogRem with
              | some clause =>
                  let audit := mkAudit L clause (I.budget entry) emptyTrace (detectLoop emptyTrace)
                  supervisoryLoop I fuel C policy gate detectLoop inner budgetExhausted mkAudit O
                    (s.markVisited L emptyTrace) (audit :: auditSoFar) emptyTrace
              | none =>
                  match inner L emptyTrace (I.budget entry) with
                  | .inr (_Lacc, out) =>
                      .acceptedWitness L out
                  | .inl trace' =>
                      match gate O L trace' (I.budget entry) catalogRem with
                      | some clause =>
                          let audit := mkAudit L clause (I.budget entry) trace' (detectLoop trace')
                          supervisoryLoop I fuel C policy gate detectLoop inner budgetExhausted mkAudit O
                            (s.markVisited L emptyTrace) (audit :: auditSoFar) emptyTrace
                      | none =>
                          let audit := mkAudit L budgetExhausted (I.budget entry) trace' none
                          supervisoryLoop I fuel C policy gate detectLoop inner budgetExhausted mkAudit O
                            (s.markVisited L emptyTrace) (audit :: auditSoFar) emptyTrace
termination_by fuel

/-- Execution function that returns both outcome and number of catalog-level
steps traversed. -/
def supervisoryLoopWithSteps
    (I : CatalogInterface Catalog Entry Lang)
    (fuel : Nat)
    (C : Catalog)
    (policy : LiftPolicy Catalog Lang)
    (gate : Obligation → Lang → Trace → Nat → Nat → Option Clause)
    (detectLoop : Trace → Option LoopMark)
    (inner : InnerSearchStep Lang Trace Out)
    (budgetExhausted : Clause)
    (mkAudit : Lang → Clause → Nat → Trace → Option LoopMark → Audit)
    (O : Obligation)
    (s : LoopState Lang Trace)
    (auditSoFar : List Audit)
    (emptyTrace : Trace) : Nat × LoopOutcome Lang Out Audit :=
  match fuel with
  | 0 =>
      (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
  | fuel + 1 =>
      match policy.choose C s.visited with
      | none =>
          (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
      | some L =>
          match I.entryOf C L with
          | none =>
              (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
          | some entry =>
              let catalogRem := I.size C - s.visited.length - 1
              match gate O L emptyTrace (I.budget entry) catalogRem with
              | some clause =>
                  let audit := mkAudit L clause (I.budget entry) emptyTrace (detectLoop emptyTrace)
                  let recResult := supervisoryLoopWithSteps I fuel C policy gate detectLoop inner
                    budgetExhausted mkAudit O (s.markVisited L emptyTrace) (audit :: auditSoFar) emptyTrace
                  (recResult.1 + 1, recResult.2)
              | none =>
                  match inner L emptyTrace (I.budget entry) with
                  | .inr (_Lacc, out) =>
                      (1, .acceptedWitness L out)
                  | .inl trace' =>
                      match gate O L trace' (I.budget entry) catalogRem with
                      | some clause =>
                          let audit := mkAudit L clause (I.budget entry) trace' (detectLoop trace')
                          let recResult := supervisoryLoopWithSteps I fuel C policy gate detectLoop inner
                            budgetExhausted mkAudit O (s.markVisited L emptyTrace) (audit :: auditSoFar) emptyTrace
                          (recResult.1 + 1, recResult.2)
                      | none =>
                          let audit := mkAudit L budgetExhausted (I.budget entry) trace' none
                          let recResult := supervisoryLoopWithSteps I fuel C policy gate detectLoop inner
                            budgetExhausted mkAudit O (s.markVisited L emptyTrace) (audit :: auditSoFar) emptyTrace
                          (recResult.1 + 1, recResult.2)
termination_by fuel

@[simp] theorem supervisoryLoopWithSteps_snd
    (I : CatalogInterface Catalog Entry Lang)
    (fuel : Nat)
    (C : Catalog)
    (policy : LiftPolicy Catalog Lang)
    (gate : Obligation → Lang → Trace → Nat → Nat → Option Clause)
    (detectLoop : Trace → Option LoopMark)
    (inner : InnerSearchStep Lang Trace Out)
    (budgetExhausted : Clause)
    (mkAudit : Lang → Clause → Nat → Trace → Option LoopMark → Audit)
    (O : Obligation)
    (s : LoopState Lang Trace)
    (auditSoFar : List Audit)
    (emptyTrace : Trace) :
    (supervisoryLoopWithSteps I fuel C policy gate detectLoop inner budgetExhausted mkAudit O s auditSoFar emptyTrace).2 =
      supervisoryLoop I fuel C policy gate detectLoop inner budgetExhausted mkAudit O s auditSoFar emptyTrace := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [supervisoryLoopWithSteps, supervisoryLoop]
  | succ fuel ih =>
      simp [supervisoryLoopWithSteps, supervisoryLoop]
      cases hchoose : policy.choose C s.visited <;> simp [hchoose, ih]
      rename_i current
      cases hentry : I.entryOf C current <;> simp [hchoose, hentry, ih]
      rename_i entry
      let catalogRem := I.size C - s.visited.length - 1
      cases hpre : gate O current emptyTrace (I.budget entry) catalogRem <;>
        simp [catalogRem, hchoose, hentry, hpre, ih]
      cases hinner : inner current emptyTrace (I.budget entry) <;>
        simp [catalogRem, hchoose, hentry, hpre, hinner, ih]
      rename_i trace'
      cases hpost : gate O current trace' (I.budget entry) catalogRem <;>
        simp [catalogRem, hchoose, hentry, hpre, hinner, hpost, ih]

private theorem remainingCount_cons_le
    (I : CatalogInterface Catalog Entry Lang)
    (entries : List Entry)
    (visited : List Lang)
    (current : Lang) :
    entries.countP (fun e => I.language e ∉ current :: visited) ≤
      entries.countP (fun e => I.language e ∉ visited) := by
  induction entries with
  | nil => simp
  | cons x xs ih =>
      by_cases hv : I.language x ∉ visited
      · by_cases hx : I.language x = current
        · have hstep : xs.countP (fun e => I.language e ∉ visited) ≤
            (x :: xs).countP (fun e => I.language e ∉ visited) := by
            simpa [hv] using Nat.le_succ (xs.countP (fun e => I.language e ∉ visited))
          simpa [hv, hx] using Nat.le_trans ih hstep
        · have hv' : I.language x ∉ current :: visited := by
            simp [hx, hv]
          simpa [hv, hv', hx] using Nat.succ_le_succ ih
      · have hv' : ¬ I.language x ∉ current :: visited := by
          intro h
          exact hv (fun hmem => h (by simp [hmem]))
        simpa [hv, hv'] using ih

private theorem remainingCount_markVisited_succ_le_entries
    (I : CatalogInterface Catalog Entry Lang)
    (entries : List Entry)
    (visited : List Lang)
    (current : Lang)
    (hnotin : current ∉ visited)
    (hex : ∃ e' ∈ entries, I.language e' = current) :
    entries.countP (fun e => I.language e ∉ current :: visited) + 1 ≤
      entries.countP (fun e => I.language e ∉ visited) := by
  induction entries with
  | nil =>
      rcases hex with ⟨e, he, _⟩
      cases he
  | cons x xs ih =>
      rcases hex with ⟨e, he, heq⟩
      by_cases hx : I.language x = current
      · have hmono := remainingCount_cons_le I xs visited current
        have hxNot : I.language x ∉ visited := by
          simpa [hx] using hnotin
        calc
          (x :: xs).countP (fun e => I.language e ∉ current :: visited) + 1
              = xs.countP (fun e => I.language e ∉ current :: visited) + 1 := by
                  simp [hx]
          _ ≤ xs.countP (fun e => I.language e ∉ visited) + 1 :=
              Nat.add_le_add_right hmono 1
          _ = (x :: xs).countP (fun e => I.language e ∉ visited) := by
              symm
              simp [hxNot, Nat.add_comm]
      · have hexs : ∃ e' ∈ xs, I.language e' = current := by
          cases he with
          | head => exact False.elim (hx heq)
          | tail _ hmem => exact ⟨e, hmem, heq⟩
        have hrec := ih hexs
        by_cases hv : I.language x ∉ visited
        · have hv' : I.language x ∉ current :: visited := by
            simp [hx, hv]
          simpa [hx, hv, hv'] using Nat.succ_le_succ hrec
        · have hv' : ¬ I.language x ∉ current :: visited := by
            intro h
            exact hv (fun hmem => h (by simp [hmem]))
          simpa [hx, hv, hv'] using hrec

private theorem remainingCount_markVisited_succ_le
    (I : CatalogInterface Catalog Entry Lang)
    (C : Catalog)
    (visited : List Lang)
    (current : Lang)
    (entry : Entry)
    (hentry : I.entryOf C current = some entry)
    (hnotin : current ∉ visited) :
    I.remainingCount C (current :: visited) + 1 ≤ I.remainingCount C visited := by
  have hex : ∃ e' ∈ I.entries C, I.language e' = current :=
    I.entryOf_mem C current entry hentry
  unfold CatalogInterface.remainingCount
  exact remainingCount_markVisited_succ_le_entries I (I.entries C) visited current hnotin hex

private theorem remainingCount_le_size
    (I : CatalogInterface Catalog Entry Lang)
    (C : Catalog)
    (visited : List Lang) :
    I.remainingCount C visited ≤ I.size C := by
  unfold CatalogInterface.remainingCount CatalogInterface.size
  exact List.countP_le_length

private theorem size_le_totalBudgetPlusOne_entries
    (I : CatalogInterface Catalog Entry Lang)
    (entries : List Entry) :
    entries.length ≤ entries.foldr (fun e acc => acc + (I.budget e + 1)) 0 := by
  induction entries with
  | nil => simp
  | cons e es ih =>
      have hstep : es.length + 1 ≤ es.foldr (fun e acc => acc + (I.budget e + 1)) 0 + 1 :=
        Nat.succ_le_succ ih
      have hone : es.foldr (fun e acc => acc + (I.budget e + 1)) 0 + 1 ≤
          es.foldr (fun e acc => acc + (I.budget e + 1)) 0 + (I.budget e + 1) := by
        exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le (I.budget e))) _
      exact Nat.le_trans hstep hone

private theorem size_le_totalBudgetPlusOne
    (I : CatalogInterface Catalog Entry Lang)
    (C : Catalog) :
    I.size C ≤ I.totalBudgetPlusOne C := by
  unfold CatalogInterface.size CatalogInterface.totalBudgetPlusOne
  exact size_le_totalBudgetPlusOne_entries I (I.entries C)

private theorem supervisoryLoopWithSteps_fst_le_remainingCount
    (I : CatalogInterface Catalog Entry Lang)
    (fuel : Nat)
    (C : Catalog)
    (policy : LiftPolicy Catalog Lang)
    (gate : Obligation → Lang → Trace → Nat → Nat → Option Clause)
    (detectLoop : Trace → Option LoopMark)
    (inner : InnerSearchStep Lang Trace Out)
    (budgetExhausted : Clause)
    (mkAudit : Lang → Clause → Nat → Trace → Option LoopMark → Audit)
    (O : Obligation)
    (s : LoopState Lang Trace)
    (auditSoFar : List Audit)
    (emptyTrace : Trace) :
    (supervisoryLoopWithSteps I fuel C policy gate detectLoop inner budgetExhausted mkAudit O s auditSoFar emptyTrace).1 ≤
      I.remainingCount C s.visited := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [supervisoryLoopWithSteps, CatalogInterface.remainingCount]
  | succ fuel ih =>
      simp [supervisoryLoopWithSteps]
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [hchoose, CatalogInterface.remainingCount]
      | some current =>
          cases hentry : I.entryOf C current with
          | none =>
              simp [hchoose, hentry, CatalogInterface.remainingCount]
          | some entry =>
              have hnotin : current ∉ s.visited := policy.never_revisits C s.visited current hchoose
              have hdrop : I.remainingCount C (current :: s.visited) + 1 ≤ I.remainingCount C s.visited :=
                remainingCount_markVisited_succ_le I C s.visited current entry hentry hnotin
              let catalogRem := I.size C - s.visited.length - 1
              cases hpre : gate O current emptyTrace (I.budget entry) catalogRem with
              | some clause =>
                  have hchild := ih (s := s.markVisited current emptyTrace)
                    (auditSoFar := mkAudit current clause (I.budget entry) emptyTrace (detectLoop emptyTrace) :: auditSoFar)
                  simpa [catalogRem, hchoose, hentry, hpre] using
                    Nat.le_trans (Nat.succ_le_succ hchild) hdrop
              | none =>
                  cases hinner : inner current emptyTrace (I.budget entry) with
                  | inr pair =>
                      have hone : 1 ≤ I.remainingCount C s.visited := by
                        exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hdrop
                      simpa [catalogRem, hchoose, hentry, hpre, hinner] using hone
                  | inl trace' =>
                      cases hpost : gate O current trace' (I.budget entry) catalogRem with
                      | some clause =>
                          have hchild := ih (s := s.markVisited current emptyTrace)
                            (auditSoFar := mkAudit current clause (I.budget entry) trace' (detectLoop trace') :: auditSoFar)
                          simpa [catalogRem, hchoose, hentry, hpre, hinner, hpost] using
                            Nat.le_trans (Nat.succ_le_succ hchild) hdrop
                      | none =>
                          have hchild := ih (s := s.markVisited current emptyTrace)
                            (auditSoFar := mkAudit current budgetExhausted (I.budget entry) trace' none :: auditSoFar)
                          simpa [catalogRem, hchoose, hentry, hpre, hinner, hpost] using
                            Nat.le_trans (Nat.succ_le_succ hchild) hdrop

/-- Explicit step bound for the generic supervisory engine. -/
theorem supervisoryLoop_terminates_in_catalog_budget
    (I : CatalogInterface Catalog Entry Lang)
    (C : Catalog)
    (policy : LiftPolicy Catalog Lang)
    (gate : Obligation → Lang → Trace → Nat → Nat → Option Clause)
    (detectLoop : Trace → Option LoopMark)
    (inner : InnerSearchStep Lang Trace Out)
    (budgetExhausted : Clause)
    (mkAudit : Lang → Clause → Nat → Trace → Option LoopMark → Audit)
    (O : Obligation)
    (s : LoopState Lang Trace)
    (emptyTrace : Trace) :
    ∃ (outcome : LoopOutcome Lang Out Audit) (steps : Nat),
      steps ≤ I.totalBudgetPlusOne C ∧
      supervisoryLoop I (I.size C + 1) C policy gate detectLoop inner budgetExhausted mkAudit O s [] emptyTrace = outcome := by
  refine ⟨(supervisoryLoopWithSteps I (I.size C + 1) C policy gate detectLoop inner budgetExhausted mkAudit O s [] emptyTrace).2,
    (supervisoryLoopWithSteps I (I.size C + 1) C policy gate detectLoop inner budgetExhausted mkAudit O s [] emptyTrace).1,
    ?_, ?_⟩
  · exact Nat.le_trans
      (supervisoryLoopWithSteps_fst_le_remainingCount I (I.size C + 1) C policy gate detectLoop inner budgetExhausted mkAudit O s [] emptyTrace)
      (Nat.le_trans (remainingCount_le_size I C s.visited) (size_le_totalBudgetPlusOne I C))
  · simpa using supervisoryLoopWithSteps_snd I (I.size C + 1) C policy gate detectLoop inner budgetExhausted mkAudit O s [] emptyTrace

/-- The generic supervisory loop emits exactly one of the two terminal outcome
forms. -/
theorem supervisoryLoop_emits_audit_or_accept
    (I : CatalogInterface Catalog Entry Lang)
    (C : Catalog)
    (policy : LiftPolicy Catalog Lang)
    (gate : Obligation → Lang → Trace → Nat → Nat → Option Clause)
    (detectLoop : Trace → Option LoopMark)
    (inner : InnerSearchStep Lang Trace Out)
    (budgetExhausted : Clause)
    (mkAudit : Lang → Clause → Nat → Trace → Option LoopMark → Audit)
    (O : Obligation)
    (s : LoopState Lang Trace)
    (emptyTrace : Trace) :
    let out := supervisoryLoop I (I.size C + 1) C policy gate detectLoop inner budgetExhausted mkAudit O s [] emptyTrace
    (∃ L o, out = .acceptedWitness L o) ∨ (∃ rec, out = .auditC3 rec) := by
  dsimp
  cases h : supervisoryLoop I (I.size C + 1) C policy gate detectLoop inner budgetExhausted mkAudit O s [] emptyTrace with
  | acceptedWitness L o =>
      exact Or.inl ⟨L, o, rfl⟩
  | auditC3 rec =>
      exact Or.inr ⟨rec, rfl⟩

end Engine

end OperatorKO7.SupervisoryEngine
