import OperatorKO7.Meta.FiniteGraphReachability

/-!
# Finite Graph SCC Witness Packaging

This module packages one more automation layer on top of finite reachability.
For a finite decidable directed graph, callers can state only that a nontrivial SCC
exists, and the concrete node pair plus both reachability directions are recovered
internally.

The point is not to solve SCC discovery for arbitrary TRSs. The point is to remove
the remaining hand-written pair / round-trip packaging layer once a finite graph
relation is already fixed.
-/

namespace OperatorKO7.FiniteGraphSCC

open OperatorKO7.FiniteGraphReachability

variable {α : Type} (R : α → α → Prop) [Fintype α] [DecidableEq α] [DecidableRel R]

/-- Two distinct nodes lie in the same SCC when each reaches the other. -/
def NontrivialRoundTrip (a b : α) : Prop :=
  a ≠ b ∧ Reachable R a b ∧ Reachable R b a

/-- A finite graph has a nontrivial SCC if some distinct pair lies in the same SCC. -/
def HasNontrivialSCC : Prop :=
  ∃ a b, NontrivialRoundTrip R a b

instance instDecidableNontrivialRoundTrip (a b : α) :
    Decidable (NontrivialRoundTrip R a b) := by
  unfold NontrivialRoundTrip Reachable
  infer_instance

/-- All candidate node pairs in the finite graph. -/
def candidatePairs (α : Type) [Fintype α] : Finset (α × α) :=
  Finset.univ.product Finset.univ

/-- The finite set of distinct mutually reachable node pairs. -/
def sccPairs (R : α → α → Prop) [Fintype α] [DecidableEq α] [DecidableRel R] : Finset (α × α) :=
  (candidatePairs α).filter fun p => decide (NontrivialRoundTrip R p.1 p.2)

theorem mem_sccPairs {p : α × α} :
    p ∈ sccPairs R ↔ NontrivialRoundTrip R p.1 p.2 := by
  simp [sccPairs, candidatePairs, NontrivialRoundTrip]

theorem sccPairs_nonempty_iff :
    (sccPairs R).Nonempty ↔ HasNontrivialSCC R := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, (mem_sccPairs (R := R)).1 hp⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨(a, b), (mem_sccPairs (R := R)).2 hab⟩

/-- Computable search for a concrete SCC pair on a finite graph. -/
noncomputable def findNontrivialSCCPair? : Option (α × α) :=
  (sccPairs R).toList.head?

theorem findNontrivialSCCPair?_spec {p : α × α}
    (h : findNontrivialSCCPair? (R := R) = some p) :
    NontrivialRoundTrip R p.1 p.2 := by
  classical
  have hmemList : p ∈ (sccPairs R).toList := by
    exact List.mem_of_head? (by simpa [findNontrivialSCCPair?] using h)
  have hmem : p ∈ sccPairs R := by
    simpa using hmemList
  exact (mem_sccPairs (R := R)).1 hmem

theorem exists_findNontrivialSCCPair?_eq_some
    (h : HasNontrivialSCC R) :
    ∃ p : α × α, findNontrivialSCCPair? (R := R) = some p := by
  classical
  have hs : (sccPairs R).Nonempty := (sccPairs_nonempty_iff (R := R)).2 h
  cases hlist : (sccPairs R).toList with
  | nil =>
      exfalso
      exact hs.toList_ne_nil hlist
  | cons p ps =>
      exact ⟨p, by simp [findNontrivialSCCPair?, hlist]⟩

theorem hasNontrivialSCC_iff_exists_findNontrivialSCCPair? :
    HasNontrivialSCC R ↔ ∃ p : α × α, findNontrivialSCCPair? (R := R) = some p := by
  constructor
  · exact exists_findNontrivialSCCPair?_eq_some (R := R)
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, findNontrivialSCCPair?_spec (R := R) hp⟩

theorem hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some {p : α × α}
    (h : findNontrivialSCCPair? (R := R) = some p) :
    HasNontrivialSCC R := by
  exact ⟨p.1, p.2, findNontrivialSCCPair?_spec (R := R) h⟩

theorem findNontrivialSCCPair?_eq_none_iff_not_hasNontrivialSCC :
    findNontrivialSCCPair? (R := R) = none ↔ ¬ HasNontrivialSCC R := by
  constructor
  · intro hnone hscc
    rcases exists_findNontrivialSCCPair?_eq_some (R := R) hscc with ⟨p, hp⟩
    rw [hnone] at hp
    simp at hp
  · intro hnot
    cases hfind : findNontrivialSCCPair? (R := R) with
    | none =>
        rfl
    | some p =>
        exfalso
        exact hnot (hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some (R := R) hfind)

/-- A nontrivial SCC witness can be repackaged as an explicit sigma pair. -/
private theorem witnessPair_nonempty (h : HasNontrivialSCC R) :
    Nonempty {p : α × α // NontrivialRoundTrip R p.1 p.2} := by
  classical
  rcases h with ⟨a, b, hab⟩
  exact ⟨⟨(a, b), hab⟩⟩

/-- Chosen concrete witness pair for a nontrivial SCC. -/
noncomputable def witnessPair (h : HasNontrivialSCC R) :
    {p : α × α // NontrivialRoundTrip R p.1 p.2} :=
  Classical.choice (witnessPair_nonempty R h)

noncomputable def witnessSrc (h : HasNontrivialSCC R) : α :=
  (witnessPair R h).1.1

noncomputable def witnessDst (h : HasNontrivialSCC R) : α :=
  (witnessPair R h).1.2

theorem witnessSrc_ne_witnessDst (h : HasNontrivialSCC R) :
    witnessSrc R h ≠ witnessDst R h :=
  (witnessPair R h).2.1

theorem reachable_witnessSrc_witnessDst (h : HasNontrivialSCC R) :
    Reachable R (witnessSrc R h) (witnessDst R h) :=
  (witnessPair R h).2.2.1

theorem reachable_witnessDst_witnessSrc (h : HasNontrivialSCC R) :
    Reachable R (witnessDst R h) (witnessSrc R h) :=
  (witnessPair R h).2.2.2

end OperatorKO7.FiniteGraphSCC
