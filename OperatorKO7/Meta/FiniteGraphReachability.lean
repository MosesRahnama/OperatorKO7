import Mathlib

/-!
# Finite Graph Reachability

This module adds a small finite-graph reachability layer for arbitrary directed relations.
For a finite decidable graph, bounded successor-closure over `Fintype.card α` steps already
captures the full reflexive transitive closure. The result is used as a convenience bridge
for the raw-graph SCC barrier theorems: under finite decidable graph assumptions, callers
can work with finite reachability facts instead of supplying explicit `TransGen` witnesses.
-/

namespace OperatorKO7.FiniteGraphReachability

open Relation

variable {α : Type} (R : α → α → Prop) [Fintype α] [DecidableEq α] [DecidableRel R]

/-- One-step successor closure of a finite node set. -/
def succSet (S : Finset α) : Finset α :=
  S ∪ Finset.univ.filter fun v => ∃ u ∈ S, R u v

/-- Bounded reachability iteration from a start node. -/
def reachIter (a : α) : Nat → Finset α
  | 0 => {a}
  | n + 1 => succSet R (reachIter a n)

/-- Finite reachability: successor closure after `Fintype.card α` rounds. -/
def Reachable (a b : α) : Prop :=
  b ∈ reachIter R a (Fintype.card α)

@[simp] theorem mem_succSet {S : Finset α} {v : α} :
    v ∈ succSet R S ↔ v ∈ S ∨ ∃ u ∈ S, R u v := by
  simp [succSet]

theorem subset_succSet (S : Finset α) : S ⊆ succSet R S := by
  intro v hv
  exact (mem_succSet (R := R)).2 <| Or.inl hv

theorem reachIter_mono_succ (a : α) (n : Nat) :
    reachIter R a n ⊆ reachIter R a (n + 1) := by
  simpa [reachIter] using subset_succSet (R := R) (reachIter R a n)

theorem self_mem_reachIter (a : α) : ∀ n, a ∈ reachIter R a n
  | 0 => by simp [reachIter]
  | n + 1 => by
      exact (reachIter_mono_succ (R := R) a n) (self_mem_reachIter a n)

theorem mem_reachIter_sound {a b : α} :
    ∀ {n}, b ∈ reachIter R a n → ReflTransGen R a b
  | 0, hb => by
      simp [reachIter] at hb
      subst hb
      exact ReflTransGen.refl
  | n + 1, hb => by
      rcases (mem_succSet (R := R)).1 (by simpa [reachIter] using hb) with hmem | ⟨u, hu, hub⟩
      · exact mem_reachIter_sound hmem
      · exact ReflTransGen.tail (mem_reachIter_sound hu) hub

theorem reachIter_eq_succ_of_eq_succ_at {a : α} {n k : Nat}
    (h : reachIter R a n = reachIter R a (n + 1)) :
    reachIter R a (n + k) = reachIter R a (n + k + 1) := by
  induction k with
  | zero =>
      simpa using h
  | succ k ih =>
      have hs := congrArg (succSet R) ih
      simpa [Nat.add_assoc, reachIter] using hs

theorem reachIter_eq_succ_of_eq_succ_of_le {a : α} {m n : Nat}
    (h : reachIter R a m = reachIter R a (m + 1)) (hmn : m ≤ n) :
    reachIter R a n = reachIter R a (n + 1) := by
  have hk : n = m + (n - m) := by omega
  rw [hk]
  simpa using reachIter_eq_succ_of_eq_succ_at (R := R) (a := a) (n := m) (k := n - m) h

theorem card_reachIter_ge_of_strict_prefix {a : α} :
    ∀ n,
      (∀ m, m < n → reachIter R a m ≠ reachIter R a (m + 1)) →
      n + 1 ≤ (reachIter R a n).card
  | 0, _ => by simp [reachIter]
  | n + 1, hstrict => by
      have hprefix : ∀ m, m < n → reachIter R a m ≠ reachIter R a (m + 1) := by
        intro m hm
        exact hstrict m (lt_trans hm (Nat.lt_succ_self n))
      have ih := card_reachIter_ge_of_strict_prefix n hprefix
      have hsub : reachIter R a n ⊆ reachIter R a (n + 1) :=
        reachIter_mono_succ (R := R) a n
      have hne : reachIter R a n ≠ reachIter R a (n + 1) :=
        hstrict n (Nat.lt_succ_self n)
      have hssub : reachIter R a n ⊂ reachIter R a (n + 1) := by
        refine ⟨hsub, ?_⟩
        intro hback
        exact hne (Finset.Subset.antisymm hsub hback)
      have hcard : (reachIter R a n).card < (reachIter R a (n + 1)).card :=
        Finset.card_lt_card hssub
      omega

theorem reachIter_card_eq_succ {a : α} :
    reachIter R a (Fintype.card α) = reachIter R a (Fintype.card α + 1) := by
  by_contra hne
  have hprefix : ∀ m, m < Fintype.card α + 1 → reachIter R a m ≠ reachIter R a (m + 1) := by
    intro m hm hmEq
    exact hne <|
      reachIter_eq_succ_of_eq_succ_of_le (R := R) (a := a) hmEq (by omega)
  have hcard :=
    card_reachIter_ge_of_strict_prefix (R := R) (a := a) (n := Fintype.card α + 1) hprefix
  have huniv : (reachIter R a (Fintype.card α + 1)).card ≤ Fintype.card α := by
    exact Finset.card_le_univ (reachIter R a (Fintype.card α + 1))
  omega

theorem closed_reachIter_card {a u v : α}
    (hu : u ∈ reachIter R a (Fintype.card α)) (h : R u v) :
    v ∈ reachIter R a (Fintype.card α) := by
  have hnext : v ∈ reachIter R a (Fintype.card α + 1) := by
    have : v ∈ succSet R (reachIter R a (Fintype.card α)) := (mem_succSet (R := R)).2 <|
      Or.inr ⟨u, hu, h⟩
    simpa [reachIter] using this
  simpa [reachIter_card_eq_succ (R := R) (a := a)] using hnext

theorem mem_reachIter_card_of_reflTransGen {a b : α}
    (h : ReflTransGen R a b) :
    b ∈ reachIter R a (Fintype.card α) := by
  induction h with
  | refl =>
      exact self_mem_reachIter (R := R) a (Fintype.card α)
  | tail hab hbc ih =>
      exact closed_reachIter_card (R := R) ih hbc

theorem reachable_iff_reflTransGen {a b : α} :
    Reachable R a b ↔ ReflTransGen R a b := by
  constructor
  · exact mem_reachIter_sound (R := R)
  · intro h
    exact mem_reachIter_card_of_reflTransGen (R := R) h

theorem reachable_iff_eq_or_transGen {a b : α} :
    Reachable R a b ↔ b = a ∨ TransGen R a b := by
  rw [reachable_iff_reflTransGen (R := R), Relation.reflTransGen_iff_eq_or_transGen]

theorem transGen_of_reachable_of_ne {a b : α}
    (h : Reachable R a b) (hne : a ≠ b) :
    TransGen R a b := by
  rcases (reachable_iff_eq_or_transGen (R := R)).1 h with rfl | htg
  · exact False.elim (hne rfl)
  · exact htg

end OperatorKO7.FiniteGraphReachability
