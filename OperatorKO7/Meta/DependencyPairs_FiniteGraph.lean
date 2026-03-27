import OperatorKO7.Meta.DependencyPairs_Fragment
import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.FiniteGraphSCC

/-!
# Finite Dependency-Pair Graph Interface

This module connects the finite SCC search layer back to the small dependency-pair
fragment. A caller provides only a finite decidable dependency-pair relation. The module
then:

- reuses the finite-SCC search surface (`findNontrivialSCCPair?`),
- repackages a discovered SCC into the standard `SCCCycle` witness, and
- exposes the usual DP-style contradiction theorems directly from that search result.

The goal is not to formalize all dependency-pair processors. The goal is to remove the
remaining SCC witness packaging from finite DP-graph uses of the fragment.
-/

namespace OperatorKO7.DependencyPairsFragment

open OperatorKO7.FiniteGraphReachability
open OperatorKO7.FiniteGraphSCC

/-- A finite decidable dependency-pair graph. -/
structure FiniteDPGraph (α : Type) [Fintype α] [DecidableEq α] where
  Pair : α → α → Prop
  decPair : DecidableRel Pair

attribute [instance] FiniteDPGraph.decPair

namespace FiniteDPGraph

variable {α : Type} [Fintype α] [DecidableEq α] (G : FiniteDPGraph α)

/-- Finite-SCC existence for the dependency-pair relation. -/
abbrev HasNontrivialSCC : Prop :=
  OperatorKO7.FiniteGraphSCC.HasNontrivialSCC G.Pair

/-- Finite search for a distinct SCC pair in the dependency-pair graph. -/
noncomputable def findNontrivialSCCPair? : Option (α × α) :=
  OperatorKO7.FiniteGraphSCC.findNontrivialSCCPair? (R := G.Pair)

theorem hasNontrivialSCC_iff_exists_findNontrivialSCCPair? :
    G.HasNontrivialSCC ↔ ∃ p : α × α, G.findNontrivialSCCPair? = some p := by
  simpa [FiniteDPGraph.findNontrivialSCCPair?, FiniteDPGraph.HasNontrivialSCC] using
    (OperatorKO7.FiniteGraphSCC.hasNontrivialSCC_iff_exists_findNontrivialSCCPair?
      (R := G.Pair))

theorem hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some {p : α × α}
    (h : G.findNontrivialSCCPair? = some p) :
    G.HasNontrivialSCC := by
  simpa [FiniteDPGraph.findNontrivialSCCPair?, FiniteDPGraph.HasNontrivialSCC] using
    (OperatorKO7.FiniteGraphSCC.hasNontrivialSCC_of_findNontrivialSCCPair?_eq_some
      (R := G.Pair) h)

theorem findNontrivialSCCPair?_spec {p : α × α}
    (h : G.findNontrivialSCCPair? = some p) :
    NontrivialRoundTrip G.Pair p.1 p.2 := by
  simpa [FiniteDPGraph.findNontrivialSCCPair?] using
    (OperatorKO7.FiniteGraphSCC.findNontrivialSCCPair?_spec (R := G.Pair) h)

/-- Turn any finite-SCC existence proof into the fragment's standard SCC witness. -/
noncomputable def toSCCCycle (h : G.HasNontrivialSCC) : SCCCycle α where
  Step := G.Pair
  source := witnessSrc G.Pair h
  target := witnessDst G.Pair h
  path :=
    transGen_of_reachable_of_ne (R := G.Pair)
      (reachable_witnessSrc_witnessDst (R := G.Pair) h)
      (witnessSrc_ne_witnessDst (R := G.Pair) h)

/-- A successful finite SCC search immediately yields the standard DP-fragment strict-drop
obligation along the discovered SCC edge path. -/
theorem target_lt_source_of_findNontrivialSCCPair? {m : α → Nat} {p : α × α}
    (hfind : G.findNontrivialSCCPair? = some p)
    (horient : GlobalOrients G.Pair m (· < ·)) :
    m p.2 < m p.1 := by
  have hp : NontrivialRoundTrip G.Pair p.1 p.2 := G.findNontrivialSCCPair?_spec hfind
  exact transGen_drop (R := G.Pair) (m := m) horient
    (transGen_of_reachable_of_ne (R := G.Pair) hp.2.1 hp.1)

/-- Therefore any candidate measure that fails to strictly drop across the discovered SCC
pair cannot globally orient the finite dependency-pair graph. -/
theorem not_globalOrients_of_source_le_target_of_findNontrivialSCCPair?
    {m : α → Nat} {p : α × α}
    (hfind : G.findNontrivialSCCPair? = some p)
    (hge : m p.1 ≤ m p.2) :
    ¬ GlobalOrients G.Pair m (· < ·) := by
  intro horient
  exact Nat.not_lt_of_ge hge (G.target_lt_source_of_findNontrivialSCCPair? hfind horient)

/-- The same contradiction can be phrased through the fragment's standard SCC witness,
without exposing the chosen finite SCC pair explicitly. -/
theorem not_globalOrients_of_source_le_target_of_hasNontrivialSCC
    {m : α → Nat}
    (h : G.HasNontrivialSCC)
    (hge : m (G.toSCCCycle h).source ≤ m (G.toSCCCycle h).target) :
    ¬ GlobalOrients G.Pair m (· < ·) :=
  SCCCycle.not_globalOrients_of_source_le_target (G.toSCCCycle h) hge

end FiniteDPGraph

end OperatorKO7.DependencyPairsFragment
