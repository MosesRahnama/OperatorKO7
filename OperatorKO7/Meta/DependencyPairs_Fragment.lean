import Mathlib.Order.WellFounded

/-!
# Small Dependency-Pair Fragment

This module packages the two dependency-pair mechanisms already used in the
artifact into a small reusable layer:

- rank-based pair problems, where every extracted pair strictly decreases a
  projection rank;
- SCC-style path reasoning, where a finite path in a transformed relation forces
  strict decrease under any global orienter.

This is intentionally narrow. It is not a generic DP library, and it does not
formalize processors, usable rules, or SCC decomposition algorithms.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Orientation of a relation by a measure and strict order. -/
def GlobalOrients {α β : Type} (R : α → α → Prop) (m : α → β)
    (lt : β → β → Prop) : Prop :=
  ∀ {a b : α}, R a b → lt (m b) (m a)

/-- A rank-based dependency-pair problem: every pair strictly decreases the
projection rank. -/
structure DPProjection (α : Type) where
  Pair : α → α → Prop
  rank : α → Nat
  decreases : ∀ {a b : α}, Pair a b → rank b < rank a

namespace DPProjection

/-- Reverse orientation used for well-foundedness arguments on dependency pairs. -/
def Rev {α : Type} (P : DPProjection α) : α → α → Prop :=
  fun a b => P.Pair b a

/-- Reverse pair steps are a subrelation of `<` on the projection rank. -/
lemma rev_sub_rank {α : Type} (P : DPProjection α) :
    Subrelation P.Rev (fun x y => P.rank x < P.rank y) := by
  intro a b h
  exact P.decreases h

/-- Well-foundedness of the reverse pair relation follows from strict decrease of
the projection rank. -/
theorem wfRev {α : Type} (P : DPProjection α) : WellFounded P.Rev := by
  have hrank : WellFounded (fun x y : α => P.rank x < P.rank y) :=
    InvImage.wf (f := P.rank) Nat.lt_wfRel.wf
  exact Subrelation.wf P.rev_sub_rank hrank

end DPProjection

/-- Strict orientation propagates along a nonempty transformed path. -/
theorem transGen_drop {α : Type} {R : α → α → Prop} {m : α → Nat}
    (horient : GlobalOrients R m (· < ·))
    {a b : α} (hpath : Relation.TransGen R a b) : m b < m a := by
  induction hpath with
  | single h =>
      exact horient h
  | tail hab hbc ih =>
      exact Nat.lt_trans (horient hbc) ih

/-- A finite SCC witness in a transformed relation. -/
structure SCCCycle (α : Type) where
  Step : α → α → Prop
  source : α
  target : α
  path : Relation.TransGen Step source target

namespace SCCCycle

/-- Any global orienter must strictly decrease along the SCC witness path. -/
theorem target_lt_source {α : Type} (C : SCCCycle α) {m : α → Nat}
    (horient : GlobalOrients C.Step m (· < ·)) :
    m C.target < m C.source := by
  exact transGen_drop (R := C.Step) (m := m) horient C.path

/-- If a candidate measure does not strictly decrease across the SCC witness,
then it cannot globally orient the transformed relation. -/
theorem not_globalOrients_of_source_le_target {α : Type} (C : SCCCycle α)
    {m : α → Nat} (hge : m C.source ≤ m C.target) :
    ¬ GlobalOrients C.Step m (· < ·) := by
  intro horient
  exact Nat.not_lt_of_ge hge (C.target_lt_source horient)

end SCCCycle

end OperatorKO7.DependencyPairsFragment
