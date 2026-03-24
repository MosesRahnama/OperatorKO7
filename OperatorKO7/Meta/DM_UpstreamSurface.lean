import OperatorKO7.Meta.DM_OrderType_LowerBound

/-!
# Upstream-Staging Surface for the DM Order / Order-Type Package

This module does not claim an actual Mathlib PR. Its purpose is narrower:

- isolate the *general* Dershowitz-Manna multiset-order declarations already
  present in this repository,
- restate them in one small staging surface, and
- give the artifact a concrete upstream-preparation target distinct from the
  KO7-specific calibration theorems.

The candidate surface collected here is independent of the KO7 kernel itself:

- `dmOrdEmbed` on `Multiset Nat`
- order reflection / strict monotonicity with respect to `DM`
- the upper bound `dmOrdEmbed m < ω^ω`
- the exact order-type package `dm_order_type_omega_omega`

What is still missing relative to the original review request is an actual
upstream Mathlib pull request. This file is therefore an upstream-prep artifact,
not an upstream contribution by itself.
-/

namespace OperatorKO7.MetaDMUpstream

open Ordinal
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM

/-- Compact statement of the general DM candidate surface that is plausibly
upstreamable to Mathlib after namespace / dependency cleanup. -/
def DMOrderTypeUpstreamSurface : Prop :=
  (∀ m₁ m₂ : Multiset Nat, MetaCM.DM m₁ m₂ ↔ dmOrdEmbed m₁ < dmOrdEmbed m₂) ∧
  (∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal)) ∧
  (∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmOrdEmbed m = α)

/-- The current repository already proves the full general-order surface. -/
theorem dmOrderTypeUpstreamSurface_holds : DMOrderTypeUpstreamSurface :=
  dm_order_type_omega_omega

/-- Forward strict monotonicity, exposed under the staging namespace. -/
theorem dmOrder_strictMono {m₁ m₂ : Multiset Nat} (hDM : DM m₁ m₂) :
    dmOrdEmbed m₁ < dmOrdEmbed m₂ :=
  dmOrdEmbed_strictMono hDM

/-- Order reflection, exposed under the staging namespace. -/
theorem dmOrder_reflects {m₁ m₂ : Multiset Nat}
    (hlt : dmOrdEmbed m₁ < dmOrdEmbed m₂) :
    DM m₁ m₂ :=
  dmOrdEmbed_reflects hlt

/-- The general upper bound below `ω^ω`, exposed under the staging namespace. -/
theorem dmOrder_lt_opow_omega (m : Multiset Nat) :
    dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal) :=
  dmOrdEmbed_lt_opow_omega m

/-- Exact order-type package, exposed under the staging namespace. -/
theorem dmOrder_exact_type :
    (∀ m₁ m₂ : Multiset Nat, MetaCM.DM m₁ m₂ ↔ dmOrdEmbed m₁ < dmOrdEmbed m₂) ∧
    (∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal)) ∧
    (∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmOrdEmbed m = α) :=
  dm_order_type_omega_omega

end OperatorKO7.MetaDMUpstream
