import OperatorKO7.Meta.Termination_KO7
import OperatorKO7.Meta.ComputableMeasure
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna

/-!
# DM/MPO Orientation Helpers (safe wrappers)

This module provides small, composable wrappers around the Dershowitz–Manna
multiset ordering lemmas used throughout the termination development.

They are deliberately minimal and rely on existing, proven lemmas from the
`MetaSN_DM` toolkit. No kernel rules are changed. No new axioms are introduced.

Use these helpers to keep orientation proofs concise and robust.
-/

namespace OperatorKO7.MetaOrientation

open Multiset
open MetaSN_DM
open OperatorKO7 Trace
open OperatorKO7.MetaCM

/--
Right-add orientation: if `Y ≠ 0`, then `X < X + Y` in the DM order.

This is a thin wrapper around `MetaSN_DM.dm_lt_add_of_ne_zero'` with the
arguments placed for ergonomic use.
-/
lemma dm_add_right_of_ne_zero {X Y : Multiset ℕ} (hY : Y ≠ 0) : OperatorKO7.MetaCM.DM X (X + Y) := by
  simpa using MetaSN_DM.dm_lt_add_of_ne_zero' X Y hY

/--
Left-add orientation: if `X ≠ 0`, then `Y < X + Y` in the DM order.

This follows from commutativity of multiset addition and the right-add lemma.
-/
lemma dm_add_left_of_ne_zero {X Y : Multiset ℕ} (hX : X ≠ 0) : OperatorKO7.MetaCM.DM Y (X + Y) := by
  simpa [add_comm] using MetaSN_DM.dm_lt_add_of_ne_zero' Y X hX

/-- DM drop on κᴹ for rec_zero (re-export for ergonomics). -/
lemma dm_drop_rec_zero (b s : Trace) :
    OperatorKO7.MetaCM.DM (MetaSN_DM.kappaM b) (MetaSN_DM.kappaM (recΔ b s void)) := by
  simpa [OperatorKO7.MetaCM.DM] using MetaSN_DM.dm_drop_R_rec_zero b s

/-- If X ≠ 0 then X ∪ X ≠ 0 (re-export). -/
lemma union_self_ne_zero_of_ne_zero {X : Multiset ℕ} (h : X ≠ 0) :
    X ∪ X ≠ (0 : Multiset ℕ) := by
  simpa using MetaSN_DM.union_self_ne_zero_of_ne_zero h

end OperatorKO7.MetaOrientation
