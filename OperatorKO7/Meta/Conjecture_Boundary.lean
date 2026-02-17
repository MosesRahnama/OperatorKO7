import OperatorKO7.Meta.Impossibility_Lemmas
import OperatorKO7.Meta.Operational_Incompleteness

/-!
# Conjecture Boundary (Theorem-Level No-Go Statements)

This module collects theorem-level barriers that are already justified by the
current KO7 artifact. It does **not** claim a proof of full-system
non-termination, and it does **not** upgrade the paper conjecture to a theorem.

The purpose is narrower:
- record explicit "no-go" theorems for concrete internal method families;
- keep these boundaries importable from one place for audit/review.
-/

namespace OperatorKO7.MetaConjectureBoundary

open OperatorKO7 Trace
open OperatorKO7.Impossibility

/-! ## Global-orientation interface (full kernel Step) -/

/-- A measure/order pair globally orients the full kernel `Step`. -/
def GlobalOrients {α : Type} (m : Trace → α) (lt : α → α → Prop) : Prop :=
  ∀ {a b}, Step a b → lt (m b) (m a)

/-! ## Additive / Lex barriers -/

/-- No fixed additive bump on `kappa` can orient `rec_succ` uniformly. -/
theorem no_fixed_kappa_plus_k (k : Nat) :
    ¬ (∀ (b s n : Trace),
      FailedMeasures.kappa (app s (recΔ b s n)) + k <
      FailedMeasures.kappa (recΔ b s (delta n)) + k) :=
  FailedMeasures.kappa_plus_k_fails k

/-- The simple 2-component lex witness `(kappa, mu)` fails on KO7. -/
theorem no_simple_lex_witness :
    ¬ (∀ (b s n : Trace),
      Prod.Lex (· < ·) (· < ·)
        (FailedMeasures.kappa (app s (recΔ b s n)),
         FailedMeasures.mu (app s (recΔ b s n)))
        (FailedMeasures.kappa (recΔ b s (delta n)),
         FailedMeasures.mu (recΔ b s (delta n)))) :=
  FailedMeasures.simple_lex_fails

/-- Additive size cannot strictly decrease across all `rec_succ` instances. -/
theorem no_additive_strict_drop_rec_succ :
    ¬ (∀ (b s n : Trace),
      UncheckedRecursionFailure.simpleSize (app s (recΔ b s n)) <
      UncheckedRecursionFailure.simpleSize (recΔ b s (delta n))) := by
  intro h
  have hlt := h void void void
  have hge :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  exact Nat.not_lt_of_ge hge hlt

/-! ## Strengthened full-step no-go theorems -/

/-- No fixed additive bump can globally orient full `Step`. -/
theorem no_global_step_orientation_kappa_plus_k (k : Nat) :
    ¬ GlobalOrients (fun t => FailedMeasures.kappa t + k) (· < ·) := by
  intro h
  apply no_fixed_kappa_plus_k k
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Plain structural depth (`kappa`) cannot globally orient full `Step`. -/
theorem no_global_step_orientation_kappa :
    ¬ GlobalOrients FailedMeasures.kappa (· < ·) := by
  intro h
  apply no_fixed_kappa_plus_k 0
  intro b s n
  have hlt : FailedMeasures.kappa (app s (recΔ b s n)) <
      FailedMeasures.kappa (recΔ b s (delta n)) :=
    h (Step.R_rec_succ b s n)
  simp at hlt

/-- The simple lex witness `(kappa, mu)` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simple_lex :
    ¬ GlobalOrients
      (fun t => (FailedMeasures.kappa t, FailedMeasures.mu t))
      (Prod.Lex (· < ·) (· < ·)) := by
  intro h
  apply no_simple_lex_witness
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Additive `simpleSize` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simpleSize :
    ¬ GlobalOrients UncheckedRecursionFailure.simpleSize (· < ·) := by
  intro h
  apply no_additive_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-! ## Flag-only barrier -/

/-- A single top-level flag cannot globally orient full `Step`. -/
theorem no_global_flag_only_orientation :
    ¬ (∀ a b : Trace, Step a b →
      FlagFailure.deltaFlagTop b < FlagFailure.deltaFlagTop a) := by
  intro h
  let t : Trace := delta void
  have hstep : Step (merge void t) t := Step.R_merge_void_left t
  have hlt : FlagFailure.deltaFlagTop t < FlagFailure.deltaFlagTop (merge void t) :=
    h _ _ hstep
  simp [FlagFailure.deltaFlagTop, t] at hlt

/-! ## Constellation / structural hybrid barrier -/

/-- Constellation-size cannot strictly decrease on all `rec_succ` instances. -/
theorem no_constellation_strict_drop_rec_succ :
    ¬ (∀ (b s n : Trace),
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (app s (recΔ b s n))) <
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (recΔ b s (delta n)))) := by
  intro h
  have hlt := h void void void
  have hs :
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (void : Trace)) ≥ 1 := by
    simp [ConstellationFailure.constellationSize, ConstellationFailure.toConstellation]
  have hge :=
    ConstellationFailure.constellation_size_not_decreasing void void void hs
  exact Nat.not_lt_of_ge hge hlt

/-- Constellation-size cannot globally orient full `Step`. -/
theorem no_global_step_orientation_constellation :
    ¬ GlobalOrients
      (fun t =>
        ConstellationFailure.constellationSize
          (ConstellationFailure.toConstellation t))
      (· < ·) := by
  intro h
  apply no_constellation_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Strictly monotone post-processing cannot rescue additive `simpleSize` on full `Step`. -/
theorem no_global_step_orientation_simpleSize_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ¬ GlobalOrients
      (fun t => f (UncheckedRecursionFailure.simpleSize t))
      (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta void)) (app void (recΔ void void void)) :=
    Step.R_rec_succ void void void
  have hlt :
      f (UncheckedRecursionFailure.simpleSize (app void (recΔ void void void))) <
      f (UncheckedRecursionFailure.simpleSize (recΔ void void (delta void))) :=
    h hstep
  have hge :
      UncheckedRecursionFailure.simpleSize (app void (recΔ void void void)) ≥
      UncheckedRecursionFailure.simpleSize (recΔ void void (delta void)) :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  have hmono :
      f (UncheckedRecursionFailure.simpleSize (recΔ void void (delta void))) ≤
      f (UncheckedRecursionFailure.simpleSize (app void (recΔ void void void))) :=
    hf.monotone hge
  exact Nat.not_lt_of_ge hmono hlt

/-! ## Bridge wrappers to `OpIncomp.InternallyDefinableMeasure` -/

/-- Any internal witness must include the explicit duplication non-drop barrier (r4). -/
theorem internal_measure_records_duplication_barrier
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    (x y : OperatorKO7.OpIncomp.Term) :
    ¬ OperatorKO7.OpIncomp.size (OperatorKO7.OpIncomp.R4_after x y) <
      OperatorKO7.OpIncomp.size (OperatorKO7.OpIncomp.R4_before x y) :=
  M.dup_additive_nodrop_r4 x y

/-- Any internal witness must provide per-piece orientation for every rule instance. -/
theorem internal_measure_requires_per_piece_lt
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    {l r : OperatorKO7.OpIncomp.Term}
    (hr : OperatorKO7.OpIncomp.Rule l r)
    {t : OperatorKO7.OpIncomp.Term}
    (ht : t ∈ OperatorKO7.OpIncomp.rhsPiecesLHS l) :
    M.base t l :=
  M.per_piece_base_lt hr t ht

/-- Exposes the lex/orientation gate encoded in `InternallyDefinableMeasure`. -/
theorem internal_measure_lex_gate
    (M : OperatorKO7.OpIncomp.InternallyDefinableMeasure)
    {l r : OperatorKO7.OpIncomp.Term}
    (hr : OperatorKO7.OpIncomp.Rule l r) :
    (M.flag r = false ∧ M.flag l = true) ∨
      (∃ t, t ∈ OperatorKO7.OpIncomp.rhsPiecesLHS l ∧ M.base t l) ∨
      M.base r l :=
  M.lex_ok hr

/-! ## Full-step witness (duplication branch is present in kernel Step) -/

/-- The unrestricted kernel `Step` contains the duplication branch explicitly. -/
theorem full_step_has_rec_succ_instance :
    ∃ b s n, Step (recΔ b s (delta n)) (app s (recΔ b s n)) :=
  UncheckedRecursionFailure.full_step_permits_barrier

end OperatorKO7.MetaConjectureBoundary
