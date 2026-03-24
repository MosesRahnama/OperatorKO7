import OperatorKO7.Meta.SafeStep_Ctx
import OperatorKO7.Meta.NormalizeSafe_LowerBound
import OperatorKO7.Meta.ComputableMeasure
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal

/-!
# Contextual copy-budget exploration for tighter `SafeStepCtx` complexity

This file is exploratory in origin. Its positive outcome is now re-exported
indirectly through `Meta/SafeStepCtx_Complexity_Exponential.lean`, while the
negative-search infrastructure remains here. It isolates the first binary test
for a tighter contextual potential:

- define a purely syntactic `copyBudget`
- prove it is non-increasing under `SafeStep` and `SafeStepCtx`

This does **not** yet solve the contextual complexity problem. It only establishes
that `copyBudget` is a viable control coordinate for a future lexicographic or
vector-valued potential.
-/

open OperatorKO7 Trace
open OperatorKO7.MetaCM

namespace MetaSN_KO7

/-- A purely syntactic upper budget for future `delta`-driven copying. -/
@[simp] def copyBudget : Trace → Nat
| void            => 0
| delta t         => copyBudget t + 1
| integrate t     => copyBudget t
| merge a b       => max (copyBudget a) (copyBudget b)
| app a b         => max (copyBudget a) (copyBudget b)
| recΔ b s n      => max (copyBudget b) (max (copyBudget s) (copyBudget n))
| eqW a b         => max (copyBudget a) (copyBudget b)

/-- A localized budget that only records copy pressure coming from recursor counters. -/
@[simp] def counterBudget : Trace → Nat
| void            => 0
| delta t         => counterBudget t
| integrate t     => counterBudget t
| merge a b       => max (counterBudget a) (counterBudget b)
| app a b         => max (counterBudget a) (counterBudget b)
| recΔ b s n      => max (copyBudget n)
    (max (counterBudget b) (max (counterBudget s) (counterBudget n)))
| eqW a b         => max (counterBudget a) (counterBudget b)

/-- A naive multiplicity-sensitive copy-pressure coordinate. This counts both subtree
shape and repeated occurrences, so it is a natural first attempt beyond max-based budgets. -/
@[simp] def copyMass : Trace → Nat
| void            => 0
| delta t         => copyMass t + 1
| integrate t     => copyMass t
| merge a b       => copyMass a + copyMass b
| app a b         => copyMass a + copyMass b
| recΔ b s n      => copyMass b + copyMass s + copyMass n + copyBudget n
| eqW a b         => copyMass a + copyMass b

/-- A safe root step never increases `copyBudget`. -/
theorem copyBudget_mono_safe : ∀ {a b : Trace}, SafeStep a b → copyBudget b ≤ copyBudget a
| _, _, SafeStep.R_int_delta t => by
    simp [copyBudget]
| _, _, SafeStep.R_merge_void_left t _ => by
    simp [copyBudget]
| _, _, SafeStep.R_merge_void_right t _ => by
    simp [copyBudget]
| _, _, SafeStep.R_merge_cancel t _ _ => by
    simp [copyBudget]
| _, _, SafeStep.R_rec_zero b s _ => by
    simp [copyBudget]
| _, _, SafeStep.R_rec_succ b s n => by
    have hs : max (copyBudget s) (copyBudget n) ≤ max (copyBudget s) (copyBudget n + 1) := by
      exact max_le_max le_rfl (Nat.le_succ _)
    have hb :
        max (copyBudget b) (max (copyBudget s) (copyBudget n)) ≤
          max (copyBudget b) (max (copyBudget s) (copyBudget n + 1)) := by
      exact max_le_max le_rfl hs
    simpa [copyBudget, max_assoc, max_left_comm, max_comm] using hb
| _, _, SafeStep.R_eq_refl a _ => by
    simp [copyBudget]
| _, _, SafeStep.R_eq_diff a b _ => by
    simp [copyBudget]

/-- The `rec_succ` root step drops the syntactic copy budget by at most one. -/
theorem copyBudget_rec_succ_shape (b s n : Trace) :
    copyBudget (app s (recΔ b s n)) ≤ copyBudget (recΔ b s (delta n)) := by
  exact copyBudget_mono_safe (SafeStep.R_rec_succ b s n)

/-- Context closure preserves the non-increase of `copyBudget`. -/
theorem copyBudget_mono_safeStepCtx :
    ∀ {a b : Trace}, SafeStepCtx a b → copyBudget b ≤ copyBudget a
| _, _, SafeStepCtx.root hs => copyBudget_mono_safe hs
| _, _, SafeStepCtx.integrate h => by
    simpa [copyBudget] using copyBudget_mono_safeStepCtx h
| _, _, SafeStepCtx.mergeL (a := a) (a' := a') (b := b) h => by
    change max (copyBudget a') (copyBudget b) ≤ max (copyBudget a) (copyBudget b)
    exact max_le_max (copyBudget_mono_safeStepCtx h) le_rfl
| _, _, SafeStepCtx.mergeR (a := a) (b := b) (b' := b') h => by
    change max (copyBudget a) (copyBudget b') ≤ max (copyBudget a) (copyBudget b)
    exact max_le_max le_rfl (copyBudget_mono_safeStepCtx h)
| _, _, SafeStepCtx.appL (a := a) (a' := a') (b := b) h => by
    change max (copyBudget a') (copyBudget b) ≤ max (copyBudget a) (copyBudget b)
    exact max_le_max (copyBudget_mono_safeStepCtx h) le_rfl
| _, _, SafeStepCtx.appR (a := a) (b := b) (b' := b') h => by
    change max (copyBudget a) (copyBudget b') ≤ max (copyBudget a) (copyBudget b)
    exact max_le_max le_rfl (copyBudget_mono_safeStepCtx h)
| _, _, SafeStepCtx.recB (b := b) (b' := b') (s := s) (n := n) h => by
    change max (copyBudget b') (max (copyBudget s) (copyBudget n)) ≤
      max (copyBudget b) (max (copyBudget s) (copyBudget n))
    exact max_le_max (copyBudget_mono_safeStepCtx h) le_rfl
| _, _, SafeStepCtx.recS (b := b) (s := s) (s' := s') (n := n) h => by
    change max (copyBudget b) (max (copyBudget s') (copyBudget n)) ≤
      max (copyBudget b) (max (copyBudget s) (copyBudget n))
    exact max_le_max le_rfl (max_le_max (copyBudget_mono_safeStepCtx h) le_rfl)
| _, _, SafeStepCtx.recN (b := b) (s := s) (n := n) (n' := n') h => by
    change max (copyBudget b) (max (copyBudget s) (copyBudget n')) ≤
      max (copyBudget b) (max (copyBudget s) (copyBudget n))
    exact max_le_max le_rfl (max_le_max le_rfl (copyBudget_mono_safeStepCtx h))

/-- A safe root step never increases the localized recursor-counter budget. -/
theorem counterBudget_mono_safe : ∀ {a b : Trace}, SafeStep a b → counterBudget b ≤ counterBudget a
| _, _, SafeStep.R_int_delta t => by
    simp [counterBudget]
| _, _, SafeStep.R_merge_void_left t _ => by
    simp [counterBudget]
| _, _, SafeStep.R_merge_void_right t _ => by
    simp [counterBudget]
| _, _, SafeStep.R_merge_cancel t _ _ => by
    simp [counterBudget]
| _, _, SafeStep.R_rec_zero b s _ => by
    simp [counterBudget]
| _, _, SafeStep.R_rec_succ b s n => by
    have hsub :
        max (copyBudget n)
            (max (counterBudget b) (max (counterBudget s) (counterBudget n))) ≤
          max (copyBudget n + 1)
            (max (counterBudget b) (max (counterBudget s) (counterBudget n))) := by
      exact max_le_max (Nat.le_succ _) le_rfl
    simpa [counterBudget, copyBudget, max_assoc, max_left_comm, max_comm] using hsub
| _, _, SafeStep.R_eq_refl a _ => by
    simp [counterBudget]
| _, _, SafeStep.R_eq_diff a b _ => by
    simp [counterBudget]

/-- Context closure preserves the non-increase of the localized recursor-counter budget. -/
theorem counterBudget_mono_safeStepCtx :
    ∀ {a b : Trace}, SafeStepCtx a b → counterBudget b ≤ counterBudget a
| _, _, SafeStepCtx.root hs => counterBudget_mono_safe hs
| _, _, SafeStepCtx.integrate h => by
    simpa [counterBudget] using counterBudget_mono_safeStepCtx h
| _, _, SafeStepCtx.mergeL (a := a) (a' := a') (b := b) h => by
    change max (counterBudget a') (counterBudget b) ≤ max (counterBudget a) (counterBudget b)
    exact max_le_max (counterBudget_mono_safeStepCtx h) le_rfl
| _, _, SafeStepCtx.mergeR (a := a) (b := b) (b' := b') h => by
    change max (counterBudget a) (counterBudget b') ≤ max (counterBudget a) (counterBudget b)
    exact max_le_max le_rfl (counterBudget_mono_safeStepCtx h)
| _, _, SafeStepCtx.appL (a := a) (a' := a') (b := b) h => by
    change max (counterBudget a') (counterBudget b) ≤ max (counterBudget a) (counterBudget b)
    exact max_le_max (counterBudget_mono_safeStepCtx h) le_rfl
| _, _, SafeStepCtx.appR (a := a) (b := b) (b' := b') h => by
    change max (counterBudget a) (counterBudget b') ≤ max (counterBudget a) (counterBudget b)
    exact max_le_max le_rfl (counterBudget_mono_safeStepCtx h)
| _, _, SafeStepCtx.recB (b := b) (b' := b') (s := s) (n := n) h => by
    change max (copyBudget n) (max (counterBudget b') (max (counterBudget s) (counterBudget n))) ≤
      max (copyBudget n) (max (counterBudget b) (max (counterBudget s) (counterBudget n)))
    exact max_le_max le_rfl (max_le_max (counterBudget_mono_safeStepCtx h) le_rfl)
| _, _, SafeStepCtx.recS (b := b) (s := s) (s' := s') (n := n) h => by
    change max (copyBudget n) (max (counterBudget b) (max (counterBudget s') (counterBudget n))) ≤
      max (copyBudget n) (max (counterBudget b) (max (counterBudget s) (counterBudget n)))
    exact max_le_max le_rfl (max_le_max le_rfl (max_le_max (counterBudget_mono_safeStepCtx h) le_rfl))
| _, _, SafeStepCtx.recN (b := b) (s := s) (n := n) (n' := n') h => by
    have hcopy : copyBudget n' ≤ copyBudget n := copyBudget_mono_safeStepCtx h
    have hctr : counterBudget n' ≤ counterBudget n := counterBudget_mono_safeStepCtx h
    change max (copyBudget n') (max (counterBudget b) (max (counterBudget s) (counterBudget n'))) ≤
      max (copyBudget n) (max (counterBudget b) (max (counterBudget s) (counterBudget n)))
    exact max_le_max hcopy (max_le_max le_rfl (max_le_max le_rfl hctr))

/-- A `recN` example where whole-term root normalization cost increases under a contextual step. -/
@[simp] def recNRootCostSrc : Trace := recΔ void void (merge void void)

/-- Target of the `recN` root-cost counterexample. -/
@[simp] def recNRootCostTgt : Trace := recΔ void void void

theorem recNRootCost_step : SafeStepCtx recNRootCostSrc recNRootCostTgt := by
  refine SafeStepCtx.recN ?_
  refine SafeStepCtx.root ?_
  simpa using (SafeStep.R_merge_void_left void rfl)

theorem recNRootCost_copyBudget_eq :
    copyBudget recNRootCostTgt = copyBudget recNRootCostSrc := by
  simp [recNRootCostSrc, recNRootCostTgt, copyBudget]

theorem recNRootCost_normalizeSafeSteps_src :
    normalizeSafeSteps recNRootCostSrc = 0 := by
  rw [normalizeSafeSteps_eq]
  simp [recNRootCostSrc, safeStepWitness?]

theorem recNRootCost_normalizeSafeSteps_tgt :
    normalizeSafeSteps recNRootCostTgt = 1 := by
  rw [normalizeSafeSteps_eq]
  simp [recNRootCostTgt, safeStepWitness?, normalizeSafeSteps_void]

/-- `normalizeSafeSteps` is not monotone under `SafeStepCtx`, so it cannot be used directly
as the second coordinate of a contextual lexicographic measure. -/
theorem not_normalizeSafeSteps_mono_safeStepCtx :
    ¬ ∀ {a b : Trace}, SafeStepCtx a b → normalizeSafeSteps b ≤ normalizeSafeSteps a := by
  intro hmono
  have h := hmono recNRootCost_step
  rw [recNRootCost_normalizeSafeSteps_src, recNRootCost_normalizeSafeSteps_tgt] at h
  omega

/-- A flat-`copyBudget` `rec_succ` example. -/
@[simp] def recSuccFlatTauSrc : Trace := recΔ (delta void) void (delta void)

/-- Target of the flat-`copyBudget` `rec_succ` example. -/
@[simp] def recSuccFlatTauTgt : Trace := app void (recΔ (delta void) void void)

theorem recSuccFlatTau_step : SafeStep recSuccFlatTauSrc recSuccFlatTauTgt := by
  simpa [recSuccFlatTauSrc, recSuccFlatTauTgt] using
    (SafeStep.R_rec_succ (delta void) void void)

theorem recSuccFlatTau_copyBudget_eq :
    copyBudget recSuccFlatTauTgt = copyBudget recSuccFlatTauSrc := by
  simp [recSuccFlatTauSrc, recSuccFlatTauTgt, copyBudget]

theorem recSuccFlatTau_tau_increases :
    tau recSuccFlatTauSrc < tau recSuccFlatTauTgt := by
  simp [recSuccFlatTauSrc, recSuccFlatTauTgt, tau]

/-- `tau` cannot serve as the companion coordinate on the flat-`copyBudget` `rec_succ` cases. -/
theorem not_tau_mono_on_flat_copyBudget_safe :
    ¬ ∀ {a b : Trace}, SafeStep a b → copyBudget b = copyBudget a → tau b ≤ tau a := by
  intro hmono
  have h := hmono recSuccFlatTau_step recSuccFlatTau_copyBudget_eq
  exact Nat.not_le_of_lt recSuccFlatTau_tau_increases h

/-- The active counter dominates all recursive substructure. -/
def recCounterDominates (b s n : Trace) : Prop :=
  max (counterBudget b) (max (counterBudget s) (counterBudget n)) ≤ copyBudget n

/-- Under dominance of the active counter, the localized recursor-counter budget drops on `rec_succ`. -/
theorem counterBudget_rec_succ_strict_of_dom (b s n : Trace)
    (hdom : recCounterDominates b s n) :
    counterBudget (app s (recΔ b s n)) < counterBudget (recΔ b s (delta n)) := by
  have hsrc :
      counterBudget (recΔ b s (delta n)) = copyBudget n + 1 := by
    simp [counterBudget, copyBudget, recCounterDominates] at hdom ⊢
    omega
  have htgt :
      counterBudget (app s (recΔ b s n)) = copyBudget n := by
    simp [counterBudget, recCounterDominates] at hdom ⊢
    omega
  rw [hsrc, htgt]
  omega

/-- In the earlier base-dominated flat-`copyBudget` example, the localized counter budget does drop. -/
theorem recSuccFlatTau_counterBudget_drops :
    counterBudget recSuccFlatTauTgt < counterBudget recSuccFlatTauSrc := by
  simp [recSuccFlatTauSrc, recSuccFlatTauTgt, counterBudget, copyBudget]

/-- A payload-recursive example where the localized counter budget also stays flat. -/
@[simp] def recSuccPayloadFlatSrc : Trace :=
  recΔ void (recΔ void void (delta void)) (delta void)

@[simp] def recSuccPayloadFlatTgt : Trace :=
  app (recΔ void void (delta void)) (recΔ void (recΔ void void (delta void)) void)

theorem recSuccPayloadFlat_step : SafeStep recSuccPayloadFlatSrc recSuccPayloadFlatTgt := by
  simpa [recSuccPayloadFlatSrc, recSuccPayloadFlatTgt] using
    (SafeStep.R_rec_succ void (recΔ void void (delta void)) void)

theorem recSuccPayloadFlat_copyBudget_eq :
    copyBudget recSuccPayloadFlatTgt = copyBudget recSuccPayloadFlatSrc := by
  simp [recSuccPayloadFlatSrc, recSuccPayloadFlatTgt, copyBudget]

theorem recSuccPayloadFlat_counterBudget_eq :
    counterBudget recSuccPayloadFlatTgt = counterBudget recSuccPayloadFlatSrc := by
  simp [recSuccPayloadFlatSrc, recSuccPayloadFlatTgt, counterBudget, copyBudget]

theorem recSuccPayloadFlat_tau_increases :
    tau recSuccPayloadFlatSrc < tau recSuccPayloadFlatTgt := by
  simp [recSuccPayloadFlatSrc, recSuccPayloadFlatTgt, tau]

/-- The simple lexicographic pair `(copyBudget, counterBudget)` still fails on the
payload-recursive `rec_succ` obstruction. -/
theorem not_copyBudget_counterBudget_lex_safe :
    ¬ ∀ {a b : Trace}, SafeStep a b →
      copyBudget b < copyBudget a ∨
        (copyBudget b = copyBudget a ∧ counterBudget b < counterBudget a) := by
  intro hlex
  have h := hlex recSuccPayloadFlat_step
  have hcb : copyBudget recSuccPayloadFlatTgt = copyBudget recSuccPayloadFlatSrc :=
    recSuccPayloadFlat_copyBudget_eq
  have hctr : counterBudget recSuccPayloadFlatTgt = counterBudget recSuccPayloadFlatSrc :=
    recSuccPayloadFlat_counterBudget_eq
  rcases h with hdrop | ⟨heq, hdrop⟩
  · rw [hcb] at hdrop
    exact Nat.lt_irrefl _ hdrop
  · rw [hcb] at heq
    rw [hctr] at hdrop
    exact Nat.lt_irrefl _ hdrop

/-- Even the obvious lexicographic triple `(copyBudget, counterBudget, tau)` is ruled out
by the payload-recursive `rec_succ` case. -/
theorem not_copyBudget_counterBudget_tau_lex_safe :
    ¬ ∀ {a b : Trace}, SafeStep a b →
      copyBudget b < copyBudget a ∨
        (copyBudget b = copyBudget a ∧
          (counterBudget b < counterBudget a ∨
            (counterBudget b = counterBudget a ∧ tau b < tau a))) := by
  intro hlex
  have h := hlex recSuccPayloadFlat_step
  have hcb : copyBudget recSuccPayloadFlatTgt = copyBudget recSuccPayloadFlatSrc :=
    recSuccPayloadFlat_copyBudget_eq
  have hctr : counterBudget recSuccPayloadFlatTgt = counterBudget recSuccPayloadFlatSrc :=
    recSuccPayloadFlat_counterBudget_eq
  rcases h with hdrop | ⟨heqcb, hrest⟩
  · rw [hcb] at hdrop
    exact Nat.lt_irrefl _ hdrop
  · rcases hrest with hdrop | ⟨heqctr, htaudrop⟩
    · rw [hctr] at hdrop
      exact Nat.lt_irrefl _ hdrop
    · have htauup := recSuccPayloadFlat_tau_increases
      exact Nat.lt_asymm htaudrop htauup

/-- A deeper payload where naive multiplicity-sensitive copy counting grows under `rec_succ`. -/
@[simp] def recSuccMassBadPayload : Trace :=
  recΔ void (recΔ void void (delta void)) (delta void)

@[simp] def recSuccMassBadSrc : Trace :=
  recΔ void recSuccMassBadPayload (delta void)

@[simp] def recSuccMassBadTgt : Trace :=
  app recSuccMassBadPayload (recΔ void recSuccMassBadPayload void)

theorem recSuccMassBad_step : SafeStep recSuccMassBadSrc recSuccMassBadTgt := by
  simpa [recSuccMassBadSrc, recSuccMassBadTgt, recSuccMassBadPayload] using
    (SafeStep.R_rec_succ void recSuccMassBadPayload void)

theorem recSuccMassBad_copyMass_increases :
    copyMass recSuccMassBadSrc < copyMass recSuccMassBadTgt := by
  simp [recSuccMassBadSrc, recSuccMassBadTgt, recSuccMassBadPayload, copyMass, copyBudget]

/-- The naive multiplicity-sensitive sum is not even root-monotone, so it cannot be used
as a contextual companion coordinate. -/
theorem not_copyMass_mono_safe :
    ¬ ∀ {a b : Trace}, SafeStep a b → copyMass b ≤ copyMass a := by
  intro hmono
  have h := hmono recSuccMassBad_step
  exact Nat.not_le_of_lt recSuccMassBad_copyMass_increases h

/-- A small DSL for monotone arithmetic expressions over the currently explored
contextual coordinates. -/
inductive CoordExpr where
| const : Nat → CoordExpr
| cb : CoordExpr
| ctr : CoordExpr
| tau : CoordExpr
| mass : CoordExpr
| succ : CoordExpr → CoordExpr
| add : CoordExpr → CoordExpr → CoordExpr
| max : CoordExpr → CoordExpr → CoordExpr
deriving Repr, DecidableEq

/-- Evaluate a coordinate expression on a trace. -/
@[simp] def CoordExpr.eval : CoordExpr → Trace → Nat
| .const n, _ => n
| .cb, t => copyBudget t
| .ctr, t => counterBudget t
| .tau, t => OperatorKO7.MetaCM.tau t
| .mass, t => copyMass t
| .succ e, t => Nat.succ (e.eval t)
| .add e₁ e₂, t => e₁.eval t + e₂.eval t
| .max e₁ e₂, t => Nat.max (e₁.eval t) (e₂.eval t)

theorem recSuccPayloadFlat_copyMass_eq :
    copyMass recSuccPayloadFlatTgt = copyMass recSuccPayloadFlatSrc := by
  simp [recSuccPayloadFlatSrc, recSuccPayloadFlatTgt, copyMass, copyBudget]

/-- Every monotone arithmetic expression over the current coordinates is non-decreasing
on the payload-recursive `rec_succ` obstruction. -/
theorem coordExpr_payloadFlat_nondec (e : CoordExpr) :
    e.eval recSuccPayloadFlatSrc ≤ e.eval recSuccPayloadFlatTgt := by
  induction e with
  | const n =>
      simp [CoordExpr.eval]
  | cb =>
      rw [CoordExpr.eval, CoordExpr.eval, recSuccPayloadFlat_copyBudget_eq]
  | ctr =>
      rw [CoordExpr.eval, CoordExpr.eval, recSuccPayloadFlat_counterBudget_eq]
  | tau =>
      exact Nat.le_of_lt recSuccPayloadFlat_tau_increases
  | mass =>
      rw [CoordExpr.eval, CoordExpr.eval, recSuccPayloadFlat_copyMass_eq]
  | succ e ih =>
      simpa [CoordExpr.eval] using Nat.succ_le_succ ih
  | add e₁ e₂ ih₁ ih₂ =>
      simpa [CoordExpr.eval] using Nat.add_le_add ih₁ ih₂
  | max e₁ e₂ ih₁ ih₂ =>
      simpa [CoordExpr.eval] using max_le_max ih₁ ih₂

/-- Stack-style lex certification relation for a list of coordinate expressions. -/
def CoordExprStackCertifies (es : List CoordExpr) (a b : Trace) : Prop :=
  ∃ pre e post,
    es = pre ++ e :: post ∧
    (∀ e' ∈ pre, e'.eval a = e'.eval b) ∧
    e.eval b < e.eval a

/-- No lexicographic stack built from the current monotone arithmetic expression class
can certify the payload-recursive `rec_succ` obstruction. -/
theorem not_coordExprStackCertifies_payloadFlat (es : List CoordExpr) :
    ¬ CoordExprStackCertifies es recSuccPayloadFlatSrc recSuccPayloadFlatTgt := by
  intro h
  rcases h with ⟨pre, e, post, _, _, hdrop⟩
  exact Nat.not_le_of_lt hdrop (coordExpr_payloadFlat_nondec e)

/-- Iterated delta wrapper. -/
@[simp] def deltaPow : Nat → Trace
| 0 => void
| k + 1 => delta (deltaPow k)

@[simp] theorem copyBudget_deltaPow (k : Nat) :
    copyBudget (deltaPow k) = k := by
  induction k with
  | zero =>
      simp [deltaPow, copyBudget]
  | succ k ih =>
      simp [deltaPow, copyBudget, ih]

@[simp] theorem counterBudget_deltaPow (k : Nat) :
    counterBudget (deltaPow k) = 0 := by
  induction k with
  | zero =>
      simp [deltaPow, counterBudget]
  | succ k ih =>
      simp [deltaPow, counterBudget, ih]

@[simp] theorem tau_deltaPow (k : Nat) :
    tau (deltaPow k) = 0 := by
  induction k with
  | zero =>
      simp [deltaPow, tau]
  | succ k ih =>
      simp [deltaPow, tau, ih]

@[simp] theorem copyMass_deltaPow (k : Nat) :
    copyMass (deltaPow k) = k := by
  induction k with
  | zero =>
      simp [deltaPow, copyMass]
  | succ k ih =>
      simp [deltaPow, copyMass, ih]

/-- Infinite payload-recursive `rec_succ` family with persistent copy pressure. -/
@[simp] def payloadRecFamily (k : Nat) : Trace :=
  recΔ void void (deltaPow (k + 1))

@[simp] def payloadRecFamilySrc (k : Nat) : Trace :=
  recΔ void (payloadRecFamily k) (delta (deltaPow k))

@[simp] def payloadRecFamilyTgt (k : Nat) : Trace :=
  app (payloadRecFamily k) (recΔ void (payloadRecFamily k) (deltaPow k))

theorem payloadRecFamily_step (k : Nat) :
    SafeStep (payloadRecFamilySrc k) (payloadRecFamilyTgt k) := by
  simpa [payloadRecFamilySrc, payloadRecFamilyTgt, payloadRecFamily] using
    (SafeStep.R_rec_succ void (payloadRecFamily k) (deltaPow k))

theorem payloadRecFamily_copyBudget_eq (k : Nat) :
    copyBudget (payloadRecFamilyTgt k) = copyBudget (payloadRecFamilySrc k) := by
  simp [payloadRecFamilySrc, payloadRecFamilyTgt, payloadRecFamily, copyBudget]

theorem payloadRecFamily_counterBudget_eq (k : Nat) :
    counterBudget (payloadRecFamilyTgt k) = counterBudget (payloadRecFamilySrc k) := by
  simp [payloadRecFamilySrc, payloadRecFamilyTgt, payloadRecFamily, counterBudget, copyBudget]

theorem payloadRecFamily_tau_increases (k : Nat) :
    tau (payloadRecFamilySrc k) < tau (payloadRecFamilyTgt k) := by
  simp [payloadRecFamilySrc, payloadRecFamilyTgt, payloadRecFamily, tau]

theorem payloadRecFamily_copyMass_nondec (k : Nat) :
    copyMass (payloadRecFamilySrc k) ≤ copyMass (payloadRecFamilyTgt k) := by
  simp [payloadRecFamilySrc, payloadRecFamilyTgt, payloadRecFamily, copyMass, copyBudget]
  omega

/-- The same monotone arithmetic closure is blocked on an infinite payload-recursive family,
not just on a single witness. -/
theorem coordExpr_payloadFamily_nondec (e : CoordExpr) (k : Nat) :
    e.eval (payloadRecFamilySrc k) ≤ e.eval (payloadRecFamilyTgt k) := by
  induction e generalizing k with
  | const n =>
      simp [CoordExpr.eval]
  | cb =>
      rw [CoordExpr.eval, CoordExpr.eval, payloadRecFamily_copyBudget_eq]
  | ctr =>
      rw [CoordExpr.eval, CoordExpr.eval, payloadRecFamily_counterBudget_eq]
  | tau =>
      exact Nat.le_of_lt (payloadRecFamily_tau_increases k)
  | mass =>
      exact payloadRecFamily_copyMass_nondec k
  | succ e ih =>
      simpa [CoordExpr.eval] using Nat.succ_le_succ (ih k)
  | add e₁ e₂ ih₁ ih₂ =>
      simpa [CoordExpr.eval] using Nat.add_le_add (ih₁ k) (ih₂ k)
  | max e₁ e₂ ih₁ ih₂ =>
      simpa [CoordExpr.eval] using max_le_max (ih₁ k) (ih₂ k)

theorem not_coordExprStackCertifies_payloadFamily (es : List CoordExpr) (k : Nat) :
    ¬ CoordExprStackCertifies es (payloadRecFamilySrc k) (payloadRecFamilyTgt k) := by
  intro h
  rcases h with ⟨pre, e, post, _, _, hdrop⟩
  exact Nat.not_le_of_lt hdrop (coordExpr_payloadFamily_nondec e k)

/-- Position-aware multiplicity potential: a recursor budgets `(copyBudget n + 1)` copies
of the payload cost, rather than using a global max or a naive whole-term sum. -/
@[simp] def ctxDupPotential : Trace → Nat
| void            => 0
| delta t         => ctxDupPotential t
| integrate t     => ctxDupPotential t + 1
| merge a b       => ctxDupPotential a + ctxDupPotential b + 1
| app a b         => ctxDupPotential a + ctxDupPotential b
| recΔ b s n      =>
    ctxDupPotential b +
      ctxDupPotential n +
      (copyBudget n + 1) * (ctxDupPotential s + 1) + 1
| eqW a b         => ctxDupPotential a + ctxDupPotential b + 3

/-- Every safe root step strictly decreases the position-aware multiplicity potential. -/
theorem ctxDupPotential_decreases_safe :
    ∀ {a b : Trace}, SafeStep a b → ctxDupPotential b < ctxDupPotential a
| _, _, SafeStep.R_int_delta t => by
    simp [ctxDupPotential]
| _, _, SafeStep.R_merge_void_left t _ => by
    simp [ctxDupPotential]
| _, _, SafeStep.R_merge_void_right t _ => by
    simp [ctxDupPotential]
| _, _, SafeStep.R_merge_cancel t _ _ => by
    simp [ctxDupPotential]
    omega
| _, _, SafeStep.R_rec_zero b s _ => by
    simp [ctxDupPotential]
    omega
| _, _, SafeStep.R_rec_succ b s n => by
    have hmain :
        ctxDupPotential s + (copyBudget n + 1) * (ctxDupPotential s + 1) <
          (copyBudget n + 2) * (ctxDupPotential s + 1) := by
      have hlt :
          ctxDupPotential s + (copyBudget n + 1) * (ctxDupPotential s + 1) <
            (ctxDupPotential s + 1) + (copyBudget n + 1) * (ctxDupPotential s + 1) := by
        exact Nat.add_lt_add_right (Nat.lt_succ_self (ctxDupPotential s))
          ((copyBudget n + 1) * (ctxDupPotential s + 1))
      have heq :
          (ctxDupPotential s + 1) + (copyBudget n + 1) * (ctxDupPotential s + 1) =
            (copyBudget n + 2) * (ctxDupPotential s + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.succ_mul (copyBudget n + 1) (ctxDupPotential s + 1)).symm
      exact lt_of_lt_of_eq hlt heq
    simpa [ctxDupPotential, copyBudget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_add, Nat.add_mul] using
      Nat.add_lt_add_right hmain (ctxDupPotential b + ctxDupPotential n + 1)
| _, _, SafeStep.R_eq_refl a _ => by
    simp [ctxDupPotential]
| _, _, SafeStep.R_eq_diff a b _ => by
    simp [ctxDupPotential]

/-- The position-aware multiplicity potential strictly decreases on every contextual step. -/
theorem ctxDupPotential_decreases_ctx :
    ∀ {a b : Trace}, SafeStepCtx a b → ctxDupPotential b < ctxDupPotential a
| _, _, SafeStepCtx.root hs =>
    ctxDupPotential_decreases_safe hs
| _, _, SafeStepCtx.integrate h => by
    simpa [ctxDupPotential] using Nat.succ_lt_succ (ctxDupPotential_decreases_ctx h)
| _, _, SafeStepCtx.mergeL (a := a) (a' := a') (b := b) h => by
    have ih := ctxDupPotential_decreases_ctx h
    simpa [ctxDupPotential, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_lt_add_right ih (ctxDupPotential b + 1)
| _, _, SafeStepCtx.mergeR (a := a) (b := b) (b' := b') h => by
    have ih := ctxDupPotential_decreases_ctx h
    have hsum : ctxDupPotential a + ctxDupPotential b' <
        ctxDupPotential a + ctxDupPotential b := Nat.add_lt_add_left ih (ctxDupPotential a)
    simpa [ctxDupPotential, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_lt_add_right hsum 1
| _, _, SafeStepCtx.appL (a := a) (a' := a') (b := b) h => by
    have ih := ctxDupPotential_decreases_ctx h
    simpa [ctxDupPotential, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_lt_add_right ih (ctxDupPotential b)
| _, _, SafeStepCtx.appR (a := a) (b := b) (b' := b') h => by
    have ih := ctxDupPotential_decreases_ctx h
    exact Nat.add_lt_add_left ih (ctxDupPotential a)
| _, _, SafeStepCtx.recB (b := b) (b' := b') (s := s) (n := n) h => by
    have ih := ctxDupPotential_decreases_ctx h
    let C : Nat := ctxDupPotential n + (copyBudget n + 1) * (ctxDupPotential s + 1) + 1
    have hsum : ctxDupPotential b' + C < ctxDupPotential b + C := Nat.add_lt_add_right ih C
    simpa [ctxDupPotential, C, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
| _, _, SafeStepCtx.recS (b := b) (s := s) (s' := s') (n := n) h => by
    have ih := ctxDupPotential_decreases_ctx h
    have hsucc : ctxDupPotential s' + 1 < ctxDupPotential s + 1 := Nat.succ_lt_succ ih
    have hmul :
        (copyBudget n + 1) * (ctxDupPotential s' + 1) <
          (copyBudget n + 1) * (ctxDupPotential s + 1) := by
      exact Nat.mul_lt_mul_of_pos_left hsucc (Nat.succ_pos _)
    let C : Nat := ctxDupPotential b + ctxDupPotential n
    have hsum : C + (copyBudget n + 1) * (ctxDupPotential s' + 1) <
        C + (copyBudget n + 1) * (ctxDupPotential s + 1) := Nat.add_lt_add_left hmul C
    simpa [ctxDupPotential, C, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_lt_add_right hsum 1
| _, _, SafeStepCtx.recN (b := b) (s := s) (n := n) (n' := n') h => by
    have ih := ctxDupPotential_decreases_ctx h
    have hcopy : copyBudget n' ≤ copyBudget n := copyBudget_mono_safeStepCtx h
    have hmul :
        (copyBudget n' + 1) * (ctxDupPotential s + 1) ≤
          (copyBudget n + 1) * (ctxDupPotential s + 1) := by
      exact Nat.mul_le_mul_right (ctxDupPotential s + 1) (Nat.succ_le_succ hcopy)
    let C' : Nat := ctxDupPotential b + ((copyBudget n' + 1) * (ctxDupPotential s + 1) + 1)
    let C : Nat := ctxDupPotential b + ((copyBudget n + 1) * (ctxDupPotential s + 1) + 1)
    have hleft : ctxDupPotential n' + C' < ctxDupPotential n + C' := Nat.add_lt_add_right ih C'
    have hright : ctxDupPotential n + C' ≤ ctxDupPotential n + C := by
      exact Nat.add_le_add_left
        (Nat.add_le_add_left (Nat.succ_le_succ hmul) (ctxDupPotential b))
        (ctxDupPotential n)
    have hfinal : ctxDupPotential n' + C' < ctxDupPotential n + C := lt_of_lt_of_le hleft hright
    simpa [ctxDupPotential, C', C, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

/-- Exact-length contextual chains are bounded by the new position-aware multiplicity potential. -/
theorem safeStepCtx_length_le_ctxDupPotential (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) : n ≤ ctxDupPotential t := by
  induction n generalizing t with
  | zero =>
      omega
  | succ n ih =>
      obtain ⟨v, hstep, hrest⟩ := h
      have hdrop := ctxDupPotential_decreases_ctx hstep
      have hv := ih v hrest
      omega

/-- `n + 1 ≤ 2 ^ n` for every natural number `n`. -/
private theorem succ_le_two_pow (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

/-- Powers of `2` are monotone in the exponent. -/
private theorem two_pow_mono {m n : Nat} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by decide) h

/-- `4 * 2^k = 2^(k+2)`. -/
private theorem four_mul_two_pow (k : Nat) : 4 * 2 ^ k = 2 ^ (k + 2) := by
  have h4 : (4 : Nat) = 2 ^ 2 := by decide
  calc
    4 * 2 ^ k = 2 ^ k * 4 := by ac_rfl
    _ = 2 ^ k * 2 ^ 2 := by rw [h4]
    _ = 2 ^ (k + 2) := by rw [← Nat.pow_add]

/-- `copyBudget` is bounded by structural term size. -/
theorem copyBudget_le_termSize (t : Trace) : copyBudget t ≤ termSize t := by
  induction t with
  | void =>
      simp [copyBudget, termSize]
  | delta t ih =>
      simpa [Nat.succ_eq_add_one, copyBudget, termSize, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using Nat.succ_le_succ ih
  | integrate t ih =>
      exact le_trans ih (by simp [termSize])
  | merge a b iha ihb =>
      simpa [copyBudget, termSize] using
        (max_le (le_trans iha (by omega)) (le_trans ihb (by omega)))
  | app a b iha ihb =>
      simpa [copyBudget, termSize] using
        (max_le (le_trans iha (by omega)) (le_trans ihb (by omega)))
  | recΔ b s n ihb ihs ihn =>
      have hb : copyBudget b ≤ 1 + termSize b + termSize s + termSize n := by
        omega
      have hs : copyBudget s ≤ 1 + termSize b + termSize s + termSize n := by
        omega
      have hn : copyBudget n ≤ 1 + termSize b + termSize s + termSize n := by
        omega
      simpa [copyBudget, termSize, max_le_iff] using And.intro hb (And.intro hs hn)
  | eqW a b iha ihb =>
      simpa [copyBudget, termSize] using
        (max_le (le_trans iha (by omega)) (le_trans ihb (by omega)))

/-- `copyBudget` itself is single-exponentially bounded by structural size. -/
theorem copyBudget_add_one_le_two_pow_double_termSize (t : Trace) :
    copyBudget t + 1 ≤ 2 ^ (2 * termSize t) := by
  have hsize : copyBudget t + 1 ≤ termSize t + 1 := Nat.succ_le_succ (copyBudget_le_termSize t)
  have hpow : termSize t + 1 ≤ 2 ^ termSize t := succ_le_two_pow (termSize t)
  have hmono : 2 ^ termSize t ≤ 2 ^ (2 * termSize t) := by
    exact two_pow_mono (by
      have hpos := termSize_pos t
      omega)
  exact le_trans hsize (le_trans hpow hmono)

/-- The position-aware multiplicity potential is bounded by a single exponential in term size. -/
theorem ctxDupPotential_add_one_le_two_pow_double_termSize (t : Trace) :
    ctxDupPotential t + 1 ≤ 2 ^ (2 * termSize t) := by
  induction t with
  | void =>
      simp [ctxDupPotential, termSize]
  | delta t ih =>
      simpa [ctxDupPotential, termSize] using
        le_trans ih (two_pow_mono (by omega))
  | integrate t ih =>
      have hpow : 1 ≤ 2 ^ (2 * termSize t) := Nat.one_le_pow (2 * termSize t) 2 (by omega)
      have hmain : ctxDupPotential t + 1 + 1 ≤ 2 ^ (2 * (termSize t + 1)) := by
        calc
        ctxDupPotential t + 1 + 1 ≤ 2 ^ (2 * termSize t) + 1 := by omega
        _ ≤ 2 ^ (2 * termSize t) + 2 ^ (2 * termSize t) := by
              exact Nat.add_le_add_left hpow _
        _ = 2 ^ (2 * termSize t + 1) := by
              rw [pow_succ]
              omega
        _ ≤ 2 ^ (2 * (termSize t + 1)) := by
              exact two_pow_mono (by omega)
      simpa [ctxDupPotential, termSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmain
  | merge a b iha ihb =>
      let K := 2 * termSize a + 2 * termSize b
      have hmono_a : 2 ^ (2 * termSize a) ≤ 2 ^ K := by
        exact two_pow_mono (by
          have hb := termSize_pos b
          omega)
      have hmono_b : 2 ^ (2 * termSize b) ≤ 2 ^ K := by
        exact two_pow_mono (by
          have ha := termSize_pos a
          omega)
      have haK : ctxDupPotential a + 1 ≤ 2 ^ K := le_trans iha hmono_a
      have hbK : ctxDupPotential b + 1 ≤ 2 ^ K := le_trans ihb hmono_b
      calc
        ctxDupPotential a + ctxDupPotential b + 2
            ≤ 2 ^ K + 2 ^ K := by omega
        _ = 2 ^ (K + 1) := by
              rw [pow_succ]
              omega
        _ ≤ 2 ^ (2 * (1 + termSize a + termSize b)) := by
              exact two_pow_mono (by omega)
  | app a b iha ihb =>
      let K := 2 * termSize a + 2 * termSize b
      have hmono_a : 2 ^ (2 * termSize a) ≤ 2 ^ K := by
        exact two_pow_mono (by
          have hb := termSize_pos b
          omega)
      have hmono_b : 2 ^ (2 * termSize b) ≤ 2 ^ K := by
        exact two_pow_mono (by
          have ha := termSize_pos a
          omega)
      have haK : ctxDupPotential a + 1 ≤ 2 ^ K := le_trans iha hmono_a
      have hbK : ctxDupPotential b + 1 ≤ 2 ^ K := le_trans ihb hmono_b
      calc
        ctxDupPotential a + ctxDupPotential b + 1
            ≤ 2 ^ K + 2 ^ K := by omega
        _ = 2 ^ (K + 1) := by
              rw [pow_succ]
              omega
        _ ≤ 2 ^ (2 * (1 + termSize a + termSize b)) := by
              exact two_pow_mono (by omega)
  | recΔ b s n ihb ihs ihn =>
      have hcb : copyBudget n + 1 ≤ 2 ^ (2 * termSize n) :=
        copyBudget_add_one_le_two_pow_double_termSize n
      have hpb :
          ctxDupPotential b ≤ 2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
        have hbmono :
            2 ^ (2 * termSize b) ≤
              2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
          exact two_pow_mono (by
            have hspos := termSize_pos s
            have hnpos := termSize_pos n
            omega)
        omega
      have hpn :
          ctxDupPotential n ≤ 2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
        have hnmono :
            2 ^ (2 * termSize n) ≤
              2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
          exact two_pow_mono (by
            have hbpos := termSize_pos b
            have hspos := termSize_pos s
            omega)
        omega
      have hprod :
          (copyBudget n + 1) * (ctxDupPotential s + 1) ≤
            2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
        have hmul :
            (copyBudget n + 1) * (ctxDupPotential s + 1) ≤
              2 ^ (2 * termSize n) * 2 ^ (2 * termSize s) :=
          Nat.mul_le_mul hcb ihs
        have hpow :
            2 ^ (2 * termSize n) * 2 ^ (2 * termSize s) ≤
              2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
          have hmono :
              2 ^ (2 * termSize n + 2 * termSize s) ≤
                2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
            exact two_pow_mono (by
              have hbpos := termSize_pos b
              omega)
          simpa [← Nat.pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmono
        exact le_trans hmul hpow
      have hconst :
          2 ≤ 2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
        have hs := succ_le_two_pow (2 * termSize b + 2 * termSize s + 2 * termSize n)
        have hbpos := termSize_pos b
        have hspos := termSize_pos s
        have hnpos := termSize_pos n
        omega
      have hsum :
          ctxDupPotential b + ctxDupPotential n +
              (copyBudget n + 1) * (ctxDupPotential s + 1) + 2
            ≤ 4 * 2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := by
        omega
      calc
        ctxDupPotential b + ctxDupPotential n +
            (copyBudget n + 1) * (ctxDupPotential s + 1) + 2
            ≤ 4 * 2 ^ (2 * termSize b + 2 * termSize s + 2 * termSize n) := hsum
        _ = 2 ^ ((2 * termSize b + 2 * termSize s + 2 * termSize n) + 2) := by
              rw [four_mul_two_pow]
        _ ≤ 2 ^ (2 * (1 + termSize b + termSize s + termSize n)) := by
              exact two_pow_mono (by omega)
  | eqW a b iha ihb =>
      let K := 2 * termSize a + 2 * termSize b
      have haK : ctxDupPotential a + 1 ≤ 2 ^ K := by
        refine le_trans iha ?_
        exact two_pow_mono (by
          have hb := termSize_pos b
          omega)
      have hbK : ctxDupPotential b + 1 ≤ 2 ^ K := by
        refine le_trans ihb ?_
        exact two_pow_mono (by
          have ha := termSize_pos a
          omega)
      have h2 : 2 ≤ 2 ^ K := by
        have hs := succ_le_two_pow K
        have ha := termSize_pos a
        have hb := termSize_pos b
        omega
      have hsum : ctxDupPotential a + ctxDupPotential b + 4 ≤ 4 * 2 ^ K := by
        omega
      calc
        ctxDupPotential a + ctxDupPotential b + 4
            ≤ 4 * 2 ^ K := hsum
        _ = 2 ^ (K + 2) := by
              rw [four_mul_two_pow]
        _ ≤ 2 ^ (2 * (1 + termSize a + termSize b)) := by
              exact two_pow_mono (by omega)

/-- Any contextual reduction chain is bounded by a single exponential in structural size. -/
theorem safeStepCtx_length_le_two_pow_double_termSize (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) : n + 1 ≤ 2 ^ (2 * termSize t) := by
  have hlen := safeStepCtx_length_le_ctxDupPotential t u n h
  have hpot := ctxDupPotential_add_one_le_two_pow_double_termSize t
  omega

end MetaSN_KO7
