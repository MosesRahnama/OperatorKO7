import OperatorKO7.Meta.ContextClosed_SN

/-!
# Derivational Complexity Bounds for SafeStepCtx

This module extracts concrete derivation-length bounds from the existing
well-foundedness infrastructure. The `ctxFuel` measure provides a computable
numeric bound on the length of any `SafeStepCtx` reduction chain.

Main results:

- `SafeStepCtxPow n t u`: there is an `n`-step `SafeStepCtx` chain from `t` to `u`
- `safeStepCtx_length_le_ctxFuel`: any `n`-step chain satisfies `n ≤ ctxFuel t`
- `termSize`: structural size of a `Trace` term (≥ 1 for all terms)
- `complexity_bound`: combines `ctxFuel` with `termSize` for a Nat→Nat bound

Complexity class:

The ordinal calibration of the triple-lex measure at ω^ω · 2 (proved in
`DM_OrderType.lean` and `DM_OrderType_LowerBound.lean`) places the derivational
complexity of `SafeStep` root reduction in the multiply-recursive regime.
The `ctxFuel`-based bound proved here is a concrete but cruder overestimate
(tower-exponential in term size) that covers the full context-closed relation
`SafeStepCtx`.
-/

open OperatorKO7 Trace

namespace MetaSN_KO7

/-! ## Iterated context-closed reduction with step count -/

/-- `n`-fold iterated `SafeStepCtx` relation. -/
def SafeStepCtxPow : Nat → Trace → Trace → Prop
  | 0, t, u => t = u
  | n + 1, t, u => ∃ v, SafeStepCtx t v ∧ SafeStepCtxPow n v u

theorem safeStepCtxPow_zero (t : Trace) : SafeStepCtxPow 0 t t := rfl

theorem safeStepCtxPow_step {t v : Trace} (h : SafeStepCtx t v)
    {n : Nat} {u : Trace} (hrest : SafeStepCtxPow n v u) :
    SafeStepCtxPow (n + 1) t u :=
  ⟨v, h, hrest⟩

/-- Any `n`-step `SafeStepCtx` chain from `t` has `n ≤ ctxFuel t`. -/
theorem safeStepCtx_length_le_ctxFuel (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) : n ≤ ctxFuel t := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    obtain ⟨v, hstep, hrest⟩ := h
    have hv := ih v hrest
    have hdrop := ctxFuel_decreases_ctx hstep
    omega

/-! ## Structural term size -/

/-- Structural size of a `Trace` term (≥ 1 for all terms). -/
@[simp] def termSize : Trace → Nat
  | void => 1
  | delta t => 1 + termSize t
  | integrate t => 1 + termSize t
  | merge a b => 1 + termSize a + termSize b
  | app a b => 1 + termSize a + termSize b
  | recΔ b s n => 1 + termSize b + termSize s + termSize n
  | eqW a b => 1 + termSize a + termSize b

theorem termSize_pos (t : Trace) : 0 < termSize t := by
  cases t <;> simp [termSize] <;> omega

/-! ## Explicit complexity bound as a Nat → Nat function -/

/-- Tower of exponentials with additive headroom.
`towerBound 0 = 6`
`towerBound (n+1) = 2^(2 * towerBound n + 5) + towerBound n + 1` -/
def towerBound : Nat → Nat
  | 0 => 6
  | n + 1 => 2 ^ (2 * towerBound n + 5) + towerBound n + 1

theorem towerBound_pos (n : Nat) : 0 < towerBound n := by
  cases n with
  | zero => simp [towerBound]
  | succ n => simp [towerBound]

theorem towerBound_mono {m n : Nat} (h : m ≤ n) : towerBound m ≤ towerBound n := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    have : towerBound k ≤ 2 ^ (2 * towerBound k + 5) + towerBound k :=
      Nat.le_add_left _ _
    calc towerBound m ≤ towerBound k := ih
      _ ≤ 2 ^ (2 * towerBound k + 5) + towerBound k := this
      _ ≤ 2 ^ (2 * towerBound k + 5) + towerBound k + 1 := Nat.le_succ _

private theorem nat_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    have hdbl : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [pow_succ, ← Nat.two_mul, mul_comm]
    omega

private theorem towerBound_dominates (n : Nat) :
    2 * towerBound n + 4 ≤ towerBound (n + 1) := by
  have hle := nat_le_two_pow (2 * towerBound n + 5)
  show 2 * towerBound n + 4 ≤ 2 ^ (2 * towerBound n + 5) + towerBound n + 1
  omega

/-- The combined complexity bound. -/
def complexity_bound (n : Nat) : Nat := towerBound n

/-- `ctxFuel` is bounded by `towerBound` applied to `termSize`. -/
theorem ctxFuel_le_towerBound :
    ∀ (t : Trace), ctxFuel t ≤ towerBound (termSize t) := by
  intro t
  induction t with
  | void =>
    simp [ctxFuel, termSize]
  | delta t ih =>
    simp only [ctxFuel, termSize]
    rw [show 1 + termSize t = termSize t + 1 from Nat.add_comm 1 (termSize t)]
    have hexp : ctxFuel t + 1 ≤ 2 * towerBound (termSize t) + 5 := by omega
    calc 2 ^ (ctxFuel t + 1)
        ≤ 2 ^ (2 * towerBound (termSize t) + 5) :=
          Nat.pow_le_pow_right (by omega) hexp
      _ ≤ 2 ^ (2 * towerBound (termSize t) + 5) + towerBound (termSize t) + 1 :=
          Nat.le_add_right _ (towerBound (termSize t) + 1)
      _ = towerBound (termSize t + 1) := rfl
  | integrate t ih =>
    simp only [ctxFuel, termSize]
    rw [show 1 + termSize t = termSize t + 1 from Nat.add_comm 1 (termSize t)]
    have hdom := towerBound_dominates (termSize t)
    calc ctxFuel t + 1
        ≤ towerBound (termSize t) + 1 := by omega
      _ ≤ 2 * towerBound (termSize t) + 4 := by omega
      _ ≤ towerBound (termSize t + 1) := hdom
  | merge a b iha ihb =>
    simp only [ctxFuel, termSize]
    have ha := towerBound_mono (show termSize a ≤ termSize a + termSize b by omega)
    have hb := towerBound_mono (show termSize b ≤ termSize a + termSize b by omega)
    have hdom := towerBound_dominates (termSize a + termSize b)
    calc ctxFuel a + ctxFuel b + 2
        ≤ 2 * towerBound (termSize a + termSize b) + 2 := by omega
      _ ≤ 2 * towerBound (termSize a + termSize b) + 4 := by omega
      _ ≤ towerBound (termSize a + termSize b + 1) := hdom
      _ ≤ towerBound (1 + termSize a + termSize b) := towerBound_mono (by omega)
  | app a b iha ihb =>
    simp only [ctxFuel, termSize]
    have ha := towerBound_mono (show termSize a ≤ termSize a + termSize b by omega)
    have hb := towerBound_mono (show termSize b ≤ termSize a + termSize b by omega)
    have hdom := towerBound_dominates (termSize a + termSize b)
    calc ctxFuel a + ctxFuel b + 1
        ≤ 2 * towerBound (termSize a + termSize b) + 1 := by omega
      _ ≤ 2 * towerBound (termSize a + termSize b) + 4 := by omega
      _ ≤ towerBound (termSize a + termSize b + 1) := hdom
      _ ≤ towerBound (1 + termSize a + termSize b) := towerBound_mono (by omega)
  | eqW a b iha ihb =>
    simp only [ctxFuel, termSize]
    have ha := towerBound_mono (show termSize a ≤ termSize a + termSize b by omega)
    have hb := towerBound_mono (show termSize b ≤ termSize a + termSize b by omega)
    have hdom := towerBound_dominates (termSize a + termSize b)
    calc ctxFuel a + ctxFuel b + 4
        ≤ 2 * towerBound (termSize a + termSize b) + 4 := by omega
      _ ≤ towerBound (termSize a + termSize b + 1) := hdom
      _ ≤ towerBound (1 + termSize a + termSize b) := towerBound_mono (by omega)
  | recΔ b s n ihb ihs ihn =>
    simp only [ctxFuel, termSize]
    set sb := termSize b; set ss := termSize s; set sn := termSize n
    have hns : ctxFuel n + ctxFuel s ≤ 2 * towerBound (sb + ss + sn) := by
      have := towerBound_mono (show sn ≤ sb + ss + sn by omega)
      have := towerBound_mono (show ss ≤ sb + ss + sn by omega)
      omega
    have hb_le := towerBound_mono (show sb ≤ sb + ss + sn by omega)
    have hexp : ctxFuel n + ctxFuel s + 5 ≤ 2 * towerBound (sb + ss + sn) + 5 := by omega
    have hpow := Nat.pow_le_pow_right (show 0 < 2 by omega) hexp
    have hfinal : 2 ^ (ctxFuel n + ctxFuel s + 5) + ctxFuel b + 1 ≤
        2 ^ (2 * towerBound (sb + ss + sn) + 5) + towerBound (sb + ss + sn) + 1 := by omega
    calc 2 ^ (ctxFuel n + ctxFuel s + 5) + ctxFuel b + 1
        ≤ 2 ^ (2 * towerBound (sb + ss + sn) + 5) + towerBound (sb + ss + sn) + 1 := hfinal
      _ = towerBound (sb + ss + sn + 1) := rfl
      _ ≤ towerBound (1 + sb + ss + sn) := towerBound_mono (by omega)

/-- The main derivational complexity theorem: for any term `t` of structural
size `n`, any `SafeStepCtx` reduction chain from `t` has length at most
`complexity_bound n = towerBound n`. -/
theorem safestep_length_bounded_by_size (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n ≤ complexity_bound (termSize t) := by
  exact le_trans (safeStepCtx_length_le_ctxFuel t u n h) (ctxFuel_le_towerBound t)

end MetaSN_KO7
