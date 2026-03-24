import OperatorKO7.Meta.ContextualCopyBudget

/-!
# Single-Exponential Contextual Complexity Bound

This module packages the positive outcome of the contextual copy-budget analysis.
The constructive measure now lives in `ContextualCopyBudget.lean`, while the
discarded auxiliary coordinates and no-go results were split into
`ContextualCopyBudget_NoGo.lean`. Here we expose only the resulting upper-bound
interface:

- `contextualExpBound n = 2^(2n)`
- `ctxDupPotential t + 1 ≤ contextualExpBound (termSize t)`
- any exact-length `SafeStepCtx` chain from `t` has length at most
  `contextualExpBound (termSize t)`

So the context-closed guarded relation `SafeStepCtx` admits a concrete
single-exponential structural size bound.
-/

open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Public single-exponential contextual complexity envelope. -/
def contextualExpBound (n : Nat) : Nat := 2 ^ (2 * n)

private theorem nat_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

theorem contextualExpBound_le_complexity_bound (n : Nat) :
    contextualExpBound n ≤ complexity_bound n := by
  induction n with
  | zero =>
      simp [contextualExpBound, complexity_bound, towerBound]
  | succ n ih =>
      have hpow :
          4 * towerBound n ≤ 2 ^ (2 * towerBound n + 5) := by
        have hnat : towerBound n ≤ 2 ^ towerBound n := nat_le_two_pow (towerBound n)
        have hmul : 4 * towerBound n ≤ 4 * 2 ^ towerBound n := Nat.mul_le_mul_left 4 hnat
        have hpow2 : (2 ^ (2 : Nat)) = 4 := by decide
        have hmono : 2 ^ (towerBound n + 2) ≤ 2 ^ (2 * towerBound n + 5) := by
          exact Nat.pow_le_pow_right (by decide) (by omega)
        have hfour : 4 * 2 ^ towerBound n = 2 ^ (towerBound n + 2) := by
          calc
            4 * 2 ^ towerBound n = 2 ^ towerBound n * 4 := by ac_rfl
            _ = 2 ^ towerBound n * 2 ^ 2 := by rw [← hpow2]
            _ = 2 ^ (towerBound n + 2) := by rw [← Nat.pow_add]
        exact le_trans (by simpa [hfour] using hmul) hmono
      have hexp : contextualExpBound (n + 1) = 4 * contextualExpBound n := by
        have hpow2 : (2 ^ (2 : Nat)) = 4 := by decide
        have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
        calc
          contextualExpBound (n + 1)
              = 2 ^ (2 * n + 2) := by simp [contextualExpBound, htwo]
          _ = 2 ^ (2 * n) * 2 ^ 2 := by rw [Nat.pow_add]
          _ = 4 * contextualExpBound n := by
                simp [contextualExpBound, hpow2, Nat.mul_comm]
      have hstep :
          4 * complexity_bound n ≤ 2 ^ (2 * towerBound n + 5) + towerBound n + 1 := by
        simp [complexity_bound]
        omega
      calc
        contextualExpBound (n + 1) = 4 * contextualExpBound n := hexp
        _ ≤ 4 * complexity_bound n := Nat.mul_le_mul_left 4 ih
        _ ≤ 2 ^ (2 * towerBound n + 5) + towerBound n + 1 := hstep
        _ = complexity_bound (n + 1) := by
              simp [complexity_bound, towerBound]

theorem ctxDupPotential_add_one_le_contextualExpBound (t : Trace) :
    ctxDupPotential t + 1 ≤ contextualExpBound (termSize t) := by
  simpa [contextualExpBound] using ctxDupPotential_add_one_le_two_pow_double_termSize t

theorem safeStepCtx_length_le_contextualExpBound (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n + 1 ≤ contextualExpBound (termSize t) := by
  simpa [contextualExpBound] using safeStepCtx_length_le_two_pow_double_termSize t u n h

/-- Paper-facing alias: the full context-closed guarded derivation length is
single-exponential in structural term size. -/
theorem safeStepCtx_length_le_singleExponential (t u : Trace) (n : Nat)
    (h : SafeStepCtxPow n t u) :
    n + 1 ≤ 2 ^ (2 * termSize t) :=
  safeStepCtx_length_le_two_pow_double_termSize t u n h

end MetaSN_KO7
