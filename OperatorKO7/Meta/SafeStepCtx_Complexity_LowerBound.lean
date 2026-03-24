import OperatorKO7.Meta.SafeStepCtx_Complexity_Exponential

/-!
# Exponential Lower Family for `SafeStepCtx`

This module complements the single-exponential upper bound for the guarded
context-closed relation `SafeStepCtx` with an explicit lower family.

The family is

* `ctxLowerFamily 0 = merge void void`
* `ctxLowerFamily (n+1) = recΔ void (ctxLowerFamily n) (delta (delta void))`

Each outer `rec_succ` step duplicates the payload once, yielding the exact
length recurrence

* `ctxLowerLen 0 = 1`
* `ctxLowerLen (n+1) = 2 * ctxLowerLen n + 3`

while structural size grows only linearly:

* `termSize (ctxLowerFamily n) = 5 * n + 3`.

So the guarded context-closed derivational complexity is not merely bounded
above by a single exponential; it also has a concrete single-exponential lower
family.
-/

open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Concatenate exact-length `SafeStepCtxPow` chains. -/
theorem safeStepCtxPow_trans {a b c : Trace} {m n : Nat}
    (hab : SafeStepCtxPow m a b) (hbc : SafeStepCtxPow n b c) :
    SafeStepCtxPow (m + n) a c := by
  induction m generalizing a b c with
  | zero =>
      cases hab
      simpa using hbc
  | succ m ih =>
      rcases hab with ⟨v, hav, hvb⟩
      simpa [Nat.succ_add] using
        (show SafeStepCtxPow (Nat.succ (m + n)) a c from
          ⟨v, hav, ih hvb hbc⟩)

/-- Lift an exact-length contextual chain through the left side of `app`. -/
theorem safeStepCtxPow_appL {a a' b : Trace} {n : Nat}
    (haa' : SafeStepCtxPow n a a') :
    SafeStepCtxPow n (app a b) (app a' b) := by
  induction n generalizing a a' with
  | zero =>
      cases haa'
      rfl
  | succ n ih =>
      rcases haa' with ⟨v, hav, hva'⟩
      exact ⟨app v b, SafeStepCtx.appL hav, ih hva'⟩

/-- Lift an exact-length contextual chain through the right side of `app`. -/
theorem safeStepCtxPow_appR {a b b' : Trace} {n : Nat}
    (hbb' : SafeStepCtxPow n b b') :
    SafeStepCtxPow n (app a b) (app a b') := by
  induction n generalizing b b' with
  | zero =>
      cases hbb'
      rfl
  | succ n ih =>
      rcases hbb' with ⟨v, hbv, hvb'⟩
      exact ⟨app a v, SafeStepCtx.appR hbv, ih hvb'⟩

/-- Contextual lower-bound source family. -/
@[simp] def ctxLowerFamily : Nat → Trace
| 0 => merge void void
| n + 1 => recΔ void (ctxLowerFamily n) (delta (delta void))

/-- Explicit target normal form for the lower-bound family. -/
@[simp] def ctxLowerNF : Nat → Trace
| 0 => void
| n + 1 => app (ctxLowerNF n) (app (ctxLowerNF n) void)

/-- Exact contextual derivation length of the lower-bound family. -/
@[simp] def ctxLowerLen : Nat → Nat
| 0 => 1
| n + 1 => 2 * ctxLowerLen n + 3

/-- The exact target normal forms also have exponential structural size. -/
@[simp] theorem termSize_ctxLowerNF (n : Nat) :
    termSize (ctxLowerNF n) = 2 ^ (n + 2) - 3 := by
  induction n with
  | zero =>
      simp [ctxLowerNF, termSize]
  | succ n ih =>
      calc
        termSize (ctxLowerNF (n + 1))
            = 2 * termSize (ctxLowerNF n) + 3 := by
                simp [ctxLowerNF, termSize]
                omega
        _ = 2 * (2 ^ (n + 2) - 3) + 3 := by rw [ih]
        _ = 2 ^ (n + 3) - 3 := by
              have hpow : 4 ≤ 2 ^ (n + 2) := by
                calc
                  4 = 2 ^ 2 := by decide
                  _ ≤ 2 ^ (n + 2) := by
                    exact Nat.pow_le_pow_right (by decide) (by omega)
              calc
                2 * (2 ^ (n + 2) - 3) + 3 = 2 * 2 ^ (n + 2) - 3 := by omega
                _ = 2 ^ (n + 2) * 2 - 3 := by rw [Nat.mul_comm]
                _ = 2 ^ (n + 3) - 3 := by
                  simp [pow_succ, Nat.mul_comm]

/-- Structural size of the lower-bound family grows linearly. -/
@[simp] theorem termSize_ctxLowerFamily (n : Nat) :
    termSize (ctxLowerFamily n) = 5 * n + 3 := by
  induction n with
  | zero =>
      simp [ctxLowerFamily, termSize]
  | succ n ih =>
      simp [ctxLowerFamily, termSize, ih]
      omega

/-- The lower-bound family realizes its exact contextual derivation length. -/
theorem ctxLowerFamily_pow_nf (n : Nat) :
    SafeStepCtxPow (ctxLowerLen n) (ctxLowerFamily n) (ctxLowerNF n) := by
  induction n with
  | zero =>
      refine ⟨void, ?_, rfl⟩
      refine SafeStepCtx.root ?_
      simpa [ctxLowerFamily] using (SafeStep.R_merge_void_left void rfl)
  | succ n ih =>
      let T := ctxLowerFamily n
      let N := ctxLowerNF n
      let f := ctxLowerLen n
      let s1 : Trace := app T (recΔ void T (delta void))
      let s2 : Trace := app T (app T (recΔ void T void))
      let s3 : Trace := app T (app T void)
      have h1 : SafeStepCtxPow 1 (ctxLowerFamily (n + 1)) s1 := by
        refine ⟨s1, ?_, rfl⟩
        refine SafeStepCtx.root ?_
        simpa [ctxLowerFamily, s1, T] using (SafeStep.R_rec_succ void T (delta void))
      have h2 : SafeStepCtxPow 1 s1 s2 := by
        refine ⟨s2, ?_, rfl⟩
        refine SafeStepCtx.appR ?_
        refine SafeStepCtx.root ?_
        simpa [s1, s2, T] using (SafeStep.R_rec_succ void T void)
      have h3 : SafeStepCtxPow 1 s2 s3 := by
        refine ⟨s3, ?_, rfl⟩
        refine SafeStepCtx.appR ?_
        refine SafeStepCtx.appR ?_
        refine SafeStepCtx.root ?_
        simpa [s2, s3, T] using (SafeStep.R_rec_zero void T rfl)
      have hleft : SafeStepCtxPow f s3 (app N (app T void)) := by
        simpa [s3, T, N] using (safeStepCtxPow_appL (b := app T void) ih)
      have hrightInner : SafeStepCtxPow f (app T void) (app N void) := by
        simpa [T, N] using (safeStepCtxPow_appL (b := void) ih)
      have hright : SafeStepCtxPow f (app N (app T void)) (app N (app N void)) := by
        simpa [T, N] using (safeStepCtxPow_appR (a := N) hrightInner)
      have h123 : SafeStepCtxPow 3 (ctxLowerFamily (n + 1)) s3 := by
        have h12 : SafeStepCtxPow 2 (ctxLowerFamily (n + 1)) s2 := by
          simpa using safeStepCtxPow_trans h1 h2
        simpa [Nat.add_assoc] using safeStepCtxPow_trans h12 h3
      have h123left : SafeStepCtxPow (3 + f) (ctxLowerFamily (n + 1)) (app N (app T void)) := by
        simpa [Nat.add_assoc] using safeStepCtxPow_trans h123 hleft
      have hfinal : SafeStepCtxPow ((3 + f) + f) (ctxLowerFamily (n + 1)) (ctxLowerNF (n + 1)) := by
        simpa [ctxLowerNF, N, Nat.add_assoc] using safeStepCtxPow_trans h123left hright
      simpa [ctxLowerLen, f, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

/-- The exact lower-family length dominates `2^n`, so the family is exponentially long. -/
theorem two_pow_le_ctxLowerLen (n : Nat) :
    2 ^ n ≤ ctxLowerLen n := by
  induction n with
  | zero =>
      simp [ctxLowerLen]
  | succ n ih =>
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [pow_succ]
          ac_rfl
        _ ≤ 2 * ctxLowerLen n := Nat.mul_le_mul_left 2 ih
        _ ≤ 2 * ctxLowerLen n + 3 := by omega
        _ = ctxLowerLen (n + 1) := by simp [ctxLowerLen]

/-- Public existence theorem: guarded context-closed reduction has an explicit
single-exponential lower family with linear source size. -/
theorem safeStepCtx_has_singleExponential_lower_family (n : Nat) :
    ∃ t u : Trace, ∃ m : Nat,
      termSize t = 5 * n + 3 ∧
      SafeStepCtxPow m t u ∧
      2 ^ n ≤ m := by
  refine ⟨ctxLowerFamily n, ctxLowerNF n, ctxLowerLen n, ?_, ?_, ?_⟩
  · exact termSize_ctxLowerFamily n
  · exact ctxLowerFamily_pow_nf n
  · exact two_pow_le_ctxLowerLen n

/-- The lower family also lies under the already exported single-exponential
upper envelope, pinning the guarded contextual complexity class between
matching exponentials up to constant factors in the exponent. -/
theorem safeStepCtx_has_singleExponential_size_family (n : Nat) :
    ∃ t u : Trace, ∃ m : Nat,
      termSize t = 5 * n + 3 ∧
      SafeStepCtxPow m t u ∧
      2 ^ n ≤ m ∧
      m + 1 ≤ contextualExpBound (termSize t) := by
  refine ⟨ctxLowerFamily n, ctxLowerNF n, ctxLowerLen n, ?_, ?_, ?_, ?_⟩
  · exact termSize_ctxLowerFamily n
  · exact ctxLowerFamily_pow_nf n
  · exact two_pow_le_ctxLowerLen n
  · exact safeStepCtx_length_le_contextualExpBound _ _ _ (ctxLowerFamily_pow_nf n)

/-- The same lower family also yields exponential normal-form size from a
linear-size guarded source. This gives a direct duplication-growth witness
without appealing to any external match-bound metatheory. -/
theorem safeStepCtx_has_singleExponential_output_family (n : Nat) :
    ∃ t u : Trace, ∃ m : Nat,
      termSize t = 5 * n + 3 ∧
      SafeStepCtxPow m t u ∧
      termSize u = 2 ^ (n + 2) - 3 := by
  refine ⟨ctxLowerFamily n, ctxLowerNF n, ctxLowerLen n, ?_, ?_, ?_⟩
  · exact termSize_ctxLowerFamily n
  · exact ctxLowerFamily_pow_nf n
  · exact termSize_ctxLowerNF n

end MetaSN_KO7
