import OperatorKO7.Meta.SafeStep_Complexity_Ordinal

/-!
# Position-aware contextual copy budget

This file contains the positive outcome of the tighter `SafeStepCtx`
complexity program.

What is kept here:
- the syntactic control coordinate `copyBudget`
- its monotonicity under `SafeStep` and `SafeStepCtx`
- the position-aware multiplicity potential `ctxDupPotential`
- the strict contextual descent proof
- the resulting exact-length and single-exponential size bounds

The exploratory obstruction side has been split out to
`Meta/ContextualCopyBudget_NoGo.lean`, which now contains the failed auxiliary
coordinates, payload-recursive counterexamples, and the class-level no-go
theorems for the initial monotone arithmetic measure family.
-/

open OperatorKO7 Trace

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
      have hv := ih v hrest
      have hdrop := ctxDupPotential_decreases_ctx hstep
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
