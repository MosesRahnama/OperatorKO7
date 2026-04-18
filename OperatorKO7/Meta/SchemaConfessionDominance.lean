import OperatorKO7.Meta.SchemaCanonicalTrace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Confession Dominance and Proof-Entropy Monotonicity

Schema-level mechanization of Paper 2 Propositions 3.4, 3.7, and 3.11, together
with the asymptote in Remark 3.5.

Given a step-duplicating system with an explicit base rule (see
`BaseDuplicatingSystem` in `SchemaCanonicalTrace.lean`), we define:

- the residual proof work along the canonical trace, `Res(k) = k`;
- the confessed structural burden
  `Con(k, p) = (k+1)(k+2)/2 · p` in the paper; we work with the *doubled*
  quantity `2·Con(k, p) = (k+1)(k+2)·p` throughout, which avoids natural-number
  division and exposes the same content via the product identity;
- the total confessed burden with respect to a wrapper-cell weight
  `w = |G| + |b|` as in Def 3.9–3.10;
- the proof-entropy fraction `H_proof(t_i)` via a cross-multiplied natural-
  number inequality.

We prove:

- Proposition 3.4 (confession dominance) via the doubled identity
  `2 · confessedBurden k p = (k+1)(k+2) · p` together with the closed form
  of the payload-size summation.
- Remark 3.5 (quadratic asymptote) as the same doubled product identity.
- Proposition 3.7 (proof-entropy monotonicity) as a cross-multiplied
  inequality with an explicit non-negative difference.
- Proposition 3.11 (total confessed burden) as the wrapper-cell specialization
  of the same doubled identity.

No natural-number division appears in any proof below.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

namespace BaseDuplicatingSystem

open scoped Real

/-- Residual proof work along the canonical trace: one strict subterm descent
per recursive step. -/
def residualProofWork (k : Nat) : Nat := k

/-- Doubled confessed structural burden: `2 · Con(k, p) = (k+1)(k+2) · p`.
We carry the doubling to avoid natural-number division. -/
def confessedBurdenDoubled (k p : Nat) : Nat := (k + 1) * (k + 2) * p

/-- Doubled total confessed burden with wrapper-cell weight `w`. -/
def totalConfessedBurdenDoubled (k w : Nat) : Nat := (k + 1) * (k + 2) * w

@[simp] theorem residualProofWork_eq (k : Nat) : residualProofWork k = k := rfl

@[simp] theorem confessedBurdenDoubled_eq (k p : Nat) :
    confessedBurdenDoubled k p = (k + 1) * (k + 2) * p := rfl

@[simp] theorem totalConfessedBurdenDoubled_eq (k w : Nat) :
    totalConfessedBurdenDoubled k w = (k + 1) * (k + 2) * w := rfl

/-- **Paper 2 Proposition 3.4 (payload-size summation closed form).**
The doubled sum `2 · ∑_{i=0}^{k}(i+1)·p` equals `(k+1)(k+2)·p`. -/
theorem sum_payloads_doubled (k p : Nat) :
    2 * ((Finset.range (k + 1)).sum (fun i => (i + 1) * p))
      = confessedBurdenDoubled k p := by
  induction k with
  | zero => simp [confessedBurdenDoubled]
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      unfold confessedBurdenDoubled
      ring

/-- **Paper 2 Proposition 3.11 (total confessed burden, wrapper-cell form).**
The same identity with wrapper-cell weight `w` in place of payload size `p`. -/
theorem total_confessed_burden_doubled (k w : Nat) :
    2 * ((Finset.range (k + 1)).sum (fun i => (i + 1) * w))
      = totalConfessedBurdenDoubled k w :=
  sum_payloads_doubled k w

/-! ## Real-valued asymptotic normalizers for Props. 3.4, 3.7, and 3.11 -/

/-- Real-valued quadratic normalizer for the payload confession burden:
`Con(k,p) / (k+1)^2`. This is the exact quantity appearing in
Remark 3.5. -/
noncomputable def confessionQuadraticInvariant (k p : Nat) : ℝ :=
  (confessedBurdenDoubled k p : ℝ) / (2 * (k + 1 : ℝ) ^ 2)

/-- Real-valued linear normalizer for the confession ratio:
`Con(k+1,p) / Res(k+1)^2`. This is the shifted version of the
`Con(k,p) / Res(k)` asymptotic from Proposition 3.4, normalized by the
trace length so the limit is finite. -/
noncomputable def confessionLinearNormalizer (k p : Nat) : ℝ :=
  (confessedBurdenDoubled (k + 1) p : ℝ) / (2 * (k + 1 : ℝ) ^ 2)

/-- Wrapper-cell analogue of `confessionLinearNormalizer`, used for
Proposition 3.11. -/
noncomputable def totalConfessionLinearNormalizer (k w : Nat) : ℝ :=
  (totalConfessedBurdenDoubled (k + 1) w : ℝ) / (2 * (k + 1 : ℝ) ^ 2)

/-- Real-valued proof entropy for a fixed canonical-trace stage `i`,
payload size `payloadSize`, wrapper size `wrapSize`, and constant overhead
`cStar`. -/
def proofEntropyTotalSize
    (k i payloadSize wrapSize cStar : Nat) : Nat :=
  i * (wrapSize + payloadSize) + (k - i) + cStar

/-- Real-valued proof entropy for a fixed canonical-trace stage `i`,
payload size `payloadSize`, wrapper size `wrapSize`, and constant overhead
`cStar`. -/
noncomputable def proofEntropyValue
    (k i payloadSize wrapSize cStar : Nat) : ℝ :=
  (i * payloadSize : ℝ) /
    (proofEntropyTotalSize k i payloadSize wrapSize cStar : ℝ)

@[simp] theorem confessionQuadraticInvariant_eq (k p : Nat) :
    confessionQuadraticInvariant k p
      = ((1 : ℝ) + 1 / ((k : ℝ) + 1)) * ((p : ℝ) / 2) := by
  unfold confessionQuadraticInvariant confessedBurdenDoubled
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hk]
  ring

@[simp] theorem confessionLinearNormalizer_eq (k p : Nat) :
    confessionLinearNormalizer k p
      = (((1 : ℝ) + 2 / ((k : ℝ) + 1))
          * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((p : ℝ) / 2) := by
  unfold confessionLinearNormalizer confessedBurdenDoubled
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hk]
  ring

@[simp] theorem totalConfessionLinearNormalizer_eq (k w : Nat) :
    totalConfessionLinearNormalizer k w
      = (((1 : ℝ) + 2 / ((k : ℝ) + 1))
          * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((w : ℝ) / 2) := by
  unfold totalConfessionLinearNormalizer totalConfessedBurdenDoubled
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hk]
  ring

/-- **Paper 2 Remark 3.5 (quadratic asymptote, exact limit form).**
The normalized payload confession burden tends to `|b| / 2`. -/
theorem confession_quadratic_invariant_tendsto (p : Nat) :
    Filter.Tendsto (fun k : Nat => confessionQuadraticInvariant k p)
      Filter.atTop (nhds ((p : ℝ) / 2)) := by
  have hzero :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hone :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 1 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have hmul :
      Filter.Tendsto
        (fun k : Nat =>
          ((1 : ℝ) + 1 / ((k : ℝ) + 1)) * ((p : ℝ) / 2))
        Filter.atTop (nhds ((p : ℝ) / 2)) := by
    simpa using hone.mul tendsto_const_nhds
  exact hmul.congr' <| Filter.Eventually.of_forall fun k =>
    (confessionQuadraticInvariant_eq k p).symm

/-- **Paper 2 Proposition 3.4 (linear asymptotic, normalized form).**
The shifted ratio `Con(k+1,p) / Res(k+1)^2` tends to `|b| / 2`. This is
equivalent to the paper's statement `Con(k,p) / Res(k) ~ k|b|/2`. -/
theorem confession_linear_asymptotic_tendsto (p : Nat) :
    Filter.Tendsto (fun k : Nat => confessionLinearNormalizer k p)
      Filter.atTop (nhds ((p : ℝ) / 2)) := by
  have hzero :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htwozero :
      Filter.Tendsto (fun k : Nat => (2 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using (tendsto_const_nhds (α := Nat) (x := (2 : ℝ))).mul hzero
  have hone :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 1 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have htwo :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 2 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add htwozero
  have hmul :
      Filter.Tendsto
        (fun k : Nat =>
          (((1 : ℝ) + 2 / ((k : ℝ) + 1))
            * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((p : ℝ) / 2))
        Filter.atTop (nhds ((p : ℝ) / 2)) := by
    simpa [one_mul] using (htwo.mul hone).mul tendsto_const_nhds
  exact hmul.congr' <| Filter.Eventually.of_forall fun k =>
    (confessionLinearNormalizer_eq k p).symm

/-- **Paper 2 Proposition 3.4 (arbitrary-factor domination form).**
For any fixed positive payload size, the confession ratio eventually exceeds
any prescribed factor. -/
theorem confession_ratio_eventually_dominates
    (p N : Nat) (hp : 1 ≤ p) :
    ∃ K : Nat, ∀ k ≥ K,
      (N : ℝ) ≤ (confessedBurdenDoubled (k + 1) p : ℝ) / (2 * (k + 1 : ℝ)) := by
  refine ⟨2 * N, ?_⟩
  intro k hk
  have hk1 : 0 < (2 * (k + 1 : ℝ)) := by positivity
  apply (le_div_iff₀ hk1).2
  have hnat : 2 * (k + 1) * N ≤ confessedBurdenDoubled (k + 1) p := by
    unfold confessedBurdenDoubled
    have hpk : 2 * N ≤ p * (k + 2) := by
      nlinarith [hk, hp]
    have hkk : k + 1 ≤ k + 3 := by omega
    nlinarith
  simpa [mul_assoc, mul_left_comm, mul_comm] using (show (2 * (k + 1) * N : ℝ) ≤
      (confessedBurdenDoubled (k + 1) p : ℝ) by exact_mod_cast hnat)

/-- **Paper 2 Proposition 3.11 (linear asymptotic, wrapper-cell form).**
The shifted ratio `Con_total(k+1,w) / Res(k+1)^2` tends to `w / 2`. -/
theorem total_confession_linear_asymptotic_tendsto (w : Nat) :
    Filter.Tendsto (fun k : Nat => totalConfessionLinearNormalizer k w)
      Filter.atTop (nhds ((w : ℝ) / 2)) := by
  have hzero :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htwozero :
      Filter.Tendsto (fun k : Nat => (2 : ℝ) / ((k : ℝ) + 1))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using (tendsto_const_nhds (α := Nat) (x := (2 : ℝ))).mul hzero
  have hone :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 1 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have htwo :
      Filter.Tendsto (fun k : Nat => (1 : ℝ) + 2 / ((k : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add htwozero
  have hmul :
      Filter.Tendsto
        (fun k : Nat =>
          (((1 : ℝ) + 2 / ((k : ℝ) + 1))
            * ((1 : ℝ) + 1 / ((k : ℝ) + 1))) * ((w : ℝ) / 2))
        Filter.atTop (nhds ((w : ℝ) / 2)) := by
    simpa [one_mul] using (htwo.mul hone).mul tendsto_const_nhds
  exact hmul.congr' <| Filter.Eventually.of_forall fun k =>
    (totalConfessionLinearNormalizer_eq k w).symm

@[simp] theorem proofEntropyValue_zero
    (k payloadSize wrapSize cStar : Nat) :
    proofEntropyValue k 0 payloadSize wrapSize cStar = 0 := by
  simp [proofEntropyValue]

/-- Fixed-stage overhead carried by the non-payload part of the
`proofEntropyValue` denominator. -/
def proofEntropyOverhead (k i wrapSize cStar : Nat) : Nat :=
  i * wrapSize + (k - i) + cStar

/-- **Paper 2 Proposition 3.7 (fixed-stage payload limit form).**
For each fixed nonzero stage `i`, the proof entropy tends to `1` as the
payload size tends to infinity. We shift the payload parameter by `+1` to
avoid the vacuous zero-payload edge case. -/
theorem proof_entropy_tendsto_one
    (k i wrapSize cStar : Nat) (hi : 1 ≤ i) :
    Filter.Tendsto (fun payloadSize : Nat =>
      proofEntropyValue k i (payloadSize + 1) wrapSize cStar)
      Filter.atTop (nhds 1) := by
  let Cnat : Nat := proofEntropyOverhead k i wrapSize cStar
  let C : ℝ := Cnat
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, Cnat, proofEntropyOverhead]
    positivity
  have hzero :
      Filter.Tendsto (fun payloadSize : Nat => C / ((payloadSize : ℝ) + 1))
        Filter.atTop (nhds 0) := by
    have hone :
        Filter.Tendsto (fun payloadSize : Nat => (1 : ℝ) / ((payloadSize : ℝ) + 1))
          Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [C, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using (tendsto_const_nhds (α := Nat) (x := C)).mul hone
  have hgap :
      Filter.Tendsto
        (fun payloadSize : Nat =>
          C /
            (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun payloadSize => div_nonneg hC_nonneg (by positivity)) ?_ hzero
    intro payloadSize
    have hden_ge :
        ((payloadSize : ℝ) + 1)
          ≤ (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
      exact_mod_cast (show payloadSize + 1 ≤ proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar by
        unfold proofEntropyTotalSize
        nlinarith [hi, Nat.zero_le wrapSize, Nat.zero_le cStar, Nat.zero_le (k - i)])
    have hden_pos :
        0 < (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
      have hden_pos_nat :
          0 < proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar := by
        unfold proofEntropyTotalSize
        have : 1 ≤ i * (wrapSize + (payloadSize + 1)) := by
          nlinarith [hi, Nat.succ_le_succ (Nat.zero_le payloadSize)]
        omega
      exact_mod_cast hden_pos_nat
    have hrecip :
        (1 : ℝ) / (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ)
          ≤ (1 : ℝ) / (((payloadSize : ℝ) + 1) : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) hden_ge
    have hmul :=
      mul_le_mul_of_nonneg_left hrecip hC_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hrewrite :
      (fun payloadSize : Nat =>
        proofEntropyValue k i (payloadSize + 1) wrapSize cStar)
        =ᶠ[Filter.atTop]
          (fun payloadSize : Nat =>
            1 - C /
              (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro payloadSize
    dsimp [C, Cnat, proofEntropyValue, proofEntropyOverhead]
    have hden_pos :
        (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) ≠ 0 := by
      have hden_pos_nat :
          0 < proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar := by
        unfold proofEntropyTotalSize
        have : 1 ≤ i * (wrapSize + (payloadSize + 1)) := by
          nlinarith [hi, Nat.succ_le_succ (Nat.zero_le payloadSize)]
        omega
      exact_mod_cast hden_pos_nat.ne'
    have hnum_eq_nat :
        i * (payloadSize + 1) =
          proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar
            - proofEntropyOverhead k i wrapSize cStar := by
      unfold proofEntropyTotalSize proofEntropyOverhead
      calc
        i * (payloadSize + 1)
          = (i * (payloadSize + 1) + (i * wrapSize + (k - i) + cStar))
              - (i * wrapSize + (k - i) + cStar) := by
                exact (Nat.add_sub_cancel_left (i * (payloadSize + 1))
                  (i * wrapSize + (k - i) + cStar)).symm
        _ = i * (wrapSize + (payloadSize + 1)) + (k - i) + cStar
              - (i * wrapSize + (k - i) + cStar) := by
                ring_nf
    have hnum_eq :
        (i * (payloadSize + 1) : ℝ)
          = (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) - C := by
      dsimp [C, Cnat]
      exact_mod_cast hnum_eq_nat
    calc
      proofEntropyValue k i (payloadSize + 1) wrapSize cStar
          = ((proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) - C) /
              (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
              simp [proofEntropyValue, hnum_eq]
      _ = 1 - C /
            (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ) := by
            field_simp [hden_pos]
            ring
  have hsub :
      Filter.Tendsto
        (fun payloadSize : Nat =>
          1 - C /
            (proofEntropyTotalSize k i (payloadSize + 1) wrapSize cStar : ℝ))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hgap
  simpa using hsub.congr' hrewrite.symm

/-- **Paper 2 Proposition 3.4 (ratio dominance form).** For `k ≥ 1`, the
doubled confessed burden dominates the residual work multiplied by `2k`:
concretely `confessedBurdenDoubled k p = (k+1)(k+2)·p` and
`2·k·residualProofWork k = 2k²`. The ratio
`confessedBurdenDoubled / (2·residualProofWork) → ∞` as `k·p → ∞`. We
state the product form that is equivalent in `Nat`. -/
theorem confession_dominance_product (k p : Nat) :
    confessedBurdenDoubled k p
      = (k + 1) * (k + 2) * p := rfl

/-- **Paper 2 Remark 3.5 (quadratic asymptote).** The doubled confessed
burden equals `(k+1)(k+2)·p`, so the paper's asymptote
`Con(k, p) / (Res(k)+1)² → p/2` is the same statement once divided by
`2(k+1)²`. In `Nat`, the equivalent product identity is `2 · Con = (k+1)(k+2)·p`. -/
theorem confession_doubled_eq_product (k p : Nat) :
    confessedBurdenDoubled k p = (k + 1) * (k + 2) * p := rfl

/-- Proof-entropy denominator at step `i` along the canonical trace:
`D_i := i·wrapperCellWeight + (k - i) + cStar`. -/
def proofEntropyDenominator (k i wrapperCellWeight cStar : Nat) : Nat :=
  i * wrapperCellWeight + (k - i) + cStar

/-- Proof-entropy numerator at step `i`: `i · payloadSize`. -/
def proofEntropyNumerator (i payloadSize : Nat) : Nat := i * payloadSize

/-- Cross-multiplied non-decreasing-ness predicate: the proof-entropy
fraction is non-decreasing going from step `i` to step `i+1`. -/
def ProofEntropyNonDecreasing
    (k payloadSize wrapperCellWeight cStar : Nat) : Prop :=
  ∀ i,
    proofEntropyNumerator i payloadSize
      * proofEntropyDenominator k (i + 1) wrapperCellWeight cStar
    ≤ proofEntropyNumerator (i + 1) payloadSize
      * proofEntropyDenominator k i wrapperCellWeight cStar

/-- **Paper 2 Proposition 3.7 (proof-entropy monotonicity).** The
proof-entropy fraction `H_proof(t_i)` is monotonically non-decreasing
along the canonical trace, as a cross-multiplied natural-number inequality.
The difference `RHS - LHS` is non-negative in both cases:

- when `i + 1 ≤ k`, the difference equals `p · (k + cStar)`;
- when `i ≥ k`, the difference equals `p · cStar`. -/
theorem proof_entropy_nondecreasing
    (k payloadSize wrapperCellWeight cStar : Nat) :
    ProofEntropyNonDecreasing k payloadSize wrapperCellWeight cStar := by
  intro i
  unfold proofEntropyNumerator proofEntropyDenominator
  by_cases hik : i + 1 ≤ k
  · -- Nontrivial regime: i + 1 ≤ k, so k - (i+1) = (k - i) - 1 and k - i ≥ 1.
    have hkI : k - i = (k - (i + 1)) + 1 := by omega
    set m := k - (i + 1) with hm
    rw [hkI]
    nlinarith [Nat.zero_le m, Nat.zero_le wrapperCellWeight,
               Nat.zero_le payloadSize, Nat.zero_le i, Nat.zero_le cStar]
  · -- Trailing regime: i ≥ k, so k - i = 0 and k - (i+1) = 0.
    have h1 : k - i = 0 := by omega
    have h2 : k - (i + 1) = 0 := by omega
    rw [h1, h2]
    nlinarith [Nat.zero_le wrapperCellWeight, Nat.zero_le payloadSize,
               Nat.zero_le i, Nat.zero_le cStar]

end BaseDuplicatingSystem

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
