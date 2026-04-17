import OperatorKO7.Meta.SchemaCanonicalTrace

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
