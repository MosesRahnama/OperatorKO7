import OperatorKO7.Meta.BarrierWitness
import OperatorKO7.Meta.PumpedBarrierClasses

/-!
# Small synthesis-oracle layer for direct barrier classes

This module packages the existing constructive barrier witnesses as a small
oracle interface. The intended use is bounded refinement: a candidate direct
measure is submitted to the oracle, which returns a concrete certificate triple.
Any refinement that succeeds on that triple must change at least one of the two
evaluated sides there.

This is intentionally not a synthesis engine. It is a thin certified API over
the current additive, transparent-compositional, and affine witness extractors,
plus an automatic affine-with-pump instance.
-/

namespace OperatorKO7.StepDuplicating
open StepDuplicatingSchema

/-- A small oracle interface returning a concrete barrier certificate for a
candidate direct measure family. -/
structure SynthesisOracle (S : StepDuplicatingSchema) where
  Candidate : Type
  eval : Candidate → S.T → Nat
  certify : (cand : Candidate) → BarrierCertificate S (eval cand)

/-- Candidate package for the transparent-compositional extractor. -/
structure TransparentCandidate (S : StepDuplicatingSchema) where
  measure : CompositionalMeasure S
  transparent : measure.c_succ measure.c_base = measure.c_base

/-- Candidate package for the affine extractor with an explicit pump term. -/
structure AffineOracleCandidate (S : StepDuplicatingSchema) where
  measure : AffineMeasure S
  pumpTerm : S.T
  pump_ok :
    measure.recur_counter * (measure.succ_bias + measure.succ_scale * measure.c_base) ≤
      measure.eval pumpTerm

/-- Source-side value at a certificate triple. -/
def certificateLhs {S : StepDuplicatingSchema} {eval : S.T → Nat}
    (cert : BarrierCertificate S eval) : Nat :=
  eval (S.wrap cert.s (S.recur cert.b cert.s cert.n))

/-- Target-side value at a certificate triple. -/
def certificateRhs {S : StepDuplicatingSchema} {eval : S.T → Nat}
    (cert : BarrierCertificate S eval) : Nat :=
  eval (S.recur cert.b cert.s (S.succ cert.n))

/-- A refinement avoids the oracle certificate only by changing at least one of
the two certificate-side values. -/
def changesAtCertificate {S : StepDuplicatingSchema}
    {eval₀ eval₁ : S.T → Nat} (cert : BarrierCertificate S eval₀) : Prop :=
  eval₁ (S.wrap cert.s (S.recur cert.b cert.s cert.n)) ≠ certificateLhs cert ∨
    eval₁ (S.recur cert.b cert.s (S.succ cert.n)) ≠ certificateRhs cert

/-- If a refinement succeeds on the returned certificate triple, then at least
one side of the certificate valuation must change. -/
theorem successful_refinement_changes_certificate
    {S : StepDuplicatingSchema} {eval₀ eval₁ : S.T → Nat}
    (cert : BarrierCertificate S eval₀)
    (hgood :
      eval₁ (S.wrap cert.s (S.recur cert.b cert.s cert.n)) <
        eval₁ (S.recur cert.b cert.s (S.succ cert.n))) :
    changesAtCertificate (eval₁ := eval₁) cert := by
  by_cases hlhs :
      eval₁ (S.wrap cert.s (S.recur cert.b cert.s cert.n)) =
        certificateLhs cert
  · by_cases hrhs :
        eval₁ (S.recur cert.b cert.s (S.succ cert.n)) =
          certificateRhs cert
    · exfalso
      apply cert.fails
      simpa [certificateLhs, certificateRhs, hlhs, hrhs] using hgood
    · exact Or.inr hrhs
  · exact Or.inl hlhs

/-- Additive direct-measure oracle. -/
def additiveSynthesisOracle (S : StepDuplicatingSchema) : SynthesisOracle S where
  Candidate := AdditiveMeasure S
  eval M := M.eval
  certify M := additive_witness M

/-- Transparent-compositional direct-measure oracle. -/
def transparentSynthesisOracle (S : StepDuplicatingSchema) : SynthesisOracle S where
  Candidate := TransparentCandidate S
  eval cand := cand.measure.eval
  certify cand := compositional_witness cand.measure cand.transparent

/-- Affine direct-measure oracle with an explicit pump witness. -/
def affineSynthesisOracle (S : StepDuplicatingSchema) : SynthesisOracle S where
  Candidate := AffineOracleCandidate S
  eval cand := cand.measure.eval
  certify cand := affine_witness cand.measure cand.pumpTerm cand.pump_ok

/-- The strengthened affine pumped subclass automatically supplies an oracle
certificate by choosing the corresponding successor or wrapper pump term. -/
def affineWithPumpSynthesisOracle (S : StepDuplicatingSchema) : SynthesisOracle S where
  Candidate := AffineMeasureWithPump S
  eval M := M.eval
  certify M := by
    let T := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
    if hsucc : 1 ≤ M.succ_bias ∧ 1 ≤ M.succ_scale then
      exact
        affine_witness M.toAffineMeasure (succIter S T)
          (by
            simpa [T] using
              eval_succIter_ge M.toAffineMeasure hsucc.1 hsucc.2 T)
    else
      have hwrap : 1 ≤ M.wrap_const + M.wrap_right * M.c_base := by
        rcases M.has_pump with hsucc' | hwrap
        · exact False.elim (hsucc hsucc')
        · exact hwrap
      exact
        affine_witness M.toAffineMeasure (wrapIter S T)
          (by
            simpa [T] using
              eval_wrapIter_ge_affine M.toAffineMeasure hwrap T)

end OperatorKO7.StepDuplicating
