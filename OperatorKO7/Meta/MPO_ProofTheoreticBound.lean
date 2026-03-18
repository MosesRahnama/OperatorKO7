import OperatorKO7.Meta.MPO_FullStep

/-!
# Proof-theoretic upper bound for the KO7-specialized MPO proof

This file does not change the MPO development. It packages an explicit ordinal
envelope for the existing fixed-signature ranking from `Meta/MPO_FullStep.lean`.

The point is reviewability: the KO7-specialized MPO proof is a direct ordinal
ranking argument on a fixed 7-constructor signature, and its rank lands below
`veblen 7 0`. This gives a concrete upper bound for the proof-strength row in
the paper without claiming a metatheoretic classification for generic path
orders.
-/

namespace OperatorKO7.MPOProofTheoreticBound

open scoped Ordinal
open OperatorKO7.Trace
open OperatorKO7.MetaMPO

/-- Explicit ordinal envelope for the KO7-specialized MPO ranking. -/
@[simp] noncomputable def mpoVeblenBound : Ordinal.{0} := Ordinal.veblen 7 0

lemma mpoVeblenBound_gt_one : (1 : Ordinal.{0}) < mpoVeblenBound := by
  simpa [mpoVeblenBound] using
    (veblen_gt_one_of_pos (k := (7 : Ordinal.{0})) (x := 0)
      (by exact_mod_cast (show 0 < (7 : Nat) by decide)))

lemma mpoVeblenBound_fixed :
    (ω : Ordinal.{0}) ^ mpoVeblenBound = mpoVeblenBound := by
  simpa [mpoVeblenBound] using
    (veblen_fixed_of_pos (k := (7 : Ordinal.{0})) (x := 0)
      (by exact_mod_cast (show 0 < (7 : Nat) by decide)))

lemma mpoVeblenBound_isSuccLimit :
    Order.IsSuccLimit mpoVeblenBound := by
  simpa [mpoVeblenBound] using
    (veblen_isSuccLimit_of_pos (k := (7 : Ordinal.{0})) (x := 0)
      (by exact_mod_cast (show 0 < (7 : Nat) by decide)))

lemma rank_lt_seven (s : Sym) : rank s < 7 := by
  cases s <;> decide

lemma rank_lt_seven_ord (s : Sym) : ((rank s : Nat) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
  exact_mod_cast rank_lt_seven s

lemma veblen_lt_mpoVeblenBound_of_rank_lt
    {k p : Ordinal.{0}} (hk : k < 7) (hp : p < mpoVeblenBound) :
    Ordinal.veblen k p < mpoVeblenBound := by
  dsimp [mpoVeblenBound]
  exact (Ordinal.veblen_lt_veblen_iff).2
    (Or.inr (Or.inl ⟨hk, by simpa [mpoVeblenBound] using hp⟩))

/-- Every KO7-specialized MPO ordinal rank lies below the fixed envelope
`veblen 7 0`. -/
theorem mpoOrd_lt_mpoVeblenBound : ∀ t : Trace, mpoOrd t < mpoVeblenBound
  | void => by
      have hzero : (0 : Ordinal.{0}) < mpoVeblenBound := by
        have h0 : (0 : Ordinal.{0}) < 1 := by
          exact_mod_cast (show 0 < (1 : Nat) by decide)
        exact h0.trans mpoVeblenBound_gt_one
      have hk : ((rank (sym void)) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.void : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.void
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hzero)
  | delta t => by
      have hpayload : Order.succ (mpoOrd t) < mpoVeblenBound := by
        exact mpoVeblenBound_isSuccLimit.succ_lt (mpoOrd_lt_mpoVeblenBound t)
      have hk : ((rank (sym (delta t))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.delta : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.delta
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | integrate t => by
      have hpayload : Order.succ (mpoOrd t) < mpoVeblenBound := by
        exact mpoVeblenBound_isSuccLimit.succ_lt (mpoOrd_lt_mpoVeblenBound t)
      have hk : ((rank (sym (integrate t))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.integrate : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.integrate
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | merge a b => by
      have hpayload :
          pairPayload (mpoOrd a) (mpoOrd b) < mpoVeblenBound := by
        exact pairPayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound a)
          (mpoOrd_lt_mpoVeblenBound b)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (merge a b))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.merge : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.merge
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | app a b => by
      have hpayload :
          pairPayload (mpoOrd a) (mpoOrd b) < mpoVeblenBound := by
        exact pairPayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound a)
          (mpoOrd_lt_mpoVeblenBound b)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (app a b))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.app : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.app
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | recΔ b s n => by
      have hpayload :
          triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n) < mpoVeblenBound := by
        exact triplePayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound b)
          (mpoOrd_lt_mpoVeblenBound s)
          (mpoOrd_lt_mpoVeblenBound n)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (recΔ b s n))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.recΔ : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.recΔ
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | eqW a b => by
      have hpayload :
          pairPayload (mpoOrd a) (mpoOrd b) < mpoVeblenBound := by
        exact pairPayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound a)
          (mpoOrd_lt_mpoVeblenBound b)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (eqW a b))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.eqW : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.eqW
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)

/-- The fixed-signature MPO proof is witnessed by an ordinal ranking into the
initial segment below `veblen 7 0`. -/
theorem wf_StepRev_mpo_below_veblen7 :
    ∃ ρ : Trace → Ordinal.{0},
      (∀ t, ρ t < mpoVeblenBound) ∧
      (∀ {a b : Trace}, Step a b → ρ b < ρ a) := by
  refine ⟨mpoOrd, ?_, ?_⟩
  · intro t
    exact mpoOrd_lt_mpoVeblenBound t
  · intro a b hstep
    exact mpoOrd_strict_of_mpo (mpo_orients_step hstep)

end OperatorKO7.MPOProofTheoreticBound
