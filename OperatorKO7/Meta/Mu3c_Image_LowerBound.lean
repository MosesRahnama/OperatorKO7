import OperatorKO7.Meta.DM_OrderType_LowerBound

namespace OperatorKO7.MetaDM

open Ordinal
open OperatorKO7 Trace
open OperatorKO7.MetaCM
open MetaSN_DM
open MetaSN_KO7

/-- Canonical descending multiset payload `{n+1, n, ..., 1}` used to witness large
realized `mu3c` values. -/
@[simp] def kappaTower : Nat → Multiset Nat
  | 0 => ({1} : Multiset Nat)
  | n + 1 => (n + 2) ::ₘ kappaTower n

/-- Root-side payload tower with strictly increasing recursion depth. -/
@[simp] def payloadTower : Nat → Trace
  | 0 => recΔ void void void
  | n + 1 => recΔ void void (payloadTower n)

/-- Flagged tower landing in the `δ = 1` block while preserving the same high payload. -/
@[simp] def flaggedTower (n : Nat) : Trace :=
  recΔ (payloadTower n) void (delta void)

@[simp] theorem weight_payloadTower (n : Nat) :
    weight (payloadTower n) = n + 1 := by
  induction n with
  | zero =>
      simp [payloadTower, weight]
  | succ n ih =>
      simp [payloadTower, weight, ih]

@[simp] theorem kappaM_payloadTower (n : Nat) :
    kappaM (payloadTower n) = kappaTower n := by
  induction n with
  | zero =>
      simp [payloadTower, kappaTower, kappaM]
  | succ n ih =>
      simp [payloadTower, kappaTower, kappaM, ih, weight_payloadTower]

@[simp] theorem tau_payloadTower (n : Nat) :
    tau (payloadTower n) = 3 * (n + 1) := by
  induction n with
  | zero =>
      simp [payloadTower, tau]
  | succ n ih =>
      simp [payloadTower, tau, ih]
      omega

theorem payloadTower_ne_delta : ∀ n : Nat, ∀ t : Trace, payloadTower n ≠ delta t
  | 0, t, h => by cases h
  | _ + 1, t, h => by cases h

@[simp] theorem deltaFlag_payloadTower (n : Nat) :
    deltaFlag (payloadTower n) = 0 := by
  unfold deltaFlag
  cases n with
  | zero =>
      simp [payloadTower]
  | succ n =>
      simp [payloadTower, payloadTower_ne_delta]

@[simp] theorem kappaM_flaggedTower (n : Nat) :
    kappaM (flaggedTower n) = (1 ::ₘ kappaTower n) := by
  simp [flaggedTower, kappaM_payloadTower, kappaM]

@[simp] theorem tau_flaggedTower (n : Nat) :
    tau (flaggedTower n) = 3 * (n + 2) := by
  simp [flaggedTower, tau_payloadTower, tau]
  omega

@[simp] theorem deltaFlag_flaggedTower (n : Nat) :
    deltaFlag (flaggedTower n) = 1 := by
  simp [flaggedTower, deltaFlag]

private theorem mem_kappaTower_lt (n : Nat) :
    ∀ m ∈ kappaTower n, m < n + 2 := by
  intro m hm
  induction n generalizing m with
  | zero =>
      simp [kappaTower] at hm
      rcases hm with rfl
      omega
  | succ n ih =>
      simp [kappaTower] at hm
      rcases hm with rfl | hm
      · omega
      · exact lt_trans (ih _ hm) (by omega)

@[simp] theorem dmOrdEmbed_kappaTower_succ (n : Nat) :
    dmOrdEmbed (kappaTower (n + 1)) =
      (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) + dmOrdEmbed (kappaTower n) := by
  have hlt : ∀ m ∈ kappaTower n, m < n + 2 := mem_kappaTower_lt n
  calc
    dmOrdEmbed (kappaTower (n + 1))
        = dmOrdEmbed (Multiset.replicate 1 (n + 2) + kappaTower n) := by
            simp [kappaTower]
    _ = (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) * (1 : Ordinal) +
          dmOrdEmbed (kappaTower n) := by
            simpa using dmOrdEmbed_replicate_add_of_all_lt (z := n + 2) (c := 1) hlt
    _ = (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) + dmOrdEmbed (kappaTower n) := by
            simp

theorem opow_le_dmOrdEmbed_kappaTower (n : Nat) :
    (ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal) ≤ dmOrdEmbed (kappaTower n) := by
  induction n with
  | zero =>
      simp [kappaTower, dmOrdEmbed_singleton]
  | succ n ih =>
      rw [dmOrdEmbed_kappaTower_succ]
      exact Ordinal.le_add_right _ _

private theorem opow_mul_opow_nat (n : Nat) :
    (ω : Ordinal) * ((ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal)) =
      (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) := by
  calc
    (ω : Ordinal) * ((ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal))
        = (ω : Ordinal) ^ (1 : Ordinal) * ((ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal)) := by
            simp [Ordinal.opow_one]
    _ = (ω : Ordinal) ^ ((1 : Ordinal) + ((n + 1 : Nat) : Ordinal)) := by
          simpa using (Ordinal.opow_add (ω : Ordinal) (1 : Ordinal) ((n + 1 : Nat) : Ordinal)).symm
    _ = (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) := by
      have hnat : (1 : Ordinal) + ((n + 1 : Nat) : Ordinal) = ((n + 2 : Nat) : Ordinal) := by
        exact_mod_cast (by omega : 1 + (n + 1) = n + 2)
      exact congrArg (fun o : Ordinal => (ω : Ordinal) ^ o) hnat

@[simp] theorem mu3c_payloadTower (n : Nat) :
    mu3c (payloadTower n) = (0, (kappaTower n, 3 * (n + 1))) := by
  rw [mu3c, deltaFlag_payloadTower, kappaM_payloadTower, tau_payloadTower]

@[simp] theorem mu3c_flaggedTower (n : Nat) :
    mu3c (flaggedTower n) = (1, (1 ::ₘ kappaTower n, 3 * (n + 2))) := by
  rw [mu3c, deltaFlag_flaggedTower, kappaM_flaggedTower, tau_flaggedTower]

/-- Realized lower-bound family inside the `δ = 0` block of `mu3c`. -/
theorem payloadTower_mu3c_lower (n : Nat) :
    (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤
      lex3cToOrd (mu3c (payloadTower n)) := by
  have hκ : (ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal) ≤
      dmOrdEmbed (kappaM (payloadTower n)) := by
    simpa [kappaM_payloadTower] using opow_le_dmOrdEmbed_kappaTower n
  have hmul :
      (ω : Ordinal) * ((ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal)) ≤
        (ω : Ordinal) * dmOrdEmbed (kappaM (payloadTower n)) := by
    exact mul_le_mul_left' hκ (ω : Ordinal)
  have hle :
      (ω : Ordinal) * dmOrdEmbed (kappaM (payloadTower n)) ≤
        lexDMToOrd (kappaM (payloadTower n), tau (payloadTower n)) := by
    simp [lexDMToOrd]
  calc
    (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal)
        = (ω : Ordinal) * ((ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal)) := by
            rw [opow_mul_opow_nat]
    _ ≤ (ω : Ordinal) * dmOrdEmbed (kappaM (payloadTower n)) := hmul
    _ ≤ lexDMToOrd (kappaM (payloadTower n), tau (payloadTower n)) := hle
    _ = lex3cToOrd (mu3c (payloadTower n)) := by
          rw [mu3c_payloadTower]
          simp [lex3cToOrd, lexDMToOrd]

/-- Realized lower-bound family inside the `δ = 1` block of `mu3c`. -/
theorem flaggedTower_mu3c_lower (n : Nat) :
    (ω : Ordinal) ^ (ω : Ordinal) + (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤
      lex3cToOrd (mu3c (flaggedTower n)) := by
  have hκbase :
      (ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal) ≤
        dmOrdEmbed (kappaTower n) := opow_le_dmOrdEmbed_kappaTower n
  have hκ :
      (ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal) ≤
        dmOrdEmbed (kappaM (flaggedTower n)) := by
    have hmono : kappaTower n ≤ kappaM (flaggedTower n) := by
      simpa [kappaM_flaggedTower, add_comm] using
        (Multiset.le_add_right (kappaTower n) ({1} : Multiset Nat))
    exact le_trans hκbase (dmOrdEmbed_mono hmono)
  have hmul :
      (ω : Ordinal) * ((ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal)) ≤
        (ω : Ordinal) * dmOrdEmbed (kappaM (flaggedTower n)) := by
    exact mul_le_mul_left' hκ (ω : Ordinal)
  have hle :
      (ω : Ordinal) * dmOrdEmbed (kappaM (flaggedTower n)) ≤
        lexDMToOrd (kappaM (flaggedTower n), tau (flaggedTower n)) := by
    simp [lexDMToOrd]
  have hinner :
      (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤
        lexDMToOrd (kappaM (flaggedTower n), tau (flaggedTower n)) := by
    calc
      (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal)
          = (ω : Ordinal) * ((ω : Ordinal) ^ ((n + 1 : Nat) : Ordinal)) := by
              rw [opow_mul_opow_nat]
      _ ≤ (ω : Ordinal) * dmOrdEmbed (kappaM (flaggedTower n)) := hmul
      _ ≤ lexDMToOrd (kappaM (flaggedTower n), tau (flaggedTower n)) := hle
  have hleft :
      (ω : Ordinal) ^ (ω : Ordinal) + (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤
        (ω : Ordinal) ^ (ω : Ordinal) +
          lexDMToOrd (kappaM (flaggedTower n), tau (flaggedTower n)) := by
    exact add_le_add_left hinner ((ω : Ordinal) ^ (ω : Ordinal))
  have hleftRaw :
      (ω : Ordinal) ^ (ω : Ordinal) + (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤
        (ω : Ordinal) ^ (ω : Ordinal) +
          lexDMToOrd (1 ::ₘ kappaTower n, 3 + 3 * (n + 1)) := by
    simpa [kappaM_flaggedTower, flaggedTower, tau_payloadTower, tau] using hleft
  have hleft' :
      (ω : Ordinal) ^ (ω : Ordinal) + (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤
        (ω : Ordinal) ^ (ω : Ordinal) +
          lexDMToOrd (1 ::ₘ kappaTower n, 3 * (n + 2)) := by
    have htau : 3 + 3 * (n + 1) = 3 * (n + 2) := by omega
    simpa [lexDMToOrd, htau] using hleftRaw
  rw [mu3c_flaggedTower]
  simpa [lex3cToOrd, lexDMToOrd] using hleft'

/-- The `δ = 0` family stays inside the first `ω^ω` block. -/
theorem payloadTower_mu3c_lt_block_cap (n : Nat) :
    lex3cToOrd (mu3c (payloadTower n)) < (ω : Ordinal) ^ (ω : Ordinal) := by
  rw [mu3c_payloadTower]
  simpa [kappaM_payloadTower, tau_payloadTower, lex3cToOrd] using
    (lexDMToOrd_lt_opow_omega (kappaM (payloadTower n), tau (payloadTower n)))

/-- The `δ = 1` family stays below the global `ω^ω · 2` cap. -/
theorem flaggedTower_mu3c_lt_two_block_cap (n : Nat) :
    lex3cToOrd (mu3c (flaggedTower n)) <
      ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) := by
  exact lex3c_order_type_bound (flaggedTower n)

/-- Existential lower-bound family for the first `mu3c` block. -/
theorem mu3c_lower_family_block0 (n : Nat) :
    ∃ t : Trace,
      (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤ lex3cToOrd (mu3c t) ∧
      lex3cToOrd (mu3c t) < (ω : Ordinal) ^ (ω : Ordinal) := by
  exact ⟨payloadTower n, payloadTower_mu3c_lower n, payloadTower_mu3c_lt_block_cap n⟩

/-- Existential lower-bound family for the second `mu3c` block. -/
theorem mu3c_lower_family_block1 (n : Nat) :
    ∃ t : Trace,
      (ω : Ordinal) ^ (ω : Ordinal) + (ω : Ordinal) ^ ((n + 2 : Nat) : Ordinal) ≤
        lex3cToOrd (mu3c t) ∧
      lex3cToOrd (mu3c t) < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) := by
  exact ⟨flaggedTower n, flaggedTower_mu3c_lower n, flaggedTower_mu3c_lt_two_block_cap n⟩

end OperatorKO7.MetaDM
