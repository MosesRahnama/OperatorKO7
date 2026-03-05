import OperatorKO7.Meta.SafeStep_Ctx
import Mathlib.Logic.Relation

/-!
Context-closed strong normalization for the KO7 safe fragment.

This module proves unconditional well-foundedness of `SafeStepCtxRev` (the
reverse of the partial context closure `SafeStepCtx`) via a direct numeric
interpretation `ctxFuel` (exponential weights). The key theorem is
`wf_SafeStepCtxRev : WellFounded (fun a b => SafeStepCtx b a)`.

Infrastructure:
- Reusable accessibility/transport lemmas for the reverse context relation
  `SafeStepCtxRev a b :≡ SafeStepCtx b a`.
- Projections of accessibility through constructor embeddings
  (`recB`, `recS`, `recN`, `appL/R`, `mergeL/R`, `integrate`).
- `Acc` pullback along `InvImage`.

The unconditional proof (no `sorry`) works by showing `ctxFuel` strictly
decreases on every `SafeStepCtx` step (`ctxFuel_decreases_ctx`), reducing
well-foundedness to `Nat.lt`.
-/

open OperatorKO7 Trace

namespace MetaSN_KO7

/-- Reverse relation for context-closed safe steps. -/
def SafeStepCtxRev : Trace → Trace → Prop := fun a b => SafeStepCtx b a

/-- Pull accessibility back along a subrelation. -/
lemma Acc.of_subrelation {α : Sort _} {r s : α → α → Prop}
    (hsub : ∀ {a b}, r a b → s a b) {a : α} (ha : Acc s a) : Acc r a := by
  induction ha with
  | intro a hs ih =>
      refine Acc.intro a ?_
      intro b hb
      exact ih b (hsub hb)

/-- Pull accessibility back through an `InvImage` equality witness. -/
lemma acc_invImage_of_acc
    {α β : Sort _} {r : β → β → Prop} (f : α → β)
    {b0 : β} (hb0 : Acc r b0) :
    ∀ {a : α}, f a = b0 → Acc (InvImage r f) a := by
  induction hb0 with
  | intro b0 hpred ih =>
      intro a ha
      refine Acc.intro a ?_
      intro a' ha'
      have hb' : r (f a') b0 := by
        simpa [InvImage, ha] using ha'
      exact ih (f a') hb' (a := a') rfl

/-! ### Constructor-lifted subrelations -/

lemma sub_integrate :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => integrate t) x y := by
  intro x y hxy
  exact SafeStepCtx.integrate hxy

lemma sub_mergeL (b : Trace) :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => merge t b) x y := by
  intro x y hxy
  exact SafeStepCtx.mergeL hxy

lemma sub_mergeR (a : Trace) :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => merge a t) x y := by
  intro x y hxy
  exact SafeStepCtx.mergeR hxy

lemma sub_appL (b : Trace) :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => app t b) x y := by
  intro x y hxy
  exact SafeStepCtx.appL hxy

lemma sub_appR (a : Trace) :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => app a t) x y := by
  intro x y hxy
  exact SafeStepCtx.appR hxy

lemma sub_recB (s n : Trace) :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => recΔ t s n) x y := by
  intro x y hxy
  exact SafeStepCtx.recB hxy

lemma sub_recS (b n : Trace) :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => recΔ b t n) x y := by
  intro x y hxy
  exact SafeStepCtx.recS hxy

lemma sub_recN (b s : Trace) :
    ∀ {x y : Trace},
      SafeStepCtxRev x y →
      InvImage SafeStepCtxRev (fun t => recΔ b s t) x y := by
  intro x y hxy
  exact SafeStepCtx.recN hxy

/-! ### Accessibility projections through constructors -/

lemma acc_integrate_arg_of_acc {t : Trace}
    (h : Acc SafeStepCtxRev (integrate t)) :
    Acc SafeStepCtxRev t := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => integrate x)) t :=
    acc_invImage_of_acc (f := fun x => integrate x) h rfl
  exact Acc.of_subrelation sub_integrate hInv

lemma acc_merge_left_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (merge a b)) :
    Acc SafeStepCtxRev a := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => merge x b)) a :=
    acc_invImage_of_acc (f := fun x => merge x b) h rfl
  exact Acc.of_subrelation (sub_mergeL b) hInv

lemma acc_merge_right_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (merge a b)) :
    Acc SafeStepCtxRev b := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => merge a x)) b :=
    acc_invImage_of_acc (f := fun x => merge a x) h rfl
  exact Acc.of_subrelation (sub_mergeR a) hInv

lemma acc_app_left_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (app a b)) :
    Acc SafeStepCtxRev a := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => app x b)) a :=
    acc_invImage_of_acc (f := fun x => app x b) h rfl
  exact Acc.of_subrelation (sub_appL b) hInv

lemma acc_app_right_of_acc {a b : Trace}
    (h : Acc SafeStepCtxRev (app a b)) :
    Acc SafeStepCtxRev b := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => app a x)) b :=
    acc_invImage_of_acc (f := fun x => app a x) h rfl
  exact Acc.of_subrelation (sub_appR a) hInv

lemma acc_rec_base_of_acc {b s n : Trace}
    (h : Acc SafeStepCtxRev (recΔ b s n)) :
    Acc SafeStepCtxRev b := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => recΔ x s n)) b :=
    acc_invImage_of_acc (f := fun x => recΔ x s n) h rfl
  exact Acc.of_subrelation (sub_recB s n) hInv

lemma acc_rec_step_of_acc {b s n : Trace}
    (h : Acc SafeStepCtxRev (recΔ b s n)) :
    Acc SafeStepCtxRev s := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => recΔ b x n)) s :=
    acc_invImage_of_acc (f := fun x => recΔ b x n) h rfl
  exact Acc.of_subrelation (sub_recS b n) hInv

lemma acc_rec_arg_of_acc {b s n : Trace}
    (h : Acc SafeStepCtxRev (recΔ b s n)) :
    Acc SafeStepCtxRev n := by
  have hInv : Acc (InvImage SafeStepCtxRev (fun x => recΔ b s x)) n :=
    acc_invImage_of_acc (f := fun x => recΔ b s x) h rfl
  exact Acc.of_subrelation (sub_recN b s) hInv

/-! ### Constructor closure lemmas (forward-step accessibility) -/

theorem acc_ctx_void : Acc SafeStepCtxRev void := by
  refine Acc.intro _ ?_
  intro y hy
  cases hy
  case root hs =>
    have hnone : safeStepWitness? void = none := by simp [safeStepWitness?]
    exact (safeStepWitness?_none_no_step hnone y hs).elim

theorem acc_ctx_delta (t : Trace) : Acc SafeStepCtxRev (delta t) := by
  refine Acc.intro _ ?_
  intro y hy
  cases hy
  case root hs =>
    have hnone : safeStepWitness? (delta t) = none := by simp [safeStepWitness?]
    exact (safeStepWitness?_none_no_step hnone y hs).elim

theorem acc_ctx_app_of_acc :
    ∀ a, Acc SafeStepCtxRev a →
    ∀ b, Acc SafeStepCtxRev b →
      Acc SafeStepCtxRev (app a b) := by
  intro a ha
  induction ha with
  | intro a hpredA ihA =>
      intro b hb
      induction hb with
      | intro b hpredB ihB =>
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs =>
              have hnone : safeStepWitness? (app a b) = none := by simp [safeStepWitness?]
              exact (safeStepWitness?_none_no_step hnone y hs).elim
          | appL hA => exact ihA _ hA b hbAcc
          | appR hB => exact ihB _ hB

theorem acc_ctx_merge_of_acc :
    ∀ a, Acc SafeStepCtxRev a →
    ∀ b, Acc SafeStepCtxRev b →
      Acc SafeStepCtxRev (merge a b) := by
  intro a ha
  induction ha with
  | intro a hpredA ihA =>
      intro b hb
      induction hb with
      | intro b hpredB ihB =>
          have haAcc : Acc SafeStepCtxRev a := Acc.intro a hpredA
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs =>
              cases hs with
              | R_merge_void_left t _ => simpa using hbAcc
              | R_merge_void_right t _ => simpa using haAcc
              | R_merge_cancel t _ _ => simpa using haAcc
          | mergeL hA => exact ihA _ hA b hbAcc
          | mergeR hB => exact ihB _ hB

theorem acc_ctx_integrate_of_acc
    (t : Trace) (ht : Acc SafeStepCtxRev t) :
    Acc SafeStepCtxRev (integrate t) := by
  induction ht with
  | intro t hpredT ihT =>
      refine Acc.intro _ ?_
      intro y hy
      cases hy with
      | root hs =>
          cases hs with
          | R_int_delta u =>
              simpa using acc_ctx_void
      | integrate hT => exact ihT _ hT

theorem acc_ctx_eqW_of_acc
    (a b : Trace) (ha : Acc SafeStepCtxRev a) (hb : Acc SafeStepCtxRev b) :
    Acc SafeStepCtxRev (eqW a b) := by
  refine Acc.intro _ ?_
  intro y hy
  cases hy with
  | root hs =>
      cases hs with
      | R_eq_refl a h0 =>
          simpa using acc_ctx_void
      | R_eq_diff a b hne =>
          exact acc_ctx_integrate_of_acc (merge a b) (acc_ctx_merge_of_acc a ha b hb)

theorem acc_ctx_rec_void_of_acc :
    ∀ b, Acc SafeStepCtxRev b →
    ∀ s, Acc SafeStepCtxRev s →
      Acc SafeStepCtxRev (recΔ b s void) := by
  intro b hb
  induction hb with
  | intro b hpredB ihB =>
      intro s hs
      induction hs with
      | intro s hpredS ihS =>
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          have hsAcc : Acc SafeStepCtxRev s := Acc.intro s hpredS
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs0 =>
              cases hs0 with
              | R_rec_zero _ _ _ =>
                  simpa using hbAcc
          | recB hB =>
              exact ihB _ hB s hsAcc
          | recS hS =>
              exact ihS _ hS
          | recN hN =>
              cases hN with
              | root hsVoid =>
                  have hnone : safeStepWitness? void = none := by simp [safeStepWitness?]
                  exact (safeStepWitness?_none_no_step hnone _ hsVoid).elim

theorem acc_ctx_rec_delta_of_acc
    (n : Trace)
    (hrecArg : ∀ b s,
      Acc SafeStepCtxRev b →
      Acc SafeStepCtxRev s →
      Acc SafeStepCtxRev (recΔ b s n)) :
    ∀ b, Acc SafeStepCtxRev b →
    ∀ s, Acc SafeStepCtxRev s →
      Acc SafeStepCtxRev (recΔ b s (delta n)) := by
  intro b hb
  induction hb with
  | intro b hpredB ihB =>
      intro s hs
      induction hs with
      | intro s hpredS ihS =>
          have hbAcc : Acc SafeStepCtxRev b := Acc.intro b hpredB
          have hsAcc : Acc SafeStepCtxRev s := Acc.intro s hpredS
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | root hs0 =>
              cases hs0 with
              | R_rec_succ _ _ _ =>
                  exact acc_ctx_app_of_acc s hsAcc
                    (recΔ b s n) (hrecArg b s hbAcc hsAcc)
          | recB hB =>
              exact ihB _ hB s hsAcc
          | recS hS =>
              exact ihS _ hS
          | recN hN =>
              cases hN with
              | root hsDelta =>
                  have hnone : safeStepWitness? (delta n) = none := by simp [safeStepWitness?]
                  exact (safeStepWitness?_none_no_step hnone _ hsDelta).elim

/-- Remaining recursor-specific obligation for full context-closure SN. -/
def RecCtxAccObligation : Prop :=
  ∀ (b s n : Trace),
    Acc SafeStepCtxRev b →
    Acc SafeStepCtxRev s →
    Acc SafeStepCtxRev n →
    Acc SafeStepCtxRev (recΔ b s n)

/-- If the recursor obligation holds, then all traces are accessible for `SafeStepCtxRev`. -/
theorem acc_ctx_all_of_rec_obligation
    (hrec : RecCtxAccObligation) :
    ∀ t : Trace, Acc SafeStepCtxRev t := by
  intro t
  induction t with
  | void =>
      exact acc_ctx_void
  | delta t _ =>
      exact acc_ctx_delta t
  | integrate t iht =>
      exact acc_ctx_integrate_of_acc t iht
  | merge a b iha ihb =>
      exact acc_ctx_merge_of_acc a iha b ihb
  | app a b iha ihb =>
      exact acc_ctx_app_of_acc a iha b ihb
  | recΔ b s n ihb ihs ihn =>
      exact hrec b s n ihb ihs ihn
  | eqW a b iha ihb =>
      exact acc_ctx_eqW_of_acc a b iha ihb

/-- Conditional well-foundedness: reduces `wf_SafeStepCtxRev` to `RecCtxAccObligation`. -/
theorem wf_SafeStepCtxRev_of_rec_obligation
    (hrec : RecCtxAccObligation) :
    WellFounded (fun a b : Trace => SafeStepCtx b a) := by
  refine ⟨?_⟩
  intro t
  simpa [SafeStepCtxRev] using acc_ctx_all_of_rec_obligation hrec t

/-
Unconditional context-closure SN via a direct numeric interpretation.

`ctxFuel` is chosen to be strictly monotone under all context constructors and
to strictly decrease on every safe root rule; this yields strict decrease for
`SafeStepCtx` by induction on the context derivation.
-/

@[simp] def ctxFuel : Trace → Nat
| void            => 0
| delta t         => 2 ^ (ctxFuel t + 1)
| integrate t     => ctxFuel t + 1
| merge a b       => ctxFuel a + ctxFuel b + 2
| app a b         => ctxFuel a + ctxFuel b + 1
| recΔ b s n      => 2 ^ (ctxFuel n + ctxFuel s + 5) + ctxFuel b + 1
| eqW a b         => ctxFuel a + ctxFuel b + 4

lemma one_lt_two_nat : 1 < (2 : Nat) := by decide

lemma lt_two_pow_succ (n : Nat) : n < 2 ^ (n + 1) := by
  have h : n + 1 < 2 ^ (n + 1) := Nat.lt_pow_self (n := n + 1) one_lt_two_nat
  exact lt_trans (Nat.lt_succ_self n) h

lemma ctxFuel_rec_succ_drop (b s n : Trace) :
    ctxFuel (app s (recΔ b s n)) < ctxFuel (recΔ b s (delta n)) := by
  set mb := ctxFuel b
  set ms := ctxFuel s
  set mn := ctxFuel n
  let A : Nat := mn + ms + 5
  let B : Nat := 2 ^ (mn + 1) + ms + 5
  have hExpA_lt : A < B := by
    have hmn : mn < 2 ^ (mn + 1) := lt_two_pow_succ mn
    have h₁ : mn + ms < 2 ^ (mn + 1) + ms := Nat.add_lt_add_right hmn ms
    exact Nat.add_lt_add_right h₁ 5
  have hpowA_lt : 2 ^ A < 2 ^ B :=
    Nat.pow_lt_pow_right one_lt_two_nat hExpA_lt
  have hms_pow : ms + 1 < 2 ^ (ms + 1) := Nat.lt_pow_self (n := ms + 1) one_lt_two_nat
  have hExpSmall_le : ms + 1 ≤ A := by
    unfold A
    omega
  have hpowSmall_le : 2 ^ (ms + 1) ≤ 2 ^ A :=
    Nat.pow_le_pow_right (by decide : 2 > 0) hExpSmall_le
  have hms_lt_powA : ms + 1 < 2 ^ A := lt_of_lt_of_le hms_pow hpowSmall_le
  have hsum_lt : 2 ^ A + (ms + 1) < 2 ^ A + 2 ^ A := by
    exact Nat.add_lt_add_left hms_lt_powA (2 ^ A)
  have hdouble : 2 ^ A + 2 ^ A = 2 ^ (A + 1) := by
    calc
      2 ^ A + 2 ^ A = 2 * 2 ^ A := by simp [Nat.two_mul]
      _ = 2 ^ (A + 1) := by simp [Nat.pow_succ, Nat.mul_comm]
  have hA1_lt_B : A + 1 < B := by
    have hmn1 : mn + 1 < 2 ^ (mn + 1) := Nat.lt_pow_self (n := mn + 1) one_lt_two_nat
    have h₁ : mn + 1 + (ms + 5) < 2 ^ (mn + 1) + (ms + 5) := Nat.add_lt_add_right hmn1 (ms + 5)
    have : mn + ms + 6 < 2 ^ (mn + 1) + ms + 5 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁
    simpa [A, B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hpowA1_lt_B : 2 ^ (A + 1) < 2 ^ B := Nat.pow_lt_pow_right one_lt_two_nat hA1_lt_B
  have hcore : 2 ^ A + (ms + 1) < 2 ^ B := by
    have hsum_lt' : 2 ^ A + (ms + 1) < 2 ^ (A + 1) := by
      simpa [hdouble] using hsum_lt
    exact lt_trans hsum_lt' hpowA1_lt_B
  have hfinal : 2 ^ A + (ms + 1) + (mb + 1) < 2 ^ B + (mb + 1) := by
    exact Nat.add_lt_add_right hcore (mb + 1)
  have hlhs : ctxFuel (app s (recΔ b s n)) = 2 ^ A + (ms + 1) + (mb + 1) := by
    simp [ctxFuel, A, mb, ms, mn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hrhs : ctxFuel (recΔ b s (delta n)) = 2 ^ B + (mb + 1) := by
    simp [ctxFuel, B, mb, ms, mn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hlhs, hrhs]
  exact hfinal

lemma ctxFuel_decreases_safe : ∀ {a b : Trace}, SafeStep a b → ctxFuel b < ctxFuel a
| _, _, SafeStep.R_int_delta t => by
    simp [ctxFuel]
| _, _, SafeStep.R_merge_void_left t _ => by
    simp [ctxFuel]
| _, _, SafeStep.R_merge_void_right t _ => by
    simp [ctxFuel]
| _, _, SafeStep.R_merge_cancel t _ _ => by
    simp [ctxFuel]
    omega
| _, _, SafeStep.R_rec_zero b s _ => by
    have h₁ : ctxFuel b < ctxFuel b + 1 := Nat.lt_succ_self (ctxFuel b)
    have h₂ : ctxFuel b + 1 ≤ 2 ^ (ctxFuel s + 5) + (ctxFuel b + 1) := Nat.le_add_left _ _
    have h₃ : ctxFuel b < 2 ^ (ctxFuel s + 5) + (ctxFuel b + 1) := lt_of_lt_of_le h₁ h₂
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₃
| _, _, SafeStep.R_rec_succ b s n => by
    simpa [ctxFuel] using ctxFuel_rec_succ_drop b s n
| _, _, SafeStep.R_eq_refl a _ => by
    simp [ctxFuel]
| _, _, SafeStep.R_eq_diff a b _ => by
    simp [ctxFuel]

lemma ctxFuel_decreases_ctx : ∀ {a b : Trace}, SafeStepCtx a b → ctxFuel b < ctxFuel a
| _, _, SafeStepCtx.root hs => ctxFuel_decreases_safe hs
| _, _, @SafeStepCtx.integrate t u h => by
    have ih : ctxFuel u < ctxFuel t := ctxFuel_decreases_ctx h
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right ih 1)
| _, _, @SafeStepCtx.mergeL a a' b h => by
    have ih : ctxFuel a' < ctxFuel a := ctxFuel_decreases_ctx h
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right ih (ctxFuel b + 2))
| _, _, @SafeStepCtx.mergeR a b b' h => by
    have ih : ctxFuel b' < ctxFuel b := ctxFuel_decreases_ctx h
    have h₁ : ctxFuel a + ctxFuel b' < ctxFuel a + ctxFuel b := Nat.add_lt_add_left ih (ctxFuel a)
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right h₁ 2)
| _, _, @SafeStepCtx.appL a a' b h => by
    have ih : ctxFuel a' < ctxFuel a := ctxFuel_decreases_ctx h
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right ih (ctxFuel b + 1))
| _, _, @SafeStepCtx.appR a b b' h => by
    have ih : ctxFuel b' < ctxFuel b := ctxFuel_decreases_ctx h
    have h₁ : ctxFuel a + ctxFuel b' < ctxFuel a + ctxFuel b := Nat.add_lt_add_left ih (ctxFuel a)
    simpa [ctxFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right h₁ 1)
| _, _, @SafeStepCtx.recB b b' s n h => by
    have ih : ctxFuel b' < ctxFuel b := ctxFuel_decreases_ctx h
    let C : Nat := 2 ^ (ctxFuel n + ctxFuel s + 5)
    have h₁ : C + ctxFuel b' < C + ctxFuel b := Nat.add_lt_add_left ih C
    simpa [ctxFuel, C, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right h₁ 1)
| _, _, @SafeStepCtx.recS b s s' n h => by
    have ih : ctxFuel s' < ctxFuel s := ctxFuel_decreases_ctx h
    let E' : Nat := ctxFuel n + ctxFuel s' + 5
    let E : Nat := ctxFuel n + ctxFuel s + 5
    have hExp : E' < E := by
      have h₁ : ctxFuel n + ctxFuel s' < ctxFuel n + ctxFuel s := Nat.add_lt_add_left ih (ctxFuel n)
      simpa [E', E] using Nat.add_lt_add_right h₁ 5
    have hPow : 2 ^ E' < 2 ^ E := Nat.pow_lt_pow_right one_lt_two_nat hExp
    simpa [ctxFuel, E', E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right hPow (ctxFuel b + 1))
| _, _, @SafeStepCtx.recN b s n n' h => by
    have ih : ctxFuel n' < ctxFuel n := ctxFuel_decreases_ctx h
    let E' : Nat := ctxFuel n' + ctxFuel s + 5
    let E : Nat := ctxFuel n + ctxFuel s + 5
    have hExp : E' < E := by
      have h₁ : ctxFuel n' + ctxFuel s < ctxFuel n + ctxFuel s := Nat.add_lt_add_right ih (ctxFuel s)
      simpa [E', E] using Nat.add_lt_add_right h₁ 5
    have hPow : 2 ^ E' < 2 ^ E := Nat.pow_lt_pow_right one_lt_two_nat hExp
    simpa [ctxFuel, E', E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.add_lt_add_right hPow (ctxFuel b + 1))

theorem wf_SafeStepCtxRev : WellFounded (fun a b : Trace => SafeStepCtx b a) := by
  have hwf : WellFounded (fun x y : Trace => ctxFuel x < ctxFuel y) :=
    InvImage.wf (f := ctxFuel) Nat.lt_wfRel.wf
  have hsub : Subrelation (fun a b : Trace => SafeStepCtx b a)
      (fun x y : Trace => ctxFuel x < ctxFuel y) := by
    intro a b h
    exact ctxFuel_decreases_ctx h
  exact Subrelation.wf hsub hwf

theorem recCtxAccObligation : RecCtxAccObligation := by
  intro b s n hb hs hn
  exact (wf_SafeStepCtxRev.apply (recΔ b s n))

theorem acc_ctx_all : ∀ t : Trace, Acc SafeStepCtxRev t := by
  intro t
  simpa [SafeStepCtxRev] using (wf_SafeStepCtxRev.apply t)

end MetaSN_KO7
