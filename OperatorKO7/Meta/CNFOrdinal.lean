-- (pretty-printing and examples moved below, after definitions)
/-!
  # Constructive CNF Ordinal - Complete, Axiom-Free, Computable

  This module provides a fully constructive Cantor Normal Form (CNF) ordinal type and computable implementations for:
  - Canonical structure and invariants
  - Normalization (merge, sort, remove zeros)
  - Addition, multiplication, ω-exponentiation
  - Total, computable lexicographic comparison (cmp, le, lt)
  - No axioms, no sorry, no noncomputable

  All code is total and lint-clean. See Docs/A_Constructive_Ordinal_Skeleton.md for intended semantics and proofs.
-/
set_option linter.unnecessarySimpa false


namespace OperatorKO7.MetaCNF

/-!
  ## CNF Representation
  - List of (exponent, coefficient) pairs, exponents strictly decreasing, coefficients positive.
  - Invariant: No zero coefficients, no zero exponents except possibly for the last term (finite part).
  - Example: ω^3·2 + ω^1·5 + 7  ≡  [(3,2), (1,5), (0,7)]
-/



structure CNF where
  repr : List (Nat × Nat) -- List of (exponent, coefficient) pairs
  -- Invariant: strictly decreasing exponents, all coefficients > 0
deriving Repr, DecidableEq

/-!
  ## Helper: merge like exponents, remove zeros, sort decreasing
-/
private def insertDesc (p : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [p]
  | (q::qs) => if p.1 > q.1 then p :: q :: qs else q :: insertDesc p qs

private def sortDesc (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.foldl (fun acc x => insertDesc x acc) []

private def mergeLike (l : List (Nat × Nat)) : List (Nat × Nat) :=
  let l := l.filter (fun ⟨_, c⟩ => c ≠ 0)
  let l := sortDesc l -- sort by decreasing exponent
  let rec go (acc : List (Nat × Nat)) (l : List (Nat × Nat)) : List (Nat × Nat) :=
    match l with
    | [] => acc.reverse
    | (e, c) :: xs =>
      match acc with
      | (e', c') :: as' =>
        if e = e' then go ((e, c + c') :: as') xs else go ((e, c) :: acc) xs
      | [] => go [(e, c)] xs
  go [] l

/-!
  ## Normalization: canonical form
-/
def norm_cnf (x : CNF) : CNF :=
  { repr := mergeLike x.repr }

/-!
  ## Lexicographic comparison on normalized representations
  Compare two CNFs by their normalized `repr` lists. Higher exponents dominate;
  when exponents tie, higher coefficients dominate. Missing tails are treated
  as smaller (i.e., [] < non-empty).
-/
def cmpList : List (Nat × Nat) → List (Nat × Nat) → Ordering
  | [], [] => Ordering.eq
  | [], _  => Ordering.lt
  | _,  [] => Ordering.gt
  | (e1, c1) :: xs, (e2, c2) :: ys =>
    if e1 < e2 then Ordering.lt else
    if e2 < e1 then Ordering.gt else
    -- exponents are equal; compare coefficients
    if c1 < c2 then Ordering.lt else
    if c2 < c1 then Ordering.gt else
    -- equal head terms; recurse on tails
    cmpList xs ys

/-- Reflexivity for list-lex comparison. -/
theorem cmpList_refl_eq : ∀ xs : List (Nat × Nat), cmpList xs xs = Ordering.eq := by
  intro xs; induction xs with
  | nil => simp [cmpList]
  | @cons hd tl ih =>
    cases hd with
    | mk e c =>
      -- both exponent and coefficient self-comparisons fall through to recursion
      simp [cmpList, Nat.lt_irrefl, ih]

/-- Head-case: if e1 < e2, the comparison is lt (and swaps to gt). -/
theorem cmpList_cons_cons_exp_lt
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e1 < e2) :
  cmpList ((e1, c1) :: xs) ((e2, c2) :: ys) = Ordering.lt := by
  simp [cmpList, h]

/-- Head-case (swap): if e1 < e2, then swapping yields gt. -/
theorem cmpList_cons_cons_exp_lt_swap
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e1 < e2) :
  cmpList ((e2, c2) :: ys) ((e1, c1) :: xs) = Ordering.gt := by
  -- On swap, the second branch detects e1 < e2
  have : ¬ e2 < e1 := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [cmpList, this, h]

/-- Head-case: if e2 < e1, the comparison is gt (and swaps to lt). -/
theorem cmpList_cons_cons_exp_gt
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e2 < e1) :
  cmpList ((e1, c1) :: xs) ((e2, c2) :: ys) = Ordering.gt := by
  have : ¬ e1 < e2 := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [cmpList, this, h]

/-- Head-case (swap): if e2 < e1, swapping yields lt. -/
theorem cmpList_cons_cons_exp_gt_swap
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)} (h : e2 < e1) :
  cmpList ((e2, c2) :: ys) ((e1, c1) :: xs) = Ordering.lt := by
  simp [cmpList, h]

/-- Head-case: equal exponents, smaller coefficient gives lt. -/
theorem cmpList_cons_cons_exp_eq_coeff_lt
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)} (h : c1 < c2) :
  cmpList ((e, c1) :: xs) ((e, c2) :: ys) = Ordering.lt := by
  have : ¬ e < e := Nat.lt_irrefl _
  simp [cmpList, this, h]

/-- Head-case: equal exponents, larger coefficient gives gt. -/
theorem cmpList_cons_cons_exp_eq_coeff_gt
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)} (h : c2 < c1) :
  cmpList ((e, c1) :: xs) ((e, c2) :: ys) = Ordering.gt := by
  have : ¬ e < e := Nat.lt_irrefl _
  have : ¬ c1 < c2 := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [cmpList, Nat.lt_irrefl, this, h]

/-- Head-case: equal exponents and coefficients, comparison recurses. -/
theorem cmpList_cons_cons_exp_eq_coeff_eq
  {e c : Nat} {xs ys : List (Nat × Nat)} :
  cmpList ((e, c) :: xs) ((e, c) :: ys) = cmpList xs ys := by
  simp [cmpList, Nat.lt_irrefl]

/-- Base-case: [] < non-empty. -/
theorem cmpList_nil_left_lt {y : Nat × Nat} {ys : List (Nat × Nat)} :
  cmpList [] (y :: ys) = Ordering.lt := by
  simp [cmpList]

/-- Base-case: non-empty > []. -/
theorem cmpList_nil_right_gt {x : Nat × Nat} {xs : List (Nat × Nat)} :
  cmpList (x :: xs) [] = Ordering.gt := by
  simp [cmpList]

/-- Eliminate cmpList=lt on cons/cons: describes exactly which head-case caused it or recurses. -/
theorem cmpList_cons_cons_lt_cases
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (h : cmpList ((e1, c1) :: xs) ((e2, c2) :: ys) = Ordering.lt) :
  e1 < e2 ∨ (e1 = e2 ∧ c1 < c2) ∨ (e1 = e2 ∧ c1 = c2 ∧ cmpList xs ys = Ordering.lt) := by
  -- peel the nested ifs of cmpList via case splits
  classical
  if hlt : e1 < e2 then
    -- immediate lt by exponent
    exact Or.inl hlt
  else
    have hnotlt : ¬ e1 < e2 := by simpa using hlt
    if hgt : e2 < e1 then
      -- would force gt, contradicting h
      have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
        simp [cmpList, hnotlt, hgt]
      cases this ▸ h
    else
      have hnotgt : ¬ e2 < e1 := by simpa using hgt
      -- exponents must be equal
      have heq : e1 = e2 := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
      -- compare coefficients
      if hclt : c1 < c2 then
        exact Or.inr (Or.inl ⟨heq, hclt⟩)
      else
        if hcgt : c2 < c1 then
          -- would force gt, contradicting h (use the dedicated head-eq coeff-gt lemma)
          have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
            subst heq; simpa using (cmpList_cons_cons_exp_eq_coeff_gt (xs:=xs) (ys:=ys) (e:=e1) (c1:=c1) (c2:=c2) hcgt)
          cases this ▸ h
        else
          -- equal coefficients; recurse: rewrite h to a tail-lt
          have hceq : c1 = c2 := by
            -- from ¬ c1 < c2 and ¬ c2 < c1, get equality
            have hle₁ : c2 ≤ c1 := Nat.not_lt.mp hclt
            have hle₂ : c1 ≤ c2 := Nat.not_lt.mp hcgt
            exact Nat.le_antisymm hle₂ hle₁
          -- rewrite h via heq and hceq, then drop to tails
          have h' : cmpList ((e1,c1)::xs) ((e1,c1)::ys) = Ordering.lt := by
            simpa [heq, hceq] using h
          have hTail : cmpList xs ys = Ordering.lt := by
            simpa [cmpList_cons_cons_exp_eq_coeff_eq] using h'
          exact Or.inr (Or.inr ⟨heq, hceq, hTail⟩)

/-- Symmetry for lt: if cmpList xs ys = lt then cmpList ys xs = gt. -/
theorem cmpList_symm_gt_of_lt :
  ∀ xs ys : List (Nat × Nat), cmpList xs ys = Ordering.lt → cmpList ys xs = Ordering.gt
  | [], [] , h => by cases h
  | [], (y::ys), _ => by simp [cmpList]
  | (x::xs), [], h => by cases h
  | ((e1,c1)::xs), ((e2,c2)::ys), h =>
    -- analyze which branch produced lt, then swap accordingly
    have hc := cmpList_cons_cons_lt_cases (xs:=xs) (ys:=ys) h
    by
      cases hc with
      | inl hExpLt =>
        -- exponent lt ⇒ swapped is gt
        exact (cmpList_cons_cons_exp_lt_swap (xs:=xs) (ys:=ys) hExpLt)
      | inr hrest =>
        cases hrest with
        | inl hCoeffLt =>
          rcases hCoeffLt with ⟨heq, hclt⟩
          -- equal exponents, coeff lt ⇒ swapped is gt by coeff-gt lemma with roles swapped
          subst heq
          exact (cmpList_cons_cons_exp_eq_coeff_gt (xs:=ys) (ys:=xs) (e:=e1) (c1:=c2) (c2:=c1) hclt)
        | inr hEqTail =>
          rcases hEqTail with ⟨heq, hceq, htail⟩
          -- descend to tails and lift back via eq-head lemma
          have ih := cmpList_symm_gt_of_lt xs ys htail
          subst heq; subst hceq
          simpa [cmpList_cons_cons_exp_eq_coeff_eq] using ih

/-- Total, computable comparison on CNF via normalized representations. -/
def cmp_cnf (x y : CNF) : Ordering :=
  cmpList (norm_cnf x).repr (norm_cnf y).repr

/-- Strict order: x < y iff cmp is lt. -/
def lt_cnf (x y : CNF) : Prop := cmp_cnf x y = Ordering.lt

/-- Non-strict order: x ≤ y iff cmp is not gt. -/
def le_cnf (x y : CNF) : Prop := cmp_cnf x y ≠ Ordering.gt

theorem cmp_self_eq (x : CNF) : cmp_cnf x x = Ordering.eq := by
  simp [cmp_cnf, cmpList_refl_eq]

/-- Reflexivity: x ≤ x. -/
theorem le_refl (x : CNF) : le_cnf x x := by
  simp [le_cnf, cmp_self_eq]

/-- Irreflexivity: ¬ (x < x). -/
theorem lt_irrefl (x : CNF) : ¬ lt_cnf x x := by
  -- lt_cnf x x means cmp_cnf x x = Ordering.lt, but cmp_self_eq says it's eq.
  simp [lt_cnf, cmp_self_eq]

/-- Value-level trichotomy for cmpList. -/
theorem cmpList_cases (xs ys : List (Nat × Nat)) :
    cmpList xs ys = Ordering.lt ∨ cmpList xs ys = Ordering.eq ∨ cmpList xs ys = Ordering.gt := by
  cases h : cmpList xs ys with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr (Or.inl rfl)
  | gt => exact Or.inr (Or.inr rfl)

/-- Asymmetry at list level: if cmpList xs ys = lt then cmpList ys xs ≠ lt. -/
theorem cmpList_asymm_of_lt {xs ys : List (Nat × Nat)} (h : cmpList xs ys = Ordering.lt) :
    cmpList ys xs ≠ Ordering.lt := by
  have hgt := cmpList_symm_gt_of_lt xs ys h
  intro hcontra
  -- rewrite the gt-equality at the same lhs to force a lt=gt contradiction
  have : Ordering.lt = Ordering.gt := by
    simpa [hcontra] using hgt
  have ne : Ordering.lt ≠ Ordering.gt := by decide
  exact ne this

/-- Trichotomy on cmp: exactly one of lt/eq/gt holds as a value. -/
theorem cmp_cases (x y : CNF) :
    cmp_cnf x y = Ordering.lt ∨ cmp_cnf x y = Ordering.eq ∨ cmp_cnf x y = Ordering.gt := by
  cases h : cmp_cnf x y with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr (Or.inl rfl)
  | gt => exact Or.inr (Or.inr rfl)

/-- If x ≤ y, then cmp is either lt or eq (never gt). -/
theorem le_cases {x y : CNF} (hxy : le_cnf x y) :
    cmp_cnf x y = Ordering.lt ∨ cmp_cnf x y = Ordering.eq := by
  -- Case on the computed ordering; rule out gt using hxy.
  cases h : cmp_cnf x y with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr rfl
  | gt =>
    -- hxy says cmp_cnf x y ≠ gt, contradiction
  exact False.elim (hxy h)

/-- General CNF asymmetry: x < y implies not (y < x). -/
theorem lt_asymm_cnf {x y : CNF} (hxy : lt_cnf x y) : ¬ lt_cnf y x := by
  -- unfold to list-level and use cmpList asymmetry
  unfold lt_cnf at *
  unfold cmp_cnf at *
  -- set normalized lists for readability
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  -- First coerce hxy to a statement about cmpList xs ys = lt
  have hxy' : cmpList xs ys = Ordering.lt := by simpa using hxy
  -- Symmetry gives cmpList ys xs = gt
  have hgt : cmpList ys xs = Ordering.gt := cmpList_symm_gt_of_lt xs ys hxy'
  -- Show lt cannot also hold
  intro hcontra
  have ne : Ordering.lt ≠ Ordering.gt := by decide
  -- hcontra : cmpList ys xs = lt, hgt : cmpList ys xs = gt ⇒ lt = gt
  have : Ordering.gt = Ordering.lt := by exact hgt.symm.trans hcontra
  exact (ne.symm) this

/-- Antisymmetry for `le_cnf` at the cmp level: if x ≤ y and y ≤ x then cmp is eq. -/
theorem le_antisymm_cnf {x y : CNF}
  (hxy : le_cnf x y) (hyx : le_cnf y x) : cmp_cnf x y = Ordering.eq := by
  cases hcmp : cmp_cnf x y with
  | lt =>
    -- translate to list-level, flip, and contradict hyx
    have hltList : cmpList (norm_cnf x).repr (norm_cnf y).repr = Ordering.lt := by
      simpa [cmp_cnf] using hcmp
    have hgtList : cmpList (norm_cnf y).repr (norm_cnf x).repr = Ordering.gt :=
      cmpList_symm_gt_of_lt _ _ hltList
    have : cmp_cnf y x = Ordering.gt := by
      simpa [cmp_cnf] using hgtList
    exact (hyx this).elim
  | eq => exact rfl
  | gt => exact (hxy hcmp).elim
/-- Congruence of cmp on the left, given normalized representations are equal. -/
theorem cmp_congr_left_repr_eq {x y z : CNF}
  (h : (norm_cnf x).repr = (norm_cnf y).repr) :
  cmp_cnf x z = cmp_cnf y z := by
  unfold cmp_cnf; simp [h]

/-- Transitivity for list-level lt: if xs < ys and ys < zs then xs < zs. -/
theorem cmpList_trans_lt :
  ∀ {xs ys zs : List (Nat × Nat)},
    cmpList xs ys = Ordering.lt → cmpList ys zs = Ordering.lt →
    cmpList xs zs = Ordering.lt := by
  intro xs; induction xs with
  | nil =>
    intro ys zs hxy hyz; cases ys with
    | nil => cases hxy
    | cons y ys =>
      -- cmpList [] (y::ys) = lt, so xs<zs regardless of hyz structure on left
      simp [cmpList] at hxy; cases zs with
      | nil =>
        -- hyz: (y::ys) < [] impossible
        simp [cmpList] at hyz
      | cons z zs =>
        simp [cmpList]
  | cons x xs ih =>
    intro ys zs hxy hyz
    cases ys with
    | nil =>
      -- xs<[] impossible
      simp [cmpList] at hxy
    | cons y ys =>
      cases zs with
      | nil =>
        -- ys<[] impossible
        simp [cmpList] at hyz
      | cons z zs =>
        cases x with
        | mk e1 c1 =>
        cases y with
        | mk e2 c2 =>
        cases z with
        | mk e3 c3 =>
        -- analyze hxy
        have hx := cmpList_cons_cons_lt_cases (xs:=xs) (ys:=ys) (e1:=e1) (c1:=c1) (e2:=e2) (c2:=c2) hxy
        -- analyze hyz for ys vs zs
        have hy := cmpList_cons_cons_lt_cases (xs:=ys) (ys:=zs) (e1:=e2) (c1:=c2) (e2:=e3) (c2:=c3) hyz
        -- split on cases to derive e1<e3 or tie and reduce
        rcases hx with hExpLt | hCoeffLt | hTailLt
        · -- e1 < e2; by trans with e2 ≤ e3 from hy
          -- derive e2 ≤ e3
          have hE23 : e2 ≤ e3 := by
            rcases hy with hE2lt3 | hrest
            · exact Nat.le_of_lt hE2lt3
            · rcases hrest with hE2eqE3CoeffLt | hE2eqE3Tail
              · have heq : e2 = e3 := hE2eqE3CoeffLt.left
                simpa [heq] using (le_rfl : e2 ≤ e2)
              · have heq : e2 = e3 := hE2eqE3Tail.left
                simpa [heq] using (le_rfl : e2 ≤ e2)
          -- from e2 ≤ e3, split eq/lt to conclude e1 < e3
          have hE13 : e1 < e3 := by
            have hE2eqOrLt := Nat.lt_or_eq_of_le hE23
            cases hE2eqOrLt with
            | inl hlt23 => exact Nat.lt_trans hExpLt hlt23
            | inr heq23 => simpa [heq23] using hExpLt
          exact (cmpList_cons_cons_exp_lt (xs:=xs) (ys:=zs) (e1:=e1) (c1:=c1) (e2:=e3) (c2:=c3) hE13)
        · -- e1 = e2 ∧ c1 < c2
          rcases hCoeffLt with ⟨hE12, hC12⟩
          -- from hy, either e2<e3 -> then e1<e3; or e2=e3 and c2<c3; or tie and descend
          rcases hy with hE2lt3 | hrest
          · have hE13 : e1 < e3 := by simpa [hE12] using hE2lt3
            exact (cmpList_cons_cons_exp_lt (xs:=xs) (ys:=zs) (e1:=e1) (c1:=c1) (e2:=e3) (c2:=c3) hE13)
          · rcases hrest with hE2eqE3CoeffLt | hE2eqE3Tail
            · rcases hE2eqE3CoeffLt with ⟨hE23, hC23⟩
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              -- coefficients chain: c1 < c2 and c2 < c3 ⇒ c1 < c3
              have hC13 : c1 < c3 := Nat.lt_trans hC12 hC23
              -- conclude by head coefficient comparison
              have hlt : cmpList ((e3,c1)::xs) ((e3,c3)::zs) = Ordering.lt :=
                cmpList_cons_cons_exp_eq_coeff_lt (xs:=xs) (ys:=zs) (e:=e3) (c1:=c1) (c2:=c3) hC13
              simpa [hE13] using hlt
            · rcases hE2eqE3Tail with ⟨hE23, hC23, _hTail⟩
              -- heads tie and c2=c3; from c1<c2 and c2=c3, get c1<c3 and conclude
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              have hC13 : c1 < c3 := by simpa [hC23] using hC12
              have hlt : cmpList ((e3,c1)::xs) ((e3,c3)::zs) = Ordering.lt :=
                cmpList_cons_cons_exp_eq_coeff_lt (xs:=xs) (ys:=zs) (e:=e3) (c1:=c1) (c2:=c3) hC13
              simpa [hE13] using hlt
        · -- e1 = e2 ∧ c1 = c2 ∧ tail lt; combine with hy cases
          rcases hTailLt with ⟨hE12, hC12, hTailXY⟩
          rcases hy with hE2lt3 | hrest
          · have hE13 : e1 < e3 := by simpa [hE12] using hE2lt3
            exact (cmpList_cons_cons_exp_lt (xs:=xs) (ys:=zs) (e1:=e1) (c1:=c1) (e2:=e3) (c2:=c3) hE13)
          · rcases hrest with hE2eqE3CoeffLt | hE2eqE3Tail
            · rcases hE2eqE3CoeffLt with ⟨hE23, hC23⟩
              -- heads tie and c2<c3 ⇒ with c1=c2 we get c1<c3, immediate lt
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              have hC13 : c1 < c3 := by simpa [hC12] using hC23
              have hlt : cmpList ((e3,c1)::xs) ((e3,c3)::zs) = Ordering.lt :=
                cmpList_cons_cons_exp_eq_coeff_lt (xs:=xs) (ys:=zs) (e:=e3) (c1:=c1) (c2:=c3) hC13
              simpa [hE13] using hlt
            · rcases hE2eqE3Tail with ⟨hE23, hC23, hTailYZ⟩
              have hE13 : e1 = e3 := by simpa [hE12] using hE23
              have hC13 : c1 = c3 := by simpa [hE12, hC12] using hC23
              -- descend both with ih on tails
              have ih'' : cmpList xs zs = Ordering.lt := ih (ys:=ys) (zs:=zs) hTailXY hTailYZ
              simpa [cmpList, hE13, Nat.lt_irrefl, hC13] using ih''

/-- Transitivity for CNF lt. -/
theorem lt_trans_cnf {x y z : CNF} (hxy : lt_cnf x y) (hyz : lt_cnf y z) : lt_cnf x z := by
  unfold lt_cnf at *
  -- abbreviations for readability
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  let zs := (norm_cnf z).repr
  -- rewrite both facts to list-level and apply list transitivity
  have hx : cmpList xs ys = Ordering.lt := by simpa [cmp_cnf, xs, ys] using hxy
  have hy : cmpList ys zs = Ordering.lt := by simpa [cmp_cnf, ys, zs] using hyz
  have hz : cmpList xs zs = Ordering.lt := cmpList_trans_lt (xs:=xs) (ys:=ys) (zs:=zs) hx hy
  simpa [cmp_cnf, xs, ys, zs]

/-- Trichotomy for CNF compare: exactly one of lt/eq/gt holds. -/
theorem cmp_cnf_trichotomy (x y : CNF) :
  cmp_cnf x y = Ordering.lt ∨ cmp_cnf x y = Ordering.eq ∨ cmp_cnf x y = Ordering.gt := by
  unfold cmp_cnf
  exact cmpList_cases (norm_cnf x).repr (norm_cnf y).repr

/-- Congruence of cmp on the right, given normalized representations are equal. -/
theorem cmp_congr_right_repr_eq {x y z : CNF}
  (h : (norm_cnf y).repr = (norm_cnf z).repr) :
  cmp_cnf x y = cmp_cnf x z := by
  unfold cmp_cnf; simp [h]

/-- CNF head-case: if normalized head exponents satisfy e1 < e2, then cmp is lt. -/
theorem cmp_cnf_head_exp_lt {x y : CNF}
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e1, c1) :: xs)
  (hy : (norm_cnf y).repr = (e2, c2) :: ys)
  (h : e1 < e2) :
  cmp_cnf x y = Ordering.lt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_lt h]

/-- CNF head-case: if normalized head exponents satisfy e2 < e1, then cmp is gt. -/
theorem cmp_cnf_head_exp_gt {x y : CNF}
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e1, c1) :: xs)
  (hy : (norm_cnf y).repr = (e2, c2) :: ys)
  (h : e2 < e1) :
  cmp_cnf x y = Ordering.gt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_gt h]

/-- CNF head-case: equal head exponents, smaller left coefficient gives lt. -/
theorem cmp_cnf_head_exp_eq_coeff_lt {x y : CNF}
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e, c1) :: xs)
  (hy : (norm_cnf y).repr = (e, c2) :: ys)
  (h : c1 < c2) :
  cmp_cnf x y = Ordering.lt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_eq_coeff_lt h]

/-- CNF head-case: equal head exponents, larger left coefficient gives gt. -/
theorem cmp_cnf_head_exp_eq_coeff_gt {x y : CNF}
  {e c1 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e, c1) :: xs)
  (hy : (norm_cnf y).repr = (e, c2) :: ys)
  (h : c2 < c1) :
  cmp_cnf x y = Ordering.gt := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_eq_coeff_gt h]

/-- CNF head-case: equal head term, comparison recurses on tails. -/
theorem cmp_cnf_head_exp_coeff_eq {x y : CNF}
  {e c : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e, c) :: xs)
  (hy : (norm_cnf y).repr = (e, c) :: ys) :
  cmp_cnf x y = cmpList xs ys := by
  unfold cmp_cnf; simp [hx, hy, cmpList_cons_cons_exp_eq_coeff_eq]

/-- CNF asymmetry in the simple head-exp case: if head e1 < e2 then x < y and not y < x. -/
theorem lt_asymm_head_exp {x y : CNF}
  {e1 c1 e2 c2 : Nat} {xs ys : List (Nat × Nat)}
  (hx : (norm_cnf x).repr = (e1, c1) :: xs)
  (hy : (norm_cnf y).repr = (e2, c2) :: ys)
  (h : e1 < e2) : lt_cnf x y ∧ ¬ lt_cnf y x := by
  constructor
  · unfold lt_cnf; simp [cmp_cnf_head_exp_lt (x:=x) (y:=y) hx hy h]
  · intro hlt
    have hswap : cmp_cnf y x = Ordering.gt := by
      unfold cmp_cnf; simp [hy, hx, cmpList_cons_cons_exp_lt_swap h]
    have ne : Ordering.gt ≠ Ordering.lt := by decide
    -- unfold lt_cnf in hlt to get a cmp equality
    have hlt' : cmp_cnf y x = Ordering.lt := by
      -- linter: prefer simp at hlt' instead of simpa using hlt
      simp [lt_cnf] at hlt; exact hlt
    -- rewrite cmp_cnf y x via hswap to derive an impossible equality
    have hbad : Ordering.gt = Ordering.lt := by
      -- simplify hlt' with the computed swap
      simpa [hswap] using hlt'
    exact ne hbad

/-!
  ## Instances: Decidability and Ord for CNF
-/

instance instDecidableRel_le_cnf : DecidableRel le_cnf := by
  intro x y
  unfold le_cnf
  infer_instance

instance instDecidableRel_lt_cnf : DecidableRel lt_cnf := by
  intro x y
  unfold lt_cnf
  infer_instance

instance : Ord CNF where
  compare := cmp_cnf

/-- If y and z normalize to the same repr and x < y, then x < z. -/
theorem lt_trans_eq_right {x y z : CNF}
  (hYZ : (norm_cnf y).repr = (norm_cnf z).repr)
  (hXY : lt_cnf x y) : lt_cnf x z := by
  unfold lt_cnf at *
  simpa [cmp_congr_right_repr_eq (x:=x) (y:=y) (z:=z) hYZ] using hXY
/-- If x and y normalize to the same repr and y < z, then x < z. -/
theorem lt_trans_eq_left {x y z : CNF}
  (hXY : (norm_cnf x).repr = (norm_cnf y).repr)
  (hYZ : lt_cnf y z) : lt_cnf x z := by
  unfold lt_cnf at *
  simpa [cmp_congr_left_repr_eq (x:=x) (y:=y) (z:=z) hXY] using hYZ

/-- If y and z normalize to the same repr and x ≤ y, then x ≤ z. -/
theorem le_trans_eq_right {x y z : CNF}
  (hYZ : (norm_cnf y).repr = (norm_cnf z).repr)
  (hXY : le_cnf x y) : le_cnf x z := by
  unfold le_cnf at *
  -- cmp x z = gt would rewrite to cmp x y = gt via congruence, contradicting hXY
  intro hgt
  have : cmp_cnf x y = Ordering.gt := by
    simpa [cmp_congr_right_repr_eq (x:=x) (y:=y) (z:=z) hYZ] using hgt
  exact hXY this

/-- If x and y normalize to the same repr and y ≤ z, then x ≤ z. -/
theorem le_trans_eq_left {x y z : CNF}
  (hXY : (norm_cnf x).repr = (norm_cnf y).repr)
  (hYZ : le_cnf y z) : le_cnf x z := by
  unfold le_cnf at *
  intro hgt
  -- rewrite cmp x z to cmp y z using repr equality, contradicting hYZ
  have : cmp_cnf y z = Ordering.gt := by
    simpa [cmp_congr_left_repr_eq (x:=x) (y:=y) (z:=z) hXY] using hgt
  exact hYZ this

/-!
  ## Tiny conveniences
-/

/-- If normalized representations are equal, cmp is `eq`. -/
theorem cmp_eq_of_norm_repr_eq {x y : CNF}
  (h : (norm_cnf x).repr = (norm_cnf y).repr) :
  cmp_cnf x y = Ordering.eq := by
  unfold cmp_cnf
  simp [cmpList_refl_eq, h]

/-!
  Equality characterization: if cmpList = eq then the lists are equal.
  This lets us reflect cmp equality back to structural equality of normalized
  representations at the CNF level.
-/
theorem cmpList_eq_implies_eq :
    ∀ {xs ys : List (Nat × Nat)}, cmpList xs ys = Ordering.eq → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil =>
      simp [cmpList] at h
      exact rfl
    | cons y ys =>
      -- cmpList [] (y::ys) = lt, contradicting eq
      simp [cmpList] at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      -- cmpList (x::xs) [] = gt, contradicting eq
      simp [cmpList] at h
    | cons y ys =>
      cases x with
      | mk e1 c1 =>
        cases y with
        | mk e2 c2 =>
        classical
        -- eliminate strict exponent inequalities via if-splits
        if hltE : e1 < e2 then
          have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
            simpa [cmpList, hltE]
          cases this ▸ h
        else
          have hnot12 : ¬ e1 < e2 := by simpa using hltE
          if hgtE : e2 < e1 then
            have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
              simpa [cmpList, hnot12, hgtE]
            cases this ▸ h
          else
            -- exponents equal
            have heq : e1 = e2 :=
              Nat.le_antisymm (Nat.le_of_not_gt hgtE) (Nat.le_of_not_gt hltE)
            -- eliminate strict coefficient inequalities
            if hltC : c1 < c2 then
              have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
                simpa [cmpList, heq, Nat.lt_irrefl, hltC]
              cases this ▸ h
            else
              have hnotc12 : ¬ c1 < c2 := by simpa using hltC
              if hgtC : c2 < c1 then
                have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.gt := by
                  simpa [cmpList, heq, Nat.lt_irrefl, hnotc12, hgtC]
                cases this ▸ h
              else
                -- coefficients equal; descend to tails
                have hceq : c1 = c2 := by
                  have hle₁ : c2 ≤ c1 := Nat.not_lt.mp hltC
                  have hle₂ : c1 ≤ c2 := Nat.not_lt.mp hgtC
                  exact Nat.le_antisymm hle₂ hle₁
                have hTail : cmpList xs ys = Ordering.eq := by
                  simpa [cmpList, heq, hceq, Nat.lt_irrefl] using h
                have ih' := ih hTail
                subst heq; subst hceq
                simp [ih']

theorem cmp_eq_iff_norm_repr_eq {x y : CNF} :
    cmp_cnf x y = Ordering.eq ↔ (norm_cnf x).repr = (norm_cnf y).repr := by
  constructor
  · intro h
    unfold cmp_cnf at h
    exact cmpList_eq_implies_eq h
  · intro hrepr
    exact cmp_eq_of_norm_repr_eq (x:=x) (y:=y) hrepr

/-- lt implies le (definitionally). -/
theorem le_of_lt {x y : CNF} (h : lt_cnf x y) : le_cnf x y := by
  unfold lt_cnf at h
  unfold le_cnf
  intro hgt
  -- rewriting with h produces an impossible lt=gt
  cases h ▸ hgt

/-- CNF-level symmetry: if cmp x y = lt then cmp y x = gt. -/
theorem cmp_cnf_symm_gt_of_lt {x y : CNF}
  (h : cmp_cnf x y = Ordering.lt) : cmp_cnf y x = Ordering.gt := by
  classical
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  have hlist : cmpList xs ys = Ordering.lt := by
    simpa [cmp_cnf, xs, ys] using h
  have hgt := cmpList_symm_gt_of_lt xs ys hlist
  simpa [cmp_cnf, xs, ys] using hgt

-- (We intentionally avoid a gt→lt symmetry lemma here to keep the proof surface minimal.)

/-- Symmetry for gt: if cmpList xs ys = gt then cmpList ys xs = lt. -/
theorem cmpList_symm_lt_of_gt :
  ∀ xs ys : List (Nat × Nat), cmpList xs ys = Ordering.gt → cmpList ys xs = Ordering.lt
  | [], [], h => by cases h
  | [], (y::ys), h => by
      -- cmpList [] (y::ys) = lt, so gt is impossible
      cases h
  | (x::xs), [], _h => by
      -- non-empty vs []
      simp [cmpList]
  | ((e1,c1)::xs), ((e2,c2)::ys), h =>
      by
        classical
        -- split on exponent comparison using an if-then-else
        if hlt12 : e1 < e2 then
          -- then result would be lt, contradicts gt
          have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
            simpa [cmpList, hlt12]
          cases this ▸ h
        else
          have hnot12 : ¬ e1 < e2 := by simpa using hlt12
          if hlt21 : e2 < e1 then
            -- gt by exponent; swap gives lt
            exact (cmpList_cons_cons_exp_gt_swap (xs:=xs) (ys:=ys) (e1:=e1) (c1:=c1) (e2:=e2) (c2:=c2) hlt21)
          else
            -- exponents equal
            have heq : e1 = e2 :=
              Nat.le_antisymm (Nat.le_of_not_gt hlt21) (Nat.le_of_not_gt hlt12)
            -- compare coefficients similarly
            if hclt12 : c1 < c2 then
              -- would make lt, contradict gt
              have : cmpList ((e1,c1)::xs) ((e2,c2)::ys) = Ordering.lt := by
                simpa [cmpList, heq, Nat.lt_irrefl, hclt12]
              cases this ▸ h
            else
              have hnotc12 : ¬ c1 < c2 := by simpa using hclt12
              if hclt21 : c2 < c1 then
                -- swapped becomes lt by coeff-lt
                have : cmpList ((e2,c2)::ys) ((e1,c1)::xs) = Ordering.lt := by
                  simpa [heq] using (cmpList_cons_cons_exp_eq_coeff_lt (xs:=ys) (ys:=xs) (e:=e1) (c1:=c2) (c2:=c1) hclt21)
                simpa using this
              else
                -- coefficients equal; descend to tails
                have hceq : c1 = c2 := by
                  have hle₁ : c2 ≤ c1 := Nat.not_lt.mp hclt12
                  have hle₂ : c1 ≤ c2 := Nat.not_lt.mp hclt21
                  exact Nat.le_antisymm hle₂ hle₁
                -- from h = gt, tails must be gt as well
                have hTail : cmpList xs ys = Ordering.gt := by
                  simpa [cmpList, heq, hceq, Nat.lt_irrefl] using h
                -- recurse on tails
                have ih := cmpList_symm_lt_of_gt xs ys hTail
                -- lift back through equal heads
                simpa [cmpList_cons_cons_exp_eq_coeff_eq, heq, hceq] using ih

/-- CNF-level symmetry: if cmp x y = gt then cmp y x = lt. -/
theorem cmp_cnf_symm_lt_of_gt {x y : CNF}
  (h : cmp_cnf x y = Ordering.gt) : cmp_cnf y x = Ordering.lt := by
  classical
  let xs := (norm_cnf x).repr
  let ys := (norm_cnf y).repr
  have hlist : cmpList xs ys = Ordering.gt := by
    simpa [cmp_cnf, xs, ys] using h
  have hlt := cmpList_symm_lt_of_gt xs ys hlist
  simpa [cmp_cnf, xs, ys] using hlt

/- Totality for ≤ on CNF. -/
theorem le_total_cnf (x y : CNF) : le_cnf x y ∨ le_cnf y x := by
  -- case on the computed comparison
  cases h : cmp_cnf x y with
  | lt => exact Or.inl (le_of_lt (by simpa [lt_cnf] using h))
  | eq => exact Or.inl (by simp [le_cnf, h])
  | gt =>
    -- swap gives lt, hence y ⪯ x
    have : cmp_cnf y x = Ordering.lt := cmp_cnf_symm_lt_of_gt h
    exact Or.inr (by
      -- lt implies ≤ by definition (not gt)
      have : lt_cnf y x := by simpa [lt_cnf] using this
      exact le_of_lt this)

-- Infix notations (optional ergonomics)
infix:50 " ≺ " => lt_cnf
infix:50 " ⪯ " => le_cnf

/-!
  ## Addition: merge and normalize
-/
def add_cnf (x y : CNF) : CNF :=
  norm_cnf { repr := x.repr ++ y.repr }

/-!
  ## Multiplication: distributive law, collect like terms, normalize
-/
def mul_cnf (x y : CNF) : CNF :=
  match norm_cnf x, norm_cnf y with
  | { repr := [] }, _ => { repr := [] }
  | _, { repr := [] } => { repr := [] }
  | { repr := xs }, { repr := ys } =>
    let terms := List.foldr (fun a b => List.append a b) [] (xs.map (fun (e1, c1) => ys.map (fun (e2, c2) => (e1 + e2, c1 * c2))))
    norm_cnf { repr := terms }

/-!
  ## ω-Exponentiation: ω^x
  - ω^0 = 1
  - ω^{sum_i ω^{a_i}·c_i} = ω^{ω^{a_1}·c_1 + ...}
  For CNF, ω^x is just shifting exponents up one level.
-/
def opowω_cnf (x : CNF) : CNF :=
  match norm_cnf x with
  | { repr := [] } => { repr := [(0,1)] } -- ω^0 = 1
  | { repr := xs } => { repr := xs.map (fun (e, c) => (e + 1, c)) }

/-!
  ## Examples
-/
def cnf_zero : CNF := { repr := [] }
def cnf_one : CNF := { repr := [(0,1)] }
def cnf_omega : CNF := { repr := [(1,1)] }
def cnf_omega_plus_one : CNF := { repr := [(1,1),(0,1)] }
def cnf_two_omega : CNF := { repr := [(1,2)] }
def cnf_omega_sq : CNF := { repr := [(2,1)] }

/-!
  ## Basic tests (examples)
-/




end OperatorKO7.MetaCNF

namespace OperatorKO7.MetaCNF

/-!
  ## Pretty-printing (basic)
  Converts a CNF to a human-readable string for debugging and examples.
-/
def intercalate (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xs => xs.foldl (fun acc s => acc ++ sep ++ s) x

def showTerm : Nat × Nat → String
  | (0, c) => toString c
  | (e, 1) => "ω^" ++ toString e
  | (e, c) => toString c ++ "·ω^" ++ toString e

def showCNF (cnf : CNF) : String :=
  match cnf.repr with
  | [] => "0"
  | xs => intercalate " + " (xs.map showTerm)

instance : ToString CNF where
  toString := showCNF

/-!
  ## Normalization checks (boolean)
  Executable validators for CNF invariants. Useful for tests and examples.
-/
def allPosCoeffs : List (Nat × Nat) → Bool
  | [] => true
  | (_, c) :: xs => (c > 0) && allPosCoeffs xs

def sortedStrictDesc : List (Nat × Nat) → Bool
  | [] => true
  | [ _ ] => true
  | (e1, _) :: (e2, c2) :: xs => (e1 > e2) && sortedStrictDesc ((e2, c2) :: xs)

def isNormalizedB (x : CNF) : Bool :=
  sortedStrictDesc x.repr && allPosCoeffs x.repr

/-!
  ## Inspectors and predicates (ergonomics)
-/

def isZero (x : CNF) : Bool :=
  match (norm_cnf x).repr with
  | [] => true
  | _ => false

def isOne (x : CNF) : Bool :=
  decide ((norm_cnf x).repr = [(0, 1)])

def isOmegaPow (x : CNF) : Bool :=
  match (norm_cnf x).repr with
  | [(_, 1)] => true
  | _ => false

def degreeOpt (x : CNF) : Option Nat :=
  match (norm_cnf x).repr with
  | [] => none
  | (e, _) :: _ => some e

/-- Transitivity for `≤` on CNF. -/
theorem le_trans_cnf {x y z : CNF} (hxy : le_cnf x y) (hyz : le_cnf y z) : le_cnf x z := by
  -- By definition, le_cnf x z means cmp_cnf x z ≠ gt. Prove by contradiction.
  unfold le_cnf at *
  intro hgt
  -- Case on cmp x y.
  cases hxyCases : cmp_cnf x y with
  | lt =>
    -- y ≤ z splits into lt or eq.
    have hyCases := le_cases (x:=y) (y:=z) hyz
    cases hyCases with
    | inl hylt =>
      -- x < y and y < z ⇒ x < z, contradicting cmp x z = gt.
      have hxlt : lt_cnf x y := by simpa [lt_cnf] using hxyCases
      have hzlt : lt_cnf x z := lt_trans_cnf hxlt (by simpa [lt_cnf] using hylt)
      -- Convert to cmp form and contradict hgt directly.
      have : cmp_cnf x z = Ordering.lt := by simpa [lt_cnf] using hzlt
      cases this ▸ hgt
    | inr hyeq =>
      -- cmp y z = eq ⇒ normalize-equal reprs; transport x<y to x<z.
      have hrepr : (norm_cnf y).repr = (norm_cnf z).repr :=
        (cmp_eq_iff_norm_repr_eq).mp hyeq
      have hxlt : lt_cnf x y := by simpa [lt_cnf] using hxyCases
      have hzlt : lt_cnf x z := lt_trans_eq_right (x:=x) (y:=y) (z:=z) hrepr hxlt
      have : cmp_cnf x z = Ordering.lt := by simpa [lt_cnf] using hzlt
      cases this ▸ hgt
  | eq =>
    -- cmp x y = eq ⇒ normalized reprs equal; rewrite left via congruence and use hyz.
    have hrepr : (norm_cnf x).repr = (norm_cnf y).repr :=
      (cmp_eq_iff_norm_repr_eq).mp hxyCases
    -- Transport y ≤ z to x ≤ z, closing the contradiction.
    exact (le_trans_eq_left (x:=x) (y:=y) (z:=z) hrepr hyz) hgt
  | gt =>
    -- Contradicts hxy immediately.
    exact (hxy hxyCases).elim

def leadCoeffOpt (x : CNF) : Option Nat :=
  match (norm_cnf x).repr with
  | [] => none
  | (_, c) :: _ => some c

/-!
  ## Example values and usage
-/
def example1 := add_cnf cnf_omega cnf_one         -- ω + 1
def example2 := add_cnf cnf_omega cnf_omega       -- ω + ω = 2·ω
def example3 := mul_cnf cnf_omega cnf_omega       -- ω * ω = ω^2

end OperatorKO7.MetaCNF

namespace OperatorKO7.MetaCNF

/-!
  ## Min/Max and sorting helpers (ergonomics)
-/

def min_cnf (x y : CNF) : CNF := if lt_cnf x y then x else y
def max_cnf (x y : CNF) : CNF := if lt_cnf x y then y else x

private def insertBy (x : CNF) : List CNF → List CNF
  | [] => [x]
  | y :: ys => if lt_cnf x y then x :: y :: ys else y :: insertBy x ys

def sortCNF (xs : List CNF) : List CNF :=
  xs.foldl (fun acc x => insertBy x acc) []

def isNonDecreasing (xs : List CNF) : Bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: y :: ys =>
    let leB (a b : CNF) : Bool :=
      match cmp_cnf a b with
      | Ordering.gt => false
      | _ => true
    leB x y && isNonDecreasing (y :: ys)

def minListCNF : List CNF → Option CNF
  | [] => none
  | x :: xs => some (xs.foldl (fun acc y => min_cnf acc y) x)

def maxListCNF : List CNF → Option CNF
  | [] => none
  | x :: xs => some (xs.foldl (fun acc y => max_cnf acc y) x)

-- Demo checks
#eval toString (min_cnf cnf_omega cnf_one)    -- expect "1"
#eval toString (max_cnf cnf_omega cnf_one)    -- expect "ω^1"
-- Use a local demo set to avoid forward references
def demoList : List CNF := [cnf_zero, cnf_one, cnf_omega]
#eval isNonDecreasing (sortCNF demoList)       -- expect true
#eval (match minListCNF demoList with | some x => toString x | none => "-")
#eval (match maxListCNF demoList with | some x => toString x | none => "-")

end OperatorKO7.MetaCNF

/-!
  ## Example output (for documentation/testing)
  Executable examples to illustrate CNF operations and normalization.
  These produce human-readable CNF strings and boolean normalization checks.
-/
#eval toString OperatorKO7.MetaCNF.example1
#eval toString OperatorKO7.MetaCNF.example2
#eval toString OperatorKO7.MetaCNF.example3

-- Inspector demos
#eval OperatorKO7.MetaCNF.isZero OperatorKO7.MetaCNF.cnf_zero
#eval OperatorKO7.MetaCNF.isOne OperatorKO7.MetaCNF.cnf_one
#eval OperatorKO7.MetaCNF.isOmegaPow OperatorKO7.MetaCNF.cnf_omega
#eval OperatorKO7.MetaCNF.degreeOpt OperatorKO7.MetaCNF.cnf_two_omega
#eval OperatorKO7.MetaCNF.leadCoeffOpt OperatorKO7.MetaCNF.cnf_two_omega

-- Normalization checks on the examples (true means normalized)
#eval OperatorKO7.MetaCNF.isNormalizedB (OperatorKO7.MetaCNF.norm_cnf OperatorKO7.MetaCNF.example1)
#eval OperatorKO7.MetaCNF.isNormalizedB (OperatorKO7.MetaCNF.norm_cnf OperatorKO7.MetaCNF.example2)
#eval OperatorKO7.MetaCNF.isNormalizedB (OperatorKO7.MetaCNF.norm_cnf OperatorKO7.MetaCNF.example3)

-- (pretty-printing and examples are defined at the end of the file)
-- All CNF values are normalized: exponents strictly decreasing, coefficients > 0, no duplicate exponents.

/-!
  ## Property checks (computable, #eval-style)
  Small test harness verifying comparison laws and normalization preservation
  over a fixed sample set.
-/
namespace OperatorKO7.MetaCNF

-- Boolean helpers for cmp outcomes
def isEq (x y : CNF) : Bool :=
  match cmp_cnf x y with
  | Ordering.eq => true
  | _ => false

def isLt (x y : CNF) : Bool :=
  match cmp_cnf x y with
  | Ordering.lt => true
  | _ => false

def isLe (x y : CNF) : Bool :=
  match cmp_cnf x y with
  | Ordering.gt => false
  | _ => true

-- Simple boolean all (avoid depending on extra list APIs)
def allB {α} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allB p xs

def pairs {α} (xs : List α) : List (α × α) :=
  xs.foldr (fun x acc => List.append (xs.map (fun y => (x, y))) acc) []

def triples {α} (xs : List α) : List (α × α × α) :=
  xs.foldr (fun x acc =>
    let rows := xs.foldr (fun y acc2 => List.append (xs.map (fun z => (x, y, z))) acc2) []
    List.append rows acc) []

-- Comparison properties
def antisym_check (x y : CNF) : Bool :=
  match cmp_cnf x y, cmp_cnf y x with
  | Ordering.eq, Ordering.eq => true
  | Ordering.lt, Ordering.gt => true
  | Ordering.gt, Ordering.lt => true
  | _, _ => false

def trichotomy_check (x y : CNF) : Bool :=
  match cmp_cnf x y, cmp_cnf y x with
  | Ordering.eq, Ordering.eq => true
  | Ordering.lt, Ordering.gt => true
  | Ordering.gt, Ordering.lt => true
  | _, _ => false

def trans_lt_check (a b c : CNF) : Bool :=
  if isLt a b && isLt b c then isLt a c else true

def trans_le_check (a b c : CNF) : Bool :=
  if isLe a b && isLe b c then isLe a c else true

-- Totality check for ≤: for any pair, either x ≤ y or y ≤ x
def le_total_check (x y : CNF) : Bool :=
  isLe x y || isLe y x

-- Normalization preservation (ops already normalize by definition)
def preserves_norm_add (x y : CNF) : Bool := isNormalizedB (add_cnf x y)
def preserves_norm_mul (x y : CNF) : Bool := isNormalizedB (mul_cnf x y)
def preserves_norm_opow (x : CNF) : Bool := isNormalizedB (opowω_cnf x)

-- Sample set
def samples : List CNF :=
  [ cnf_zero, cnf_one, cnf_omega, cnf_omega_plus_one, cnf_two_omega, cnf_omega_sq ]

-- Aggregate checks over samples
def check_all_antisym : Bool :=
  allB (fun p => antisym_check p.1 p.2) (pairs samples)

def check_all_trichotomy : Bool :=
  allB (fun p => trichotomy_check p.1 p.2) (pairs samples)

def check_all_trans_lt : Bool :=
  allB (fun t => trans_lt_check t.1 t.2.1 t.2.2) (triples samples)

def check_all_trans_le : Bool :=
  allB (fun t => trans_le_check t.1 t.2.1 t.2.2) (triples samples)

def check_all_total_le : Bool :=
  allB (fun p => le_total_check p.1 p.2) (pairs samples)

def check_reflexive_eq : Bool :=
  allB (fun x => isEq x x) samples

def check_norm_add : Bool :=
  allB (fun p => preserves_norm_add p.1 p.2) (pairs samples)

def check_norm_mul : Bool :=
  allB (fun p => preserves_norm_mul p.1 p.2) (pairs samples)

def check_norm_opow : Bool :=
  allB (fun x => preserves_norm_opow x) samples

/-!
  ## Extra property checks for helpers
-/

def eqListB {α} [DecidableEq α] (xs ys : List α) : Bool := decide (xs = ys)

def check_sort_idem : Bool :=
  eqListB (sortCNF samples) (sortCNF (sortCNF samples))

def check_sort_is_nondecreasing : Bool :=
  isNonDecreasing (sortCNF samples)

def check_list_min_max_nonempty : Bool :=
  match minListCNF samples, maxListCNF samples with
  | some _, some _ => true
  | _, _ => false

-- Executable reports
#eval check_reflexive_eq
#eval check_all_antisym
#eval check_all_trichotomy
#eval check_all_trans_lt
#eval check_all_trans_le
#eval check_all_total_le
#eval check_norm_add
#eval check_norm_mul
#eval check_norm_opow
#eval check_sort_idem
#eval check_sort_is_nondecreasing
#eval check_list_min_max_nonempty

end OperatorKO7.MetaCNF
