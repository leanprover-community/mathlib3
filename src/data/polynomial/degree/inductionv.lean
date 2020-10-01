import tactic
import data.polynomial.degree.basic
import data.polynomial.degree.trailing_degree
import logic.function.basic
import algebra.big_operators.basic


open_locale big_operators
open_locale classical

open function polynomial finsupp finset

namespace reverse

variables {R : Type*} [semiring R] {f : polynomial R}

lemma nonempty_of_card_nonzero {α : Type*} {s : finset α} : s.card ≠ 0 → s.nonempty :=
begin
  contrapose,
  push_neg,
  rw [nonempty_iff_ne_empty, not_not, card_eq_zero, imp_self],
  exact trivial,
end

lemma card_two_d {sup : finset ℕ} : 2 ≤ sup.card → finset.min' sup (begin
  apply nonempty_of_card_nonzero,linarith,
end) ≠ finset.max' sup (begin
  apply nonempty_of_card_nonzero,linarith,
end) :=
begin
  intro,
  apply ne_of_lt,
  apply finset.min'_lt_max'_of_card,
  exact nat.succ_le_iff.mp a,
end


lemma leading_coeff_nonzero_of_nonzero : f ≠ 0 ↔ leading_coeff f ≠ 0 :=
begin
  exact not_congr leading_coeff_eq_zero.symm,
end

def inj_mul (x : R) := ∀ ⦃a b : R⦄ , x*a=x*b → a=b

lemma non_zero_of_nonempty_support : f.1.nonempty → f ≠ 0 :=
begin
  intro,
  cases a with N Nhip,
  rw mem_support_iff_coeff_ne_zero at Nhip,
  finish,
end

lemma nonempty_support_of_non_zero : f ≠ 0 → f.1.nonempty :=
begin
  intro fne,
  rw nonempty_iff_ne_empty,
  apply ne_empty_of_mem,
  rw mem_support_iff_coeff_ne_zero,
  exact leading_coeff_nonzero_of_nonzero.mp fne,
end

lemma non_zero_iff : f.1.nonempty ↔ f ≠ 0 :=
begin
  split,
    { exact non_zero_of_nonempty_support, },
    { exact nonempty_support_of_non_zero, },
end

lemma zero_iff : ¬ f.1.nonempty ↔ f = 0 :=
begin
  rw not_congr,
    { exact not_not, },
    { exact non_zero_iff, },
end

lemma nat_trailing_degree_le_of_mem_supp (a : ℕ) :
  a ∈ f.support → nat_trailing_degree f ≤ a:=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact nat_trailing_degree_le_of_ne_zero,
end

@[simp] lemma trailing_coeff_zero : trailing_coeff (0 : polynomial R) = 0 := rfl

@[simp] lemma trailing_coeff_eq_zero : trailing_coeff f = 0 ↔ f = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma trailing_coeff_nonzero_of_nonzero : f ≠ 0 ↔ trailing_coeff f ≠ 0 :=
begin
  apply not_congr trailing_coeff_eq_zero.symm,
end

lemma le_degree_of_mem_supp (a : ℕ) :
  a ∈ f.support → a ≤ nat_degree f :=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact le_nat_degree_of_ne_zero,
end

lemma nat_trailing_degree_mem_support_of_nonzero : f ≠ 0 → nat_trailing_degree f ∈ f.support :=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact trailing_coeff_nonzero_of_nonzero.mp,
end



lemma defs_by_Johann_trailing {R : Type*} [semiring R] {f : polynomial R} (h : f ≠ 0) :
  nat_trailing_degree f = f.support.min' (non_zero_iff.mpr h) :=
begin
  apply le_antisymm,
  { apply le_min',
    intros y hy,
    exact nat_trailing_degree_le_of_mem_supp y hy },
  { apply finset.min'_le,
    rw mem_support_iff_coeff_ne_zero,
    exact trailing_coeff_nonzero_of_nonzero.mp h, },
end


lemma defs_by_Johann {R : Type*} [semiring R] {f : polynomial R} (h : f ≠ 0) :
  f.nat_degree = f.support.max' (non_zero_iff.mpr h) :=
begin
  apply le_antisymm,
  { apply finset.le_max',
    rw mem_support_iff_coeff_ne_zero,
    exact leading_coeff_nonzero_of_nonzero.mp h, },
  { apply max'_le,
    intros y hy,
    exact le_degree_of_mem_supp y hy, }
end


lemma defs_by_Johann_support {R : Type*} [semiring R] {f : polynomial R} (h : f.support.nonempty) :
  f.nat_degree = f.support.max' h :=
begin
  apply le_antisymm,
  { apply finset.le_max',
    rw finsupp.mem_support_iff,
    show f.leading_coeff ≠ 0,
    rw [ne.def, polynomial.leading_coeff_eq_zero],
    rwa [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty] at h, },
  { apply polynomial.le_nat_degree_of_ne_zero,
    have := finset.max'_mem _ h,
    rwa finsupp.mem_support_iff at this, }
end

lemma defs_with_Johann {h : f.support.nonempty} : nat_trailing_degree f = f.support.min' h :=
begin
  apply le_antisymm,
  { apply nat_trailing_degree_le_of_ne_zero,
    have := finset.min'_mem _ h,
    rwa finsupp.mem_support_iff at this, },
  { apply min'_le,
    rw finsupp.mem_support_iff,
    show trailing_coeff f ≠ 0,
    rw [ne.def, trailing_coeff_eq_zero],
    rwa [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty] at h, },
end


noncomputable def remove_leading_coefficient (f : polynomial R) : polynomial R := (∑ (i : ℕ) in finset.range f.nat_degree, (C (f.coeff i)) * X^i)

@[simp] lemma support_remove_leading_coefficient_sub : (remove_leading_coefficient f).support ⊆ range f.nat_degree :=
begin
  unfold remove_leading_coefficient,
  intros a,
  simp_rw [mem_support_iff_coeff_ne_zero, (finset_sum_coeff (range (nat_degree f)) (λ (b : ℕ), C (coeff f b) * X ^ b) a), coeff_C_mul_X (f.coeff _) _ a],
  finish,
end


lemma not_mem_of_not_mem_supset {a b : finset ℕ} (h : a ⊆ b) {n : ℕ} : n ∉ b → n ∉ a :=
begin
  apply mt,
  solve_by_elim,
end

@[simp] lemma support_remove_leading_coefficient_ne : f.nat_degree ∉ (remove_leading_coefficient f).support :=
begin
  apply not_mem_of_not_mem_supset support_remove_leading_coefficient_sub,
  exact not_mem_range_self,
end


@[simp] lemma ne_nat_degree_of_mem_support_remove {a : ℕ} : a ∈ (remove_leading_coefficient f).support → a ≠ f.nat_degree :=
begin
  contrapose,
  push_neg,
  intro,
  rw a_1,
  exact support_remove_leading_coefficient_ne,
end






lemma mem_diff_of_mem_remove_leading_coefficient {a : ℕ} : a ∈ (remove_leading_coefficient f).support → a ∈ (f.support \ {f.nat_degree}) :=
begin
  rw [mem_sdiff, mem_support_iff_coeff_ne_zero, mem_support_iff_coeff_ne_zero, not_mem_singleton],
  intro,
  split,
    { intro,
      apply a_1,
      unfold remove_leading_coefficient,
      simp only [coeff_X_pow, mul_boole, finset_sum_coeff, coeff_C_mul, mem_range, finset.sum_ite_eq],
      split_ifs,
        { assumption, },
        { refl, }, },
    { apply ne_nat_degree_of_mem_support_remove,
      rwa mem_support_iff_coeff_ne_zero, },
end

@[simp] lemma coeff_remove_eq_coeff_of_ne {a : ℕ} (h : a ≠ f.nat_degree) : (remove_leading_coefficient f).coeff a = f.coeff a :=
begin
  unfold remove_leading_coefficient,
  simp_rw [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_boole, finset.sum_ite_eq],
  split_ifs,
    { refl, },
    { symmetry,
      apply coeff_eq_zero_of_nat_degree_lt,
      rw [mem_range, not_lt] at h_1,
      exact lt_of_le_of_ne h_1 (ne.symm h), },
end

@[simp] lemma coeff_remove_nat_degree : (remove_leading_coefficient f).coeff f.nat_degree = 0 :=
begin
  unfold remove_leading_coefficient,
  simp only [coeff_X_pow, mul_boole, not_mem_range_self, finset_sum_coeff, coeff_C_mul, if_false, finset.sum_ite_eq],
end

lemma mem_remove_leading_coefficient_of_mem_diff {a : ℕ} : a ∈ (f.support \ {f.nat_degree}) → a ∈ (remove_leading_coefficient f).support :=
begin
  rw [mem_sdiff, mem_support_iff_coeff_ne_zero, mem_support_iff_coeff_ne_zero, not_mem_singleton],
  intro,
  cases a_1 with fa asmall,
  rwa coeff_remove_eq_coeff_of_ne asmall,
end

lemma support_remove_leading_coefficient (f0 : f ≠ 0) : (remove_leading_coefficient f).support = f.support \ {f.nat_degree} :=
begin
  ext,
  split,
    { rw mem_support_iff_coeff_ne_zero,
      by_cases ha : a = f.nat_degree,
        { rw ha,
          intro,
          exfalso,
          exact a_1 coeff_remove_nat_degree, },
        { rw [coeff_remove_eq_coeff_of_ne ha, mem_sdiff, not_mem_singleton],
          intro,
          exact ⟨mem_support_iff_coeff_ne_zero.mpr a_1 , ha ⟩,
        }, },
    { exact mem_remove_leading_coefficient_of_mem_diff, },
end

lemma remove_leading_coefficient_nonzero_of_large_support (f0 : 2 ≤ f.support.card) : (remove_leading_coefficient f).support.nonempty :=
begin
  have fn0 : f ≠ 0,
    rw [← non_zero_iff, nonempty_iff_ne_empty],
    intro,
    rw ← card_eq_zero at a,
    finish,
  rw nonempty_iff_ne_empty,
  apply ne_empty_of_mem,
  rotate,
  use nat_trailing_degree f,
  rw [mem_support_iff_coeff_ne_zero, coeff_remove_eq_coeff_of_ne, ← mem_support_iff_coeff_ne_zero],
    { exact nat_trailing_degree_mem_support_of_nonzero fn0, },
    { rw [defs_by_Johann fn0, defs_by_Johann_trailing fn0],
      exact card_two_d f0, },
end

lemma nat_degree_remove_leading_coefficient (f0 : 2 ≤ f.support.card) : (remove_leading_coefficient f).nat_degree < f.nat_degree :=
begin
  rw defs_by_Johann (non_zero_iff.mp (remove_leading_coefficient_nonzero_of_large_support f0)),
  apply nat.lt_of_le_and_ne _ (ne_nat_degree_of_mem_support_remove ((remove_leading_coefficient f).support.max'_mem (non_zero_iff.mpr _))),
  apply max'_le,
    rw support_remove_leading_coefficient,
      { intros y hy,
        apply le_nat_degree_of_ne_zero,
        rw mem_sdiff at hy,
        exact (mem_support_iff_coeff_ne_zero.mp hy.1), },
      { rw ← non_zero_iff,
        apply nonempty_of_card_nonzero,
        omega, },
end


lemma support_remove_lt (h : f ≠ 0) : (remove_leading_coefficient f).support.card < f.support.card :=
begin
  rw support_remove_leading_coefficient h,
  apply card_lt_card,
  split,
    { exact f.support.sdiff_subset {nat_degree f}, },
    { intro,
      rw defs_by_Johann h at a,
      have : f.support.max' (non_zero_iff.mpr h) ∈ f.support \ {f.support.max' (non_zero_iff.mpr h)} := a (max'_mem f.support (non_zero_iff.mpr h)),
      simp only [mem_sdiff, eq_self_iff_true, not_true, and_false, mem_singleton] at this,
      cases this, },
end

lemma sum_leading_term_remove (f : polynomial R) : f = (remove_leading_coefficient f) + (C f.leading_coeff) * X^f.nat_degree :=
begin
  ext1,
  by_cases nm : n = f.nat_degree,
    { rw [nm, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_remove_nat_degree, zero_add],
      refl, },
    { simp only [*, coeff_remove_eq_coeff_of_ne nm, coeff_X_pow f.nat_degree n, add_zero, coeff_C_mul, coeff_add, if_false, mul_zero], },
end

lemma nat_degree_mem_support_of_nonzero : f ≠ 0 → f.nat_degree ∈ f.support :=
begin
  intro,
  apply (f.3 f.nat_degree).mpr,
  exact leading_coeff_nonzero_of_nonzero.mp a,
end

lemma add_cancel {a b : R} {h : a=0} : a+b=b :=
begin
  rw [h, zero_add],
end

lemma monomial_of_card_support_le_one (h : f.support.card ≤ 1) : f = C f.leading_coeff * X^f.nat_degree :=
begin
  by_cases f0 : f = 0,
  { ext1,
    rw [f0, leading_coeff_zero, C_0, zero_mul], },
  conv
  begin
    congr,
    rw sum_leading_term_remove f,
    skip,
  end,
  apply add_cancel,
  rw [← support_eq_empty, ← card_eq_zero],
  apply nat.eq_zero_of_le_zero (nat.lt_succ_iff.mp _),
  convert support_remove_lt f0,
  apply le_antisymm _ h,
  exact card_le_of_subset (singleton_subset_iff.mpr (nat_degree_mem_support_of_nonzero f0)),
end

lemma mem_support_term {n a : ℕ} {c : R} : a ∈ (C c * X ^ n).support → a = n :=
begin
  intro,
  rw [mem_support_iff_coeff_ne_zero, coeff_C_mul_X c n a] at a_1,
  finish,
end

lemma support_term_nonzero {n : ℕ} {c : R} (h : c ≠ 0): (C c * X ^ n).support = singleton n :=
begin
  ext1,
  rw mem_singleton,
  split,
    { exact mem_support_term, },
    { intro,
      rwa [mem_support_iff_coeff_ne_zero, ne.def, a_1, coeff_C_mul, coeff_X_pow_self n, mul_one], },
end

lemma sum_lt_support (h : 2 ≤ f.support.card) : ∃ f0 f1 : polynomial R , f0.support.card < f.support.card ∧ f1.support.card < f.support.card ∧ f = f0+f1 :=
begin
  use (C (leading_coeff f))*X^f.nat_degree,
  use (remove_leading_coefficient f),
  split,
    { apply lt_of_lt_of_le _ h,
      convert one_lt_two,
      rw [support_term_nonzero, card_singleton],
      rw [← leading_coeff_nonzero_of_nonzero, ← non_zero_iff],
      apply nonempty_of_card_nonzero,
      omega, },
    { split,
        { apply support_remove_lt,
          rw ← non_zero_iff,
          apply nonempty_of_card_nonzero,
          omega, },
        { rw add_comm,
          exact sum_leading_term_remove f, }, },
end

lemma nonzero_or_of_nonzero_sum {a b : R} : a+b ≠ 0 → a ≠ 0 ∨ b ≠ 0 :=
begin
  contrapose,
  push_neg,
  intro,
  cases a_1 with a0 b0,
  rw [a0, b0, add_zero],
end

@[simp] lemma support_union {f g : polynomial R} {y : ℕ} : y ∈ support (f+g) → y ∈ support f ∪ support g :=
begin
  rw [mem_support_iff_coeff_ne_zero, coeff_add, mem_union, mem_support_iff_coeff_ne_zero,  mem_support_iff_coeff_ne_zero],
  exact nonzero_or_of_nonzero_sum,
end


lemma pol_ind_with_N (N : ℕ) {P : polynomial R → Prop}
 (Psum : ∀ (p q : polynomial R), (P p) → (P q) → (P (p+q)))
 (Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)) :
 ∀ p : polynomial R, p.support.card ≤ N.succ → P p :=
begin
  induction N,
    { intros p hp,
      rw monomial_of_card_support_le_one hp,
      exact Pmon p.leading_coeff p.nat_degree, },

    { intros p hp,
      by_cases p0 : p = 0,
        { rw [p0, ← zero_mul X, ← C_0, ← pow_one X],
          exact Pmon 0 1, },
        { rw sum_leading_term_remove p,
          apply Psum,
            { apply N_ih,
              apply nat.le_of_lt_succ,
              apply gt_of_ge_of_gt hp _,
              exact support_remove_lt p0, },
            { exact Pmon (leading_coeff p) (nat_degree p), }, }, },
end

lemma pol_ind (f : polynomial R) {P : polynomial R → Prop}
 {Psum : ∀ p q : polynomial R, (P p) → (P q) → (P (p+q))}
 {Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)} :
 P f :=
begin
  apply pol_ind_with_N f.support.card Psum Pmon,
  exact f.support.card.le_succ,
end

lemma mul_X_pow_ne_zero {n : ℕ} : f ≠ 0 → f*X^n ≠ 0 :=
begin
  intros a fa,
  apply a,
  exact mul_X_pow_eq_zero fa,
end

lemma min'_union {α : Type*} [decidable_linear_order α] {s t u : finset α}
 {hs : s.nonempty} {ht : t.nonempty} {hu : u.nonempty} {hust : u ⊆ s ∪ t} {y : α} :
 (y ≤ min' s hs) → (y ≤ min' t ht) → (y ≤ min' u hu) :=
begin
  intros is it,
  apply le_min',
  intros x hx,
  have : x ∈ s ∪ t,
    exact hust hx,
  rw mem_union at this,
  cases this;
    { apply le_trans _ (min'_le _ x this),
      assumption, },
end

theorem le_nat_trailing_degree_C_mul_X_pow (n : ℕ) (H : f ≠ 0) : n ≤ nat_trailing_degree (f * X^n) :=
begin
  revert H,
  apply pol_ind f,
    intros p q hp hq hpq,
    by_cases p0 : p = 0,
      rw [p0, zero_add],
      rw [p0, zero_add] at hpq,
      exact hq hpq,
      by_cases q0 : q = 0,
        rw [q0, add_zero],
        exact hp p0,

        simp_rw [defs_by_Johann_trailing (mul_X_pow_ne_zero hpq), add_mul p q (X^n)],
    apply min'_union,
    apply support_add,
    rw ← defs_by_Johann_trailing (mul_X_pow_ne_zero p0),
    exact hp p0,
    rw ← defs_by_Johann_trailing (mul_X_pow_ne_zero q0),
    exact hq q0,

    intros r m hmon,
    rw [mul_assoc, ← pow_add X m n],
    rw defs_by_Johann_trailing,
    apply le_min',
    intros y hy,
    rw [support_term_nonzero, mem_singleton] at hy,
    rw hy,
    exact nat.le_add_left n m,
      { intro,
        apply hmon,
        rw [a, C_0, zero_mul], },

      { intro,
        apply hmon,
        rw [← leading_coeff_eq_zero, leading_coeff_monomial] at a,
        rw [a, C_0, zero_mul], },
end

def rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i) + i*min 1 (i-N)



@[simp] lemma rev_at_small {N n : ℕ} (H : n ≤ N) : rev_at N n = N-n :=
begin
--  sorry,
--/-
  unfold rev_at,
  rw [nat.sub_eq_zero_of_le H, min_eq_right (nat.zero_le 1), mul_zero, add_zero],
--/
end

@[simp] lemma rev_at_large {N n : ℕ} (H : N < n) : rev_at N n = n :=
begin
--  sorry,
--/-
  unfold rev_at,
  rw [min_eq_left, mul_one, nat.sub_eq_zero_of_le (le_of_lt H), zero_add],
  rw [nat.one_succ_zero, nat.succ_le_iff],
  exact nat.sub_pos_of_lt H,
--/
end

@[simp] lemma rev_at_invol {N n : ℕ} : rev_at N (rev_at N n) = n :=
begin
  unfold rev_at,
  by_cases n ≤ N,
  {
    simp [nat.sub_eq_zero_of_le (nat.sub_le N n),nat.sub_eq_zero_of_le h, nat.sub_sub_self h], },
  { rw not_le at h,
    simp [nat.sub_eq_zero_of_le (le_of_lt (h)), min_eq_left (nat.succ_le_of_lt (nat.sub_pos_of_lt h))], },
end

/- questo lemma credo che è falso
lemma rev_at_add {M N m n : ℕ} : rev_at (M + N) (m + n) = rev_at M m + rev_at N n :=
begin
  by_cases n0 : n ≤ N ∧ m ≤ M ∧ m+n ≤ M+N,
    { rcases n0 with ⟨ n0, m0, mn0 ⟩,
      rw rev_at_small n0,
        rw rev_at_small m0,
        rw rev_at_small (add_le_add m0 n0),
        omega, },
    {
      push_neg at n0,
      sorry,
    },
end
-/



def rev_support (f : polynomial R) : set ℕ := {a : ℕ | ∃ aa ∈ f.1 , a = rev_at (nat_degree f) aa}

lemma finset_of_bounded {S : set ℕ} (N : ℕ) {nN : ∀ (n ∈ S), n ≤ N} : S.finite :=
set.finite.subset (set.finite_le_nat N) nN

lemma rev_support_finite (f : polynomial R) : (rev_support f).finite :=
begin
--    sorry,
--/-
  refine finset_of_bounded (nat_degree f),
  intros n nH,
  rcases nH with ⟨ rn , r1 , rfl ⟩ ,
  rw (rev_at_small (le_degree_of_mem_supp rn r1)),
  apply (nat_degree f).sub_le rn,
--/
end

--#exit



def reflect : ℕ → polynomial R → polynomial R := λ N : ℕ , λ p : polynomial R , ⟨ (rev_at N '' ↑(p.support)).to_finset , λ i : ℕ , p.coeff (rev_at N i) , begin
  simp_rw [set.mem_to_finset, set.mem_image, mem_coe, mem_support_iff],
  intro,
  split,
    { intro a_1,
      rcases a_1 with ⟨ a , ha , rfl⟩,
      rwa rev_at_invol, },
    { intro,
      use (rev_at N a),
      rwa [rev_at_invol, eq_self_iff_true, and_true], },
end ⟩

@[simp] lemma reflect_add {f g : polynomial R} {n : ℕ} : reflect n (f+g) = reflect n f + reflect n g :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk, coeff_add],
end

lemma coeff_eq_zero_of_not_mem_support {a : ℕ} : a ∉ f.support → f.coeff a = 0 :=
begin
--  sorry,
--/-
  contrapose,
  push_neg,
  exact mem_support_iff_coeff_ne_zero.mpr,
--/
end

@[simp] lemma reflect_term (N n : ℕ) {c : R} : reflect N (C c * X ^ n) = C c * X ^ (rev_at N n) :=
begin
  ext1,
  unfold reflect,
  rw coeff_mk,
  by_cases h : rev_at N n = n_1,
    { rw [h, coeff_C_mul, coeff_C_mul, coeff_X_pow_self, ← h, rev_at_invol, coeff_X_pow_self], },
    { rw coeff_eq_zero_of_not_mem_support,
        { symmetry,
          apply coeff_eq_zero_of_not_mem_support,
          intro,
          apply h,
          exact (mem_support_term a).symm, },
        {
          intro,
          apply h,
          rw ← @rev_at_invol N n_1,
          apply congr_arg _,
          exact (mem_support_term a).symm, }, },
end




--#exit

@[simp] lemma reflect_mul_termv {N n : ℕ} {H : f.nat_degree ≤ N } : reflect (N+n) (f * X ^ n) = reflect N f :=
begin
  sorry,
/-
  by_cases f0 : f = 0,
    { rw [f0, zero_mul],
      refl, },
    { ext1,
      unfold reflect,
      dsimp,
      by_cases n1small : n_1 ≤ N,
        { rw [rev_at_small (le_add_right n1small), rev_at_small n1small, nat.sub_add_comm n1small,coeff_mul_X_pow], },
        {
          rw not_le at n1small,
          rw [rev_at_large n1small, coeff_eq_zero_of_nat_degree_lt (gt_of_gt_of_ge n1small H)],
          by_cases n1medium : n_1 ≤ N + n,
            rw rev_at_small n1medium,
            rw coeff_eq_zero_of_lt_nat_trailing_degree,
            rw defs_by_Johann_trailing _,
            have : n ≤ (f * X ^ n).support.min' sorry,
              apply le_trailing_degree_C_mul_X_pow,

            rw nat.sub_add_comm _,
            rw coeff_mul_X_pow,
          sorry,
        },}
-/
end

lemma reflect_mul {f g : polynomial R} : reflect (f.nat_degree+g.nat_degree) (f*g) = reflect f.nat_degree (f) * reflect g.nat_degree (g) :=
begin
  revert f,
  apply pol_ind g,
    { intros p q hp hq f,
      rw [mul_add, reflect_add, reflect_add, mul_add, @hp f, @hq f], },
    {
      intros r n f Hf,
      apply pol_ind f,
        {
          intros p q hp hq,
          rw [reflect_add, add_mul, add_mul, reflect_add, reflect_term, hp, hq, reflect_term],
        },
        {
          intros r m,
          rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add, ← mul_assoc, ← C_mul],
          repeat {rw reflect_term},
          rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add, ← mul_assoc, ← C_mul],
          repeat {apply congr_arg},
          by_cases n0 : n ≤ Ng,
            by_cases m0 : m ≤ Nf,
              rw rev_at_small n0,
              rw rev_at_small m0,
              rw add_comm,
              rw rev_at_small (add_le_add n0 m0),
              zify,



          sorry,
        },
    },
end


#exit



lemma reflect_mul {f g : polynomial R} {Nf Ng : ℕ} {Hf : (f).nat_degree ≤ Nf} {Hg : (g).nat_degree ≤ Ng} : reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  revert f,
  apply pol_ind g,
    { intros p q hp hq f hf,
      rw [mul_add, reflect_add, reflect_add, mul_add, @hp f hf, @hq f hf], },
    {
      intros r n f Hf,
      apply pol_ind f,
        {
          intros p q hp hq,
          rw [reflect_add, add_mul, add_mul, reflect_add, reflect_term, hp, hq, reflect_term],
        },
        {
          intros r m,
          rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add, ← mul_assoc, ← C_mul],
          repeat {rw reflect_term},
          rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add, ← mul_assoc, ← C_mul],
          repeat {apply congr_arg},
          by_cases n0 : n ≤ Ng,
            by_cases m0 : m ≤ Nf,
              rw rev_at_small n0,
              rw rev_at_small m0,
              rw add_comm,
              rw rev_at_small (add_le_add n0 m0),
              zify,



          sorry,
        },
    },
end




#exit


@[simp] lemma reflect_zero {n : ℕ} : reflect n (0 : polynomial R) = 0 :=
begin
  refl,
end



@[simp] lemma reflect_smul (N : ℕ) {r : R} : reflect N (C r * f) = C r * (reflect N f) :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk, coeff_C_mul],
end

lemma reflect_mul_term (n : ℕ) (g : polynomial R) {Nf Ng : ℕ} {Hg : (g).nat_degree ≤ Ng} :
(reflect (n + Ng) (g * X ^ n)) = (reflect Ng g) :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk] at *,
  by_cases n1s : n_1 ≤ Ng,
    rw rev_at_small n1s,
    rw rev_at_small _,
    rw [add_comm n Ng],
    have : Ng + n - n_1 = (Ng -n_1)+ n,omega,
    rw this,
    apply coeff_mul_X_pow,
    exact le_add_left n1s,
    have Ngs : Ng < n_1, exact not_le.mp n1s,
    rw rev_at_large Ngs,
    have gdl : g.nat_degree < n_1,exact gt_of_gt_of_ge Ngs Hg,
    rw coeff_eq_zero_of_nat_degree_lt gdl,
    by_cases hn : n_1 ≤ n + Ng,
      rw rev_at_small hn,
      have : n+Ng - n_1 < n,
        sorry,
      apply coeff_eq_zero_of_lt_nat_trailing_degree,
      rw defs_by_Johann_trailing,
      apply gt_of_ge_of_gt _ this,
      apply le_min',
      intros y hy,
      sorry,
      sorry,
      rw not_le at hn,
      rw rev_at_large hn,
      apply coeff_eq_zero_of_nat_degree_lt,
      apply gt_of_gt_of_ge hn _,


--  tidy,
  sorry,
end


#exit
@[simp] lemma reflect_mul_term (n m : ℕ) {r : R} (g : polynomial R) {Nf Ng : ℕ} {Hf : (f).nat_degree ≤ Nf} {Hg : (g).nat_degree ≤ Ng} :
(reflect (Nf + Ng) (C r * g * X ^ n)).coeff m = (C r * (reflect Ng g) * X ^ rev_at Nf n).coeff m :=
begin
  unfold reflect,
  simp * at *,
  tidy,
  sorry,
end



lemma reflect_mul_ind {f g : polynomial R} {Nf Ng : ℕ} {Hf : (f).nat_degree ≤ Nf} {Hg : (g).nat_degree ≤ Ng} : reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  revert g,
  apply pol_ind f,
    { sorry, },
--      intros p q hp hq g Hg,
--      ext1,
--      simp only [add_mul, coeff_add, reflect_add],
--      finish, },
    { intros p n g Hg,
      ext1,
      simp only [reflect_term],
      rw [mul_assoc, mul_assoc, X_pow_mul, X_pow_mul, ← mul_assoc, ← mul_assoc],
      rw reflect_mul_term n n_1 (g),
      exact f,
      assumption,
      assumption,



--      simp [reflect_term, reflect_mul_term],

      sorry, },




  sorry,
end

#exit
lemma reflect_mul_ind (N : ℕ) {f g : polynomial R} {h : f.nat_degree ≤ N} : reflect N (f*g) = reflect N (f) * reflect N (g) :=
begin
  revert g,
  apply pol_ind f,
    intros p q hp hq g,
    simp [add_mul],


  sorry,
end

end reverse
