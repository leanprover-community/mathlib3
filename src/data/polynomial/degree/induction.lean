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

def shift_by : ℕ → ℕ → ℕ := λ n , λ i , i+n

@[simp] lemma shift_by_zero : shift_by 0 = id :=
rfl

@[simp] lemma shift_by_add (a b : ℕ): shift_by a ∘ shift_by b = shift_by (a+b) :=
begin
  ext1,
  unfold shift_by,
  rw [comp_app, add_comm a b, add_assoc],
end

@[simp] lemma shift_by_add_v (a b c : ℕ): shift_by (shift_by a b) c = shift_by (a+b) c :=
begin
  unfold shift_by,
  rw add_comm b a,
end

@[simp] lemma shift_small {N a : ℕ} (H : a ≤ N) : shift_by a (N - a) = N :=
nat.sub_add_cancel H

lemma shift_by_monotone (i : ℕ) : monotone (shift_by i) :=
begin
  intros m n hmn,
  exact add_le_add_right hmn i,
end

@[simp] lemma mul_X_mem_support {n : ℕ} : n.succ ∈ (f*X).support ↔ n ∈ f.support :=
begin
  repeat {rw mem_support_iff_coeff_ne_zero},
  rw coeff_mul_X,
end

@[simp] lemma mul_X_mem_support_shift {n : ℕ} : shift_by 1 n ∈ (f*X).support ↔ n ∈ f.support :=
begin
  unfold shift_by,
  rw [← nat.succ_eq_add_one, mul_X_mem_support],
end

@[simp] lemma nonzero_of_mem_support_mul_X {n : ℕ} : n ∈ (f*X).support → 1 ≤ n :=
begin
  intro a,
  suffices : n ≠ 0, by omega,
  intro n0,
  rw [n0,mem_support_iff] at a,
  apply a,
  exact coeff_mul_X_zero f,
end

@[simp] lemma mul_X_mem_support_shift' {n : ℕ} : n ∈ (f*X).support ↔ 1 ≤ n ∧ (n-1) ∈ f.support :=
begin
  split,
    { intro,
      refine ⟨ nonzero_of_mem_support_mul_X a , _ ⟩,
      rwa [← mul_X_mem_support_shift, shift_small (nonzero_of_mem_support_mul_X a)], },
    { intro,
      convert mul_X_mem_support_shift.mpr a.2,
      exact (shift_small a.1).symm, },
end


lemma mul_X_support : (f*X).support = ((shift_by 1) '' ↑(f.support)).to_finset :=
begin
  ext1,
  rw [mul_X_mem_support_shift', set.mem_to_finset],
  split,
    { intro,
      rw [← coe_image, ← shift_small a_1.left],
      exact (mem_image_of_mem (shift_by 1) a_1.right), },
    { intro,
      rw set.mem_image at a_1,
      rcases a_1 with ⟨ a_1 , ha_1 , rfl ⟩,
      refine ⟨ le_add_left rfl.ge , ha_1 ⟩, },
end


lemma mul_X_pow_support (n : ℕ) : (f*X^n).support = ((shift_by n) '' ↑(f.support)).to_finset :=
begin
  induction n with n hn,
    { rw [pow_zero, mul_one, shift_by_zero],
      ext,
      simp, },
    {
      rw [nat.succ_eq_add_one, pow_add, pow_one, ← mul_assoc, mul_X_support, hn],
      rw [set.to_finset_inj, set.coe_to_finset],
      repeat {rw ← coe_image},
      rw [image_image, shift_by_add, add_comm],
    },
end



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

lemma non_zero_of_nonempty_support : f.support.nonempty → f ≠ 0 :=
begin
  intro,
  cases a with N Nhip,
  rw mem_support_iff_coeff_ne_zero at Nhip,
  finish,
end

lemma nonempty_support_of_non_zero : f ≠ 0 → f.support.nonempty :=
begin
  intro fne,
  rw nonempty_iff_ne_empty,
  apply ne_empty_of_mem,
  rw mem_support_iff_coeff_ne_zero,
  exact leading_coeff_nonzero_of_nonzero.mp fne,
end

lemma non_zero_iff : f.support.nonempty ↔ f ≠ 0 :=
begin
  split,
    { exact non_zero_of_nonempty_support, },
    { exact nonempty_support_of_non_zero, },
end

lemma zero_iff : ¬ f.support.nonempty ↔ f = 0 :=
begin
  rw not_congr,
    { exact not_not, },
    { exact non_zero_iff, },
end

lemma zero_iff_empty : f.support = ∅ ↔ f = 0 :=
begin
  exact support_eq_empty,
end

lemma le_nat_degree_of_mem_supp (a : ℕ) :
  a ∈ f.support → a ≤ nat_degree f:=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact le_nat_degree_of_ne_zero,
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

lemma support_remove_leading_coefficient_v (f0 : f ≠ 0) : (remove_leading_coefficient f).support = f.support \ {f.nat_degree} :=
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

lemma support_remove_leading_coefficient : (remove_leading_coefficient f).support = f.support \ {f.nat_degree} :=
begin
  by_cases f0 : f = 0,
    { rw f0,
      apply (support_eq_empty).mpr,
      refl, },
    { ext,
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
        { exact mem_remove_leading_coefficient_of_mem_diff, }, },
end

lemma xx {n : ℕ} : n ≠ 0 → 1 ≤ n :=
begin
  intro,
  omega,
end

lemma support_remove_leading_coefficient_succ (h : f ≠ 0) : (remove_leading_coefficient f).support.card.succ = f.support.card :=
begin
  rw support_remove_leading_coefficient,
  rw card_sdiff,
    { rw [card_singleton, nat.succ_eq_add_one, nat.sub_add_cancel],
      apply xx,
      intro,
      rw card_eq_zero at a,
      apply h,
      exact zero_iff_empty.mp a, },
    { intros a,
      rw mem_singleton,
      rintro rfl,
      rw defs_by_Johann h,
      apply max'_mem f.support, },
end

/-
lemma xxx {s t : finset ℕ} : s ⊆ t ∧ s ≠ t → s ⊂ t:=
begin
  intro,
  cases a,
  fsplit,
    { exact a_left, },
    { suggest,

      sorry, },
end
--#exit
lemma xxx {s : finset ℕ} {n : ℕ} {h : n ∈ s} : s \ singleton n ⊂ s :=
begin
--  rw subset
  split,
    exact sdiff_subset s {n},
    apply set.nonempty_diff.mp _,
  rw sdiff
  rw ← sdiff_eq_self,
  apply set.not_subset.mpr,
  use n,
  split,
    exact h,

    rw singleton_disjoint,


  rw set.not_subset,
end
-/

lemma support_remove_leading_coefficient_lt (h : f ≠ 0) : (remove_leading_coefficient f).support.card < f.support.card :=
begin
  apply card_lt_card,
  rw [support_remove_leading_coefficient, ssubset_iff_of_subset],
    { use f.nat_degree,
      rw [← mem_sdiff, sdiff_sdiff_self_left, inter_singleton_of_mem, mem_singleton],
      rw mem_support_iff_coeff_ne_zero,
      exact leading_coeff_nonzero_of_nonzero.mp h, },
    { exact f.support.sdiff_subset {nat_degree f}, },
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
end


lemma support_remove_lt (h : f ≠ 0) : (remove_leading_coefficient f).support.card < f.support.card :=
begin
  rw support_remove_leading_coefficient,
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

lemma term_of_card_support_le_one (h : f.support.card ≤ 1) : f = C f.leading_coeff * X^f.nat_degree :=
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

lemma sset {s : finset ℕ} : s \ s = ∅ :=
begin
  exact sdiff_self s,
end



lemma mem_support_term {n a : ℕ} {c : R} : a ∈ (C c * X ^ n).support → a = n :=
begin
  intro,
  rw [mem_support_iff_coeff_ne_zero, coeff_C_mul_X c n a] at a_1,
  finish,
end

lemma support_term_nonzero {c : R} {n : ℕ} (h : c ≠ 0): (C c * X ^ n).support = singleton n :=
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

lemma mem_support_monomial {R : Type*} [semiring R] {n a : ℕ} :
  a ∈ (X ^ n : polynomial R).support → a = n :=
begin
  intro,
  rw [mem_support_iff_coeff_ne_zero, coeff_X_pow n a] at a_1,
  finish,
end

lemma support_monomial {R : Type*} [semiring R] {n : ℕ} :
  (X ^ n : polynomial R).support ⊆ singleton n :=
begin
  intros a,
  rw mem_singleton,
  exact mem_support_monomial,
end

lemma support_term (c : R) (n : ℕ) : (C c * X ^ n).support ⊆ singleton n :=
begin
  intro a,
  rw mem_singleton,
  exact mem_support_term,
end


lemma card_support_term_le_one {c : R} {n : ℕ} : (C c * X ^ n).support.card ≤ 1 :=
begin
  rw ← card_singleton n,
  apply card_le_of_subset,
  exact support_term c n,
end

/-
lemma remove_leading_coefficient_zero : remove_leading_coefficient (0 : polynomial R) = 0 :=
begin
  refl,
end
-/

@[simp] lemma nat_degree_monomial {a : R} (n : ℕ) (ha : a ≠ 0) : nat_degree (C a * X ^ n) = n :=
begin
  rw defs_by_Johann,
    { simp_rw support_term_nonzero ha,
      exact max'_singleton n, },
    { intro,
      apply ha,
      rw [← C_inj, C_0],
      apply mul_X_pow_eq_zero a_1, },
end


lemma nat_degree_term_le (a : R) (n : ℕ) : nat_degree (C a * X ^ n) ≤ n :=
begin
  by_cases a0 : a = 0,
    rw [a0, C_0, zero_mul, nat_degree_zero],
    exact nat.zero_le _,


    rw defs_by_Johann,
      { simp_rw [support_term_nonzero a0, max'_singleton n], },
      { intro,
        apply a0,
        rw [← C_inj, C_0],
        apply mul_X_pow_eq_zero a_1, },
end


lemma remove_leading_coefficient_monomial {r : R} {n : ℕ} : remove_leading_coefficient (C r * X^n) = 0 :=
begin
  by_cases h : r = 0,
    { rw [h, C_0, zero_mul],
      refl, },
    { rw [← support_eq_empty, ← sdiff_self (singleton n), support_remove_leading_coefficient],
      congr,
        { exact support_term_nonzero h, },
        { exact nat_degree_monomial n h, }, },
end


lemma remove_leading_coefficient_card : f.support.card ≤ 1 → (remove_leading_coefficient f) = 0 :=
begin
  intro,
  rw [term_of_card_support_le_one a, remove_leading_coefficient_monomial],
end


lemma nat_degree_remove_leading_coefficient_le : (remove_leading_coefficient f).nat_degree ≤ f.nat_degree :=
begin
  by_cases su : f.support.card ≤ 1,
    {
      rw [remove_leading_coefficient_card su, nat_degree_zero],
      exact zero_le f.nat_degree, },
    { apply le_of_lt,
      exact nat_degree_remove_leading_coefficient (nat.succ_le_iff.mpr (not_le.mp su)), },
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


lemma xxy {a b : ℕ} : a ≤ b ↔ a < b.succ :=
begin
  exact nat.lt_succ_iff.symm,
end

lemma yy {s : finset ℕ} : s = ∅ → ¬s.nonempty :=
begin
  intros a a_1,
  cases a_1,
  exact eq_empty_iff_forall_not_mem.mp a a_1_w a_1_h,
end

lemma pol_ind_with_N_bound (P : ℕ → polynomial R → Prop) :
 (∀ (p q : polynomial R), ∀ Np Nq Npq : ℕ , (P Np p) → (P Nq q) → (P Npq (p+q))) →
 (∀ r : R , ∀ n Nd : ℕ , n ≤ Nd → P Nd (C r * X^n)) →
 ∀ p : polynomial R, ∀ Nd : ℕ , p.nat_degree ≤ Nd → P Nd p :=
begin
  intros Psum Pmon p Nd,
  revert p,
  induction Nd,
    { intros p hp,
      convert Pmon p.leading_coeff p.nat_degree 0 hp,
      convert term_of_card_support_le_one _,
      rw ← card_singleton 0,
      apply card_le_of_subset _,
      rw [eq_C_of_nat_degree_le_zero hp, ← mul_one (C (p.coeff 0)), ← pow_zero X],
      exact support_term (p.coeff 0) 0, },

    { intros p hp,
      by_cases p0 : p = 0,
        { rw [p0, ← zero_mul (X^0), ← C_0],
          refine Pmon 0 0 Nd_n.succ (zero_le Nd_n.succ), },
        { rw sum_leading_term_remove p,
          apply Psum,
            { by_cases ps : p.support.card ≤ 1,
                { rw remove_leading_coefficient_card ps,
                  rw [← zero_mul (X^0), ← C_0],
                  refine Pmon 0 0 Nd_n (zero_le Nd_n), },
                { refine Nd_ih _ _,
                  rw ← nat.lt_succ_iff,
                  apply gt_of_ge_of_gt hp _,
                  exact nat_degree_remove_leading_coefficient (not_le.mp ps), }, },
            { exact Pmon (leading_coeff p) _ _ (le_refl _), }, }, },
end




/-

#exit
lemma pol_ind_with_N_bound_vecchio (Nd Ns : ℕ) (P : polynomial R → Prop)
 {Psum : ∀ (p q : polynomial R), (P p) → (P q) → (P (p+q))}
 {Pmon : ∀ r : R , ∀ n : ℕ , n ≤ Nd → P (C r * X^n)} :
 ∀ p : polynomial R, p.nat_degree ≤ Nd → p.support.card ≤ Ns.succ → P p :=
begin
  induction Ns,
    { intros p hp hs,
      rw term_of_card_support_le_one hs,
      apply Pmon p.leading_coeff p.nat_degree hp, },

    { intros p hp,
      by_cases p0 : p = 0,
        { rw [p0, ← zero_mul (X^0), ← C_0],
          intro,
          exact Pmon 0 0 (zero_le Nd), },
        { rw sum_leading_term_remove p,
          intro,
          apply Psum,
            { apply Ns_ih _ (le_trans nat_degree_remove_leading_coefficient_le hp),
              rw ← nat.lt_succ_iff,
              apply gt_of_ge_of_gt a _,
              rw ← sum_leading_term_remove p,
              exact support_remove_lt p0, },
            { exact Pmon (leading_coeff p) (nat_degree p) hp, }, }, },
end






lemma pol_ind_con_bounds (f : polynomial R) {P : ℕ → polynomial R → Prop}
{H : true → (pol_ind_with_N_bound P) } :
 P f :=
begin
  apply pol_ind_with_N f.support.card Psum Pmon,
  exact f.support.card.le_succ,
end



#exit
/-
lemma pol_ind_with_N_bound (N : ℕ) {P : polynomial R → Prop}
 (Psum : ∀ (p q : polynomial R), (P p) → (P q) → (P (p+q)))
 (Pmon : ∀ r : R , ∀ n : ℕ , n ≤ N.succ → P (C r * X^n)) :
 ∀ p : polynomial R, p.nat_degree ≤ N.succ → p.support.card ≤ N.succ → P p :=
begin
  induction N,
    { intros p hp hs,
      rw term_of_card_support_le_one hs,
      apply Pmon p.leading_coeff p.nat_degree hp, },

    { intros p hp,
      by_cases p0 : p = 0,
        { rw [p0, ← zero_mul X, ← C_0, ← pow_one X],
          intro,
          apply Pmon 0 1,omega, },
        { rw sum_leading_term_remove p,
          intro,
          apply Psum,
            { apply N_ih,
              intros r n hn,
              apply Pmon,
              exact nat.le_succ_of_le hn,
--              apply nat.le_of_lt_succ,
--              apply gt_of_ge_of_gt hp _,
              by_cases psu : p.support.card ≤ 1,
                convert nat.zero_le N_n.succ,
                convert nat_degree_zero,
                have : (remove_leading_coefficient p).support = ∅ ,
                  rw support_remove_leading_coefficient p0,
                  rw sdiff_eq_empty_iff_subset,
                  convert support_term p.leading_coeff p.nat_degree,
                  exact term_of_card_support_le_one psu,
                rw ← zero_iff,
                clear psu a p0 hp Pmon N_ih N_n Psum P,
                rw eq_empty_iff_forall_not_mem at this,
                intro,
                cases a,
                exact this a_w a_h,


              rw ← nat.lt_succ_iff,
              apply gt_of_ge_of_gt hp _,
              apply nat_degree_remove_leading_coefficient,
              exact not_le.mp psu,

              rw ← nat.lt_succ_iff,

              apply gt_of_ge_of_gt (a) _,
              rw ← sum_leading_term_remove p,
              exact support_remove_lt p0,
                },
            { apply Pmon (leading_coeff p) (nat_degree p),
              rwa ← sum_leading_term_remove p at a, }, }, },
end
-/



lemma pol_ind_bound (f : polynomial R) {P : polynomial R → Prop}
 {Psum : ∀ p q : polynomial R, (P p) → (P q) → (P (p+q))}
 {Pmon : ∀ r : R , ∀ n : ℕ , n ≤ f.nat_degree.succ → P (C r * X^n)} :
 P f :=
begin
  apply pol_ind_with_N_bound f.nat_degree Psum Pmon,
  exact f.nat_degree.le_succ,
  exact f.support.card.le_succ,
end

-/

lemma pol_ind_with_N (N : ℕ) {P : polynomial R → Prop}
 (Psum : ∀ (p q : polynomial R), (P p) → (P q) → (P (p+q)))
 (Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)) :
 ∀ p : polynomial R, p.support.card ≤ N.succ → P p :=
begin
  induction N,
    { intros p hp,
      rw term_of_card_support_le_one hp,
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

/-
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

lemma coeff_eq_zero_of_not_mem_support {a : ℕ} : a ∉ f.support → f.coeff a = 0 :=
begin
--  sorry,
--/-
  contrapose,
  push_neg,
  exact mem_support_iff_coeff_ne_zero.mpr,
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

@[simp] lemma reflect_zero {n : ℕ} : reflect n (0 : polynomial R) = 0 :=
begin
  refl,
end

@[simp] lemma reflect_add {f g : polynomial R} {n : ℕ} : reflect n (f+g) = reflect n f + reflect n g :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk, coeff_add],
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

@[simp] lemma reflect_monomial (N n : ℕ) : reflect N ((X : polynomial R) ^ n) = X ^ (rev_at N n) :=
begin
  rw [← one_mul (X^n), ← one_mul (X^(rev_at N n)), ← C_1, reflect_term],
end


@[simp] lemma reflect_term_small (N n : ℕ) {c : R} : n ≤ N → reflect N (C c * X ^ n) = C c * X ^ (N-n) :=
begin
  intro,
  rw ← rev_at_small a,
  exact reflect_term N n,
end

@[simp] lemma reflect_smul (N : ℕ) {r : R} : reflect N (C r * f) = C r * (reflect N f) :=
begin
  ext1,
  unfold reflect,
  simp only [coeff_mk, coeff_C_mul],
end

@[simp] lemma reflect_support_small_set (N : ℕ) {h : f.nat_degree ≤ N} : ↑(reflect N f).support = rev_at N '' ↑f.support :=
begin
  unfold reflect,
  rw set.coe_to_finset,
end

@[simp] lemma reflect_support_small (N : ℕ) {h : f.nat_degree ≤ N} : (reflect N f).support = (rev_at N '' ↑f.support).to_finset :=
rfl

lemma remove_leading_coefficient_zero : remove_leading_coefficient (0 : polynomial R) = 0 :=
rfl


lemma excongr {a b c : polynomial R} : b=c → a*b=a*c :=
begin
  exact congr_arg (λ {b : _}, a * b),
end

lemma pol_ind_card_degree_bound (N : ℕ) {P : ℕ → polynomial R → Prop}
 (Padd : ∀ f g : polynomial R , ∀ M : ℕ , f.nat_degree ≤ M → g.nat_degree ≤ M → P  M f → P M g → P M (f+g))
 (Pmon : ∀ r : R , ∀ n M : ℕ , n ≤ M → P M (C r * X^n)) :
 ∀ f : polynomial R , ∀ M : ℕ , f.support.card ≤ N.succ → f.nat_degree ≤ M → P M f :=
begin
    induction N with N hN,
    {
      intros f M hf hM,
      rw term_of_card_support_le_one (hf),
      apply Pmon (f.leading_coeff) f.nat_degree M hM,
    },
    { intros f M hf hM,
      rw sum_leading_term_remove f,
      apply Padd,
        apply le_trans _ hM,
        exact nat_degree_remove_leading_coefficient_le,

        apply le_trans _ hM,
        apply nat_degree_term_le,
        apply hN,

        by_cases f0 : f = 0,
        rw [f0, remove_leading_coefficient_zero, polynomial.support_zero, card_empty],
        exact zero_le _,

        rw ← support_remove_leading_coefficient_succ at hf,
        repeat {rw nat.succ_eq_add_one at hf},
        finish,

        intro,
        rw a at hf,
        simp at hf,
        finish,

        { apply le_trans _ hM,
          exact nat_degree_remove_leading_coefficient_le, },

        apply Pmon f.leading_coeff f.nat_degree M hM, },
end


lemma pol_ind_degree_bound {P : ℕ → polynomial R → Prop} {M : ℕ}
 {Padd : ∀ f g : polynomial R , ∀ N : ℕ , f.nat_degree ≤ N → g.nat_degree ≤ N → P N f → P N g → P N (f+g) }
 {Pmon : ∀ r : R , ∀ n N : ℕ , n ≤ N → P N (C r * X^n) } :
 f.nat_degree ≤ M → P M f :=
 begin
  intro,
  by_cases f0 : f = 0,
    { rw f0,
      convert Pmon 0 0 M (nat.zero_le _),
      rw [C_0, zero_mul], },
    { apply pol_ind_card_degree_bound f.support.card.pred Padd Pmon,
      rw [nat.succ_eq_add_one, nat.pred_eq_sub_one],
      rw nat.sub_add_cancel,
      apply xx,
      intro,
      apply f0,
      rw card_eq_zero at a_1,
      rwa ← zero_iff_empty,

      assumption, },
 end


lemma pol_ind_card (N : ℕ) {P : polynomial R → Prop}
 (Padd : ∀ f g : polynomial R , P f → P g → P (f+g))
 (Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)) :
 ∀ f : polynomial R , f.support.card = N.succ → P f :=
begin
  induction N with N hN,
    {
      intros f hf,
      rw term_of_card_support_le_one (le_of_eq hf),
      apply Pmon,
    },
    { intros f hf,
      rw sum_leading_term_remove f,
      apply Padd,
        apply hN,
        rw ← support_remove_leading_coefficient_succ at hf,
        finish,

        intro,
        rw a at hf,
        simp at hf,
        finish,

        apply Pmon, },
end




lemma pol_ind_1 {P : polynomial R → Prop}
 {Padd : ∀ f g : polynomial R , P f → P g → P (f+g) }
 {Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n) } :
 P f :=
begin
  by_cases f0 : f = 0,
    { rw f0,
      convert Pmon 0 0,
      rw [C_0, zero_mul], },
    { apply pol_ind_card f.support.card.pred Padd Pmon,
      rw [nat.succ_eq_add_one, nat.pred_eq_sub_one],
      rw nat.sub_add_cancel,
      apply xx,
      intro,
      apply f0,
      rw card_eq_zero at a,
      rwa ← zero_iff_empty, },
end


@[simp] lemma shift_rev_at (n : ℕ) {Ng a : ℕ} (h : a ≤ Ng) : rev_at (n + Ng) (shift_by n a) = rev_at Ng a :=
begin
  unfold shift_by,
  rw [rev_at_small h, rev_at_small];
  { omega, },
end


@[simp] lemma shift_rev_at_comp (n : ℕ) {Ng a : ℕ} (h : a ≤ Ng) : ((rev_at (n + Ng)) ∘ shift_by n) a = rev_at Ng a :=
begin
  exact shift_rev_at n h,
end



lemma reflect_mul_term_total_support (Ng n : ℕ) {s : finset ℕ} (hs : s.nonempty) : s.max' hs ≤ Ng → rev_at (n + Ng) '' (shift_by n '' ↑s) = rev_at Ng '' ↑s :=
begin
  intros Hs,
  repeat {rw ← coe_image},
  rw image_image,
  apply congr_arg,
  ext1,
  repeat {rw mem_image},
  split;
    { intro,
      rcases a_1 with ⟨ a , ha , rfl ⟩,
      use a,
      rw shift_rev_at_comp n (le_trans (le_max' _ _ ha) Hs),
      refine ⟨ ha , rfl ⟩, },
end





@[simp] lemma reflect_mul_term_total_zero_support (N n : ℕ) : f.nat_degree ≤ N → (reflect (n + N) (f*X^n)).support = (reflect N f).support :=
begin
  intro,
  by_cases f0 : f = 0,
    { rw [f0, zero_mul, reflect_zero, reflect_zero], },
    { rw defs_by_Johann f0 at a,
      unfold reflect,
      rw [set.to_finset_inj, mul_X_pow_support, set.coe_to_finset],
      exact @reflect_mul_term_total_support N n f.support (non_zero_iff.mpr f0) a, },
end


@[simp] lemma reflect_mul_term_total_support_plus (N n m : ℕ) {Hn : n ≤ m} {HN : f.nat_degree ≤ N} : (reflect (m + N) (f*X^n)).support = (reflect (m + N - n) f).support :=
begin
  rw le_iff_exists_add at Hn,
  cases Hn with c hc,
  rw [hc, add_assoc, reflect_mul_term_total_zero_support _ _ (le_add_left HN)],
  congr,
  rw [add_comm n, nat.add_sub_cancel],
end

def myProp (n : ℕ) : ℕ → polynomial R → Prop := λ N : ℕ , λ f : polynomial R , f.nat_degree ≤ N → (reflect (n + N) (f*X^n)) = (reflect N f)

lemma support_bound (N : ℕ) (h: f.nat_degree ≤ N) : f.support ⊆ range (N + 1) :=
begin
  intros a ha,
  rw [mem_range, nat.lt_succ_iff],
  apply le_trans _ h,
  apply le_nat_degree_of_mem_supp a ha,
end


lemma reflect_invol (N : ℕ) (f : polynomial R) : reflect N (reflect N f) = f :=
begin
  unfold reflect,
  simp only [coeff_mk, rev_at_invol, set.coe_to_finset],
  ext1,
  refl,
end


lemma reflect_mul_term_total (N n : ℕ) (f : polynomial R) {h : f.nat_degree ≤ N} : myProp n N f :=
--lemma reflect_mul_term_total (N n : ℕ) (f : polynomial R) : f.nat_degree ≤ N → (reflect (n + N) (f*X^n)) = (reflect N f) :=
begin
  apply (pol_ind_card_degree_bound N),

  unfold myProp,
  intros f g M Mf Mg Prf Prg dfg,
  rw [add_mul, reflect_add, reflect_add],
  simp only [*],

  unfold myProp,
  intros r n1 M Mn1 Mmon,
  rw [mul_assoc, ← pow_add],
  simp only [*, rev_at_small, reflect_monomial, reflect_smul],
  congr,
  rw rev_at_small,
  omega,
  rw add_comm,
  exact add_le_add_left Mn1 n,

  rw ← card_range N.succ,
  apply card_le_of_subset,
  exact support_bound N h,

  assumption,
end




def myPropExt (L n : ℕ) (hL : n ≤ L) : ℕ → polynomial R → Prop := λ N : ℕ , λ f : polynomial R , f.nat_degree ≤ N → (reflect (L + N) (f*X^n)) = (reflect (N+L-n) f)

lemma reflect_mul_term_total_ext (N L n : ℕ) (f : polynomial R) {hL : n ≤ L} {h : f.nat_degree ≤ N} : myPropExt L n hL N f :=
--lemma reflect_mul_term_total (N n : ℕ) (f : polynomial R) : f.nat_degree ≤ N → (reflect (n + N) (f*X^n)) = (reflect N f) :=
begin
  apply (pol_ind_card_degree_bound N),

  unfold myPropExt,
  intros f g M Mf Mg Prf Prg dfg,
  rw [add_mul, reflect_add, reflect_add],
  simp only [*],

  unfold myPropExt,
  intros r n1 M Mn1 Mmon,
  rw [mul_assoc, ← pow_add],
  simp only [*, rev_at_small, reflect_monomial, reflect_smul],
  repeat {apply congr_arg},
  repeat {rw rev_at_small},
  omega,
  omega,
  omega,

  rw ← card_range N.succ,
  apply card_le_of_subset,
  exact support_bound N h,

  assumption,
end



lemma pol_ind_Rhom_prod_on_card (cf cg : ℕ) (rp : ℕ → polynomial R → polynomial R)
 {rp_add  : ∀ f g : polynomial R , ∀ F : ℕ ,
  rp F (f+g) = rp F f + rp F g }
 {rp_smul : ∀ f : polynomial R , ∀ r : R , ∀ F : ℕ ,
  rp F ((C r)*f) = C r * rp F f }
 {rp_mon : ∀ n N : ℕ , n ≤ N →
  rp N (X^n) = X^(N-n) } :
 ∀ N O : ℕ , ∀ f g : polynomial R ,
 f.support.card ≤ cf.succ → g.support.card ≤ cg.succ → f.nat_degree ≤ N → g.nat_degree ≤ O →
 (rp (N + O) (f*g)) = (rp N f) * (rp O g) :=
begin
  have rp_zero : ∀ T : ℕ , rp T (0 : polynomial R) = 0,
    intro T,
    rw [← zero_mul (1 : polynomial R), ← C_0, rp_smul (1 : polynomial R) 0 T, C_0, zero_mul, zero_mul],
  induction cf with cf hcf,
    induction cg with cg hcg,
      intros N O f g Cf Cg Nf Og,
      rw [term_of_card_support_le_one Cf, term_of_card_support_le_one Cg],
      rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
      repeat {rw rp_smul},
      repeat {rw rp_mon},
      rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
      congr,
      omega,
      repeat {assumption,},
      rw add_comm,
      exact add_le_add Nf Og,

      intros N O f g Cf Cg Nf Og,

      by_cases g0 : g = 0,
        rw [g0, mul_zero, rp_zero, rp_zero, zero_add, mul_zero, zero_add],
        apply hcg N O f _ Cf _ Nf _,
      rw [sum_leading_term_remove g, mul_add, rp_add, rp_add, mul_add],

        exact (le_add_left card_support_term_le_one),
        exact (le_trans (nat_degree_term_le g.leading_coeff g.nat_degree) Og),

        rw hcg N O f (remove_leading_coefficient g) Cf _ Nf _,
        rw hcg N O f (_) Cf _ Nf _,

        exact (le_add_left card_support_term_le_one),
        exact (le_trans (nat_degree_term_le g.leading_coeff g.nat_degree) Og),

        rw ← nat.lt_succ_iff,
        apply gt_of_ge_of_gt Cg _,
        apply support_remove_leading_coefficient_lt,
        intro,
        apply rg0,
        rw [a, remove_leading_coefficient_zero],

        exact le_trans nat_degree_remove_leading_coefficient_le Og,


        --induction step
        intros N O f g Cf Cg Nf Og,

        by_cases f0 : f=0,
          rw [f0, zero_mul, rp_zero, rp_zero, zero_mul],

        rw [sum_leading_term_remove f, add_mul, rp_add, rp_add, add_mul],

        rw hcf N O (remove_leading_coefficient f) (g) _ Cg _ Og,
        rw hcf N O (_) (g) _ Cg _ Og,

        exact (le_add_left card_support_term_le_one),
        exact (le_trans (nat_degree_term_le f.leading_coeff f.nat_degree) Nf),

        { rw ← nat.lt_succ_iff,
          apply gt_of_ge_of_gt Cf _,
          apply support_remove_leading_coefficient_lt f0, },

        exact le_trans nat_degree_remove_leading_coefficient_le Nf,
end

/-
-- in questa versione, ci sono tutte le ipotesi, ma non quella che i monomi vanno in monomi.  questo crea problemi con permutare l'ordine dei coefficienti direttori
lemma pol_ind_Rhom_prod_on_card (cf cg : ℕ) (rp : ℕ → polynomial R → polynomial R)
 {rp_add  : ∀ f g : polynomial R , ∀ F : ℕ , f.nat_degree ≤ F → g.nat_degree ≤ F → rp F (f+g) = rp F f + rp F g }
 {rp_smul : ∀ f : polynomial R , ∀ r : R , ∀ F : ℕ , f.nat_degree ≤ F →
  rp F ((C r)*f) = C r * rp F f }
 {rp_mon : ∀ m n M N : ℕ , m ≤ M → n ≤ N →
  rp (M+N) (X^(m+n)) = rp M (X^m) * rp N (X^n) } :
 ∀ N O : ℕ , ∀ f g : polynomial R ,
 f.support.card ≤ cf.succ → g.support.card ≤ cg.succ → f.nat_degree ≤ N → g.nat_degree ≤ O →
 (rp (N + O) (f*g)) = (rp N f) * (rp O g) :=
begin
  induction cf with cf hcf,
    induction cg with cg hcg,
      intros N O f g Cf Cg Nf Og,
      rw [term_of_card_support_le_one Cf, term_of_card_support_le_one Cg],
      rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
      repeat {rw rp_smul},
      repeat {rw rp_mon},


  sorry,
end
-/






def myPropProd (L M l m : ℕ) (hL : l ≤ L) (hM : m ≤ M)
 : ℕ → ℕ → polynomial R → polynomial R → Prop := λ N O : ℕ , λ f g : polynomial R ,
 f.nat_degree ≤ N → g.nat_degree ≤ O →
 (reflect (N + O) (f*g)) = (reflect N f) * (reflect O g)



/-
@[simp] lemma reflect_mul_term {N n : ℕ} {H : f.nat_degree ≤ N } : reflect (N+n) (f * X ^ n) = reflect N f :=
begin

  apply reflect_mul_term_total_ext (N+n) 0 n f,--cerca di trasformarlo!
end
-/

--def myProp (n : ℕ) : ℕ → polynomial R → Prop := λ N : ℕ , λ f : polynomial R , f.nat_degree ≤ N → (reflect (n + N) (f*X^n)) = (reflect N f)

def myPropReflect (g : polynomial R) (N : ℕ) (Ng : g.nat_degree ≤ N) :
 ℕ → polynomial R → Prop :=
 λ M : ℕ , λ f : polynomial R , f.nat_degree ≤ M → (reflect (M + N) (f*g)) = (reflect M f) * (reflect N g)


lemma reflect_reflect (f g : polynomial R) (M N : ℕ) (Nf : f.nat_degree ≤ M) (Ng : g.nat_degree ≤ N) : myPropReflect g N Ng M f :=
--lemma reflect_reflect (f g : polynomial R) (M N : ℕ) {hf : f.nat_degree ≤ M} {hg : g.nat_degree ≤ N} : reflect (M+N) (f*g) = reflect M f * reflect N g :=
begin
  apply pol_ind_card_degree_bound M,

  unfold myPropReflect,
  intros f g_1 M Mf Mg1 fmul g1add Nfg1,

  rw [reflect_add, add_mul, add_mul, reflect_add],
  simp only [*],

  unfold myPropReflect,
  intros r n M Mn Mmon,
  rw [mul_assoc, X_pow_mul, ← mul_assoc],
  simp only [*, rev_at_small, reflect_monomial, reflect_smul],
  rw reflect_mul_term_total_ext,
  simp only [reflect_smul],
  rw mul_assoc,
  apply congr_arg,
  rw X_pow_mul,
--  rw ← reflect_invol (N+M-n) (reflect (N+M-n) g),
--  rw reflect_mul_term_total (N+M) 0 (reflect N g * X ^ (M - n)),
--  rw ← reflect_invol (N+M-n) (reflect N g * X ^ (M - n)),
--  rw ← reflect_mul_term_total (N+M-n) (N) (reflect N g * X ^ (M - n)),

  rw ← reflect_mul_term_total N (M-n) g,

--  rw ← add_zero (M - n + N),
  rw reflect_mul_term_total N-n (M-n) g,

  rw [← zero_add (N + M - n), ← mul_one g, ← pow_zero X],
  rw reflect_mul_term_total (N+M-n) 0 g,
  rw [← zero_add (N)],
  rw reflect_mul_term_total (N) 0 g,
  simp *,


  rw ← reflect_mul_term_total N (M-n) g,

    sorry,
end

#exit
lemma reflect_mul_term_total (c : ℕ) (N n : ℕ) (f : polynomial R) : f.support.card ≤ c.succ → f.nat_degree ≤ N → (reflect (n + N) (f*X^n)) = (reflect N f) :=
begin
  revert f,
  induction c with c hc,
    { intros f fc fd,
      rw term_of_card_support_le_one fc,
      rw [mul_assoc, ← pow_add X],
      repeat {rw reflect_term, rw rev_at_small},
        { repeat {apply congr_arg},
          omega, },
        { exact fd, },
        { rw add_comm,
          exact add_le_add_left fd n, }, },
    {
      intros f fc fd,
      rw [sum_leading_term_remove f, add_mul, mul_assoc, ← pow_add],
      simp only [*, rev_at_small, reflect_monomial, reflect_smul, reflect_add],
      have : (remove_leading_coefficient f).support.card ≤ c.succ,
        apply nat.le_of_lt_succ,
        apply gt_of_ge_of_gt fc _,
      apply hc (remove_leading_coefficient f),
      sorry,
    },

  intro,
  by_cases f0 : f = 0,
    { rw [f0, zero_mul, reflect_zero, reflect_zero], },
    { rw defs_by_Johann f0 at a,
      unfold reflect,
      rw [set.to_finset_inj, mul_X_pow_support, set.coe_to_finset],
      exact @reflect_mul_term_total_support N n f.support (non_zero_iff.mpr f0) a, },
end







#exit

lemma reflect_mul (M N : ℕ) : ∀ (Nf Ng : ℕ) (f g : polynomial R) , g.support.card ≤ M.succ → f.support.card ≤ N.succ → f.nat_degree ≤ Nf → g.nat_degree ≤ Ng → reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  induction N with N hN,
    { intros Nf Ng f g hgc hfc hf hg,
      rw term_of_card_support_le_one hfc,
      rw [reflect_term, rev_at_small hf, mul_assoc],
      rw reflect_smul,
      rw mul_assoc,
      apply congr_arg (λ {b : polynomial R}, (C f.leading_coeff) * b),
      rw X_pow_mul,

      revert g,
      induction M,
        { intros g hgc hg,
          rw term_of_card_support_le_one hgc,
          rw [reflect_smul, reflect_monomial, X_pow_mul, mul_assoc, ← pow_add X],
          rw [reflect_smul, reflect_monomial, mul_assoc, X_pow_mul, ← pow_add X],
          congr,
          rw [rev_at_small hg, rev_at_small _],
            { omega, },
            { rw add_comm Nf Ng,
              exact add_le_add hg hf, }, },
        {
          intros g hgc hg,
          rw sum_leading_term_remove g,
          rw [reflect_add, reflect_smul, add_mul, mul_add, reflect_add, reflect_monomial],
          rw rev_at_small hg,
          rw M_ih (remove_leading_coefficient g) _ _,
          congr,
          rw [mul_assoc, ← pow_add X],
          rw  reflect_mul_term_total Ng (g.nat_degree+f.nat_degree) Nf,
          sorry,
        }, },

    {
      intros Nf Ng f g fs fd gd,
      by_cases f0 : f = 0,
        { rw [f0, zero_mul, reflect_zero, reflect_zero, zero_mul], },

        { rw sum_leading_term_remove f,
          rw [reflect_add, reflect_smul, add_mul, reflect_add, add_mul, reflect_monomial],
          have : (remove_leading_coefficient f).support.card ≤ N.succ,
            rw ← nat.lt_succ_iff,
            apply gt_of_ge_of_gt fs,
            exact support_remove_leading_coefficient_lt f0,
          rw hN Nf Ng (remove_leading_coefficient f) g this (le_trans nat_degree_remove_leading_coefficient_le fd) gd,
          apply congr_arg (λ b : polynomial R , reflect Nf (remove_leading_coefficient f) * reflect Ng g + b),
          sorry, --lemma un po' più forte
 }, },
end



#exit


lemma reflect_mul (N : ℕ) : ∀ (Nf Ng : ℕ) (f g : polynomial R) , f.support.card ≤ N.succ → f.nat_degree ≤ Nf → g.nat_degree ≤ Ng → reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  induction N with N hN,
    { intros Nf Ng f g hfc hf hg,
      rw term_of_card_support_le_one hfc,
      rw [reflect_term, rev_at_small hf, mul_assoc],
      rw reflect_smul,
      rw mul_assoc,
      apply congr_arg (λ {b : polynomial R}, (C f.leading_coeff) * b),
      rw X_pow_mul,

      ext,
      unfold reflect,
      simp * at *,
      rw reflect_mul_term_total Ng f.nat_degree Nf,
      sorry, --requires a lemma
    },
    {
      intros Nf Ng f g fs fd gd,
      by_cases f0 : f = 0,
        { rw [f0, zero_mul, reflect_zero, reflect_zero, zero_mul], },

        { rw sum_leading_term_remove f,
          rw [reflect_add, reflect_smul, add_mul, reflect_add, add_mul, reflect_monomial],
          have : (remove_leading_coefficient f).support.card ≤ N.succ,
            rw ← nat.lt_succ_iff,
            apply gt_of_ge_of_gt fs,
            exact support_remove_leading_coefficient_lt f0,
          rw hN Nf Ng (remove_leading_coefficient f) g this (le_trans nat_degree_remove_leading_coefficient_le fd) gd,
          apply congr_arg (λ b : polynomial R , reflect Nf (remove_leading_coefficient f) * reflect Ng g + b),
          sorry, --lemma un po' più forte
 }, },
end



#exit


lemma reflect_mul_term_total (Ng n : ℕ) (g : polynomial R) : g.nat_degree ≤ Ng → reflect (n + Ng) (g * X ^ n) = reflect Ng g :=
begin
  intros Hg,
  induction n with n hn,
    { simp only [mul_one, zero_add, pow_zero], },
    { --rw ← hn,
      --simp only [*],
      ext,
      rw [nat.succ_eq_add_one, pow_add, pow_one],
      simp * at *,
      unfold reflect,
--      unfold reflect at hn,
      simp * at *,
      sorry,
    },
end

#exit

lemma reflect_mul_term (Nf Ng n : ℕ) (g : polynomial R) : n ≤ Nf → g.nat_degree ≤ Ng → reflect (Nf + Ng) (X ^ n * g) = X ^ (Nf - n) * reflect Ng g :=
begin
  intros Hn Hg,
  ext1,
  by_cases ns : n_1 ≤

  unfold reflect,


  simp *,
  sorry,
end

#exit

lemma reflect_mul (N : ℕ) : ∀ (Nf Ng : ℕ) (f g : polynomial R) , f.support.card ≤ N.succ → f.nat_degree ≤ Nf → g.nat_degree ≤ Ng → reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  induction N with N hN,
    { intros Nf Ng f g hfc hf hg,
      rw term_of_card_support_le_one hfc,
      rw [reflect_term, rev_at_small hf, mul_assoc],
      rw reflect_smul,
      rw mul_assoc,
      apply congr_arg (λ {b : polynomial R}, (C f.leading_coeff) * b),
      sorry, --requires a lemma
    },
    {
      intros Nf Ng f g fs fd gd,
      by_cases f0 : f = 0,
        { rw [f0, zero_mul, reflect_zero, reflect_zero, zero_mul], },

        { rw sum_leading_term_remove f,
          rw [reflect_add, reflect_smul, add_mul, reflect_add, add_mul, reflect_monomial],
          have : (remove_leading_coefficient f).support.card ≤ N.succ,
            rw ← nat.lt_succ_iff,
            apply gt_of_ge_of_gt fs,
            exact support_remove_leading_coefficient_lt f0,
          rw hN Nf Ng (remove_leading_coefficient f) g this (le_trans nat_degree_remove_leading_coefficient_le fd) gd,
          apply congr_arg (λ b : polynomial R , reflect Nf (remove_leading_coefficient f) * reflect Ng g + b),
          sorry, --lemma un po' più forte
 }, },
end

lemma reflect_mul (N Nf Ng : ℕ) (f g : polynomial R) : f.support.card ≤ N.succ → f.nat_degree ≤ Nf → g.nat_degree ≤ Ng → reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  induction N,
    { intros hfc hf hg,
      rw term_of_card_support_le_one hfc,
      rw [reflect_term, rev_at_small hf, mul_assoc],
      rw reflect_smul,
      rw mul_assoc,
      apply congr_arg (λ {b : polynomial R}, (C f.leading_coeff) * b),
      sorry, --requires a lemma
    },
    {
      intros fcar fdeg gdeg,
      by_cases f0 : f = 0,
        { rw [f0, zero_mul, reflect_zero, reflect_zero, zero_mul], },

        { rw sum_leading_term_remove f,
          rw [reflect_add, reflect_smul, add_mul, reflect_add, add_mul, reflect_monomial],
          have : (remove_leading_coefficient f).support.card ≤ N_n.succ,
            rw ← nat.lt_succ_iff,
            apply gt_of_ge_of_gt fcar,
            exact support_remove_leading_coefficient_lt f0,
          --rw N_ih,
          sorry, }, },
end
#exit
--      simp only [nat.nat_zero_eq_zero, reflect_smul, zero_add],

      rw eq_C_of_nat_degree_le_zero hf,
      congr,
      unfold reflect,
      have : rev_at 0 = id,
        ext,
        by_cases x0 : x = 0,
          rw x0,
          refl,
          apply rev_at_large (nat.pos_of_ne_zero x0),
      simp_rw this,
      ext1,
      refl, },
    {
      intros a a_1,


      induction Ng,

      ext1,
      sorry,
    },
end


#exit

lemma reflect_mul (Nf Ng : ℕ) (f g : polynomial R) : f.nat_degree ≤ Nf → g.nat_degree ≤ Ng → reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  induction Nf,
    { intros hf hg,
      rw eq_C_of_nat_degree_le_zero hf,
      simp only [nat.nat_zero_eq_zero, reflect_smul, zero_add],
      congr,
      unfold reflect,
      have : rev_at 0 = id,
        ext,
        by_cases x0 : x = 0,
          rw x0,
          refl,
          apply rev_at_large (nat.pos_of_ne_zero x0),
      simp_rw this,
      ext1,
      refl, },
    {
      intros a a_1,


      induction Ng,

      ext1,
      sorry,
    },
end


#exit
lemma reflect_mul {Nf Ng : ℕ} {Hf : f.nat_degree ≤ Nf} : ∀ g : polynomial R, ∀ Ng : ℕ, g.nat_degree ≤ Ng → reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  apply pol_ind_with_N_bound,
    { intros p q Np Nq Npq hp hq,
      rw [mul_add, reflect_add, reflect_add, mul_add],
      revert Np Nq Npq,
      sorry, },
    {
      sorry,
    },
end


#exit



lemma reflect_mul {Nf Ng : ℕ} {Hf : f.nat_degree ≤ Nf} : ∀ g : polynomial R, ∀ Ng : ℕ , g.nat_degree ≤ Ng → reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  intro g,
  apply pol_ind g,
  {
    intros p q hp hq Ng Hg,
    simp [mul_add],
    rw hq Ng,
    rw hp Ng,
  },
  {
    intros r n g Ng Hg,
    rw mul_assoc,
    simp [X_pow_mul],
    rw ← mul_assoc,
    simp,
    sorry,
  },
end

#exit
lemma reflect_mul {f g : polynomial R} {Nf Ng : ℕ} {Hf : (f).nat_degree ≤ Nf} {Hg : (g).nat_degree ≤ Ng} : reflect (Nf+Ng) (f*g) = reflect Nf (f) * reflect Ng (g) :=
begin
  revert Nf f,
--  revert f,
  apply pol_ind g,
    { intros p q hp hq Nf f Hf,
      rwa [mul_add, reflect_add, reflect_add, mul_add, @hp _ _ Hf, @hq _ _ _], },
    {
      intros r n Nf f Hf,
      apply pol_ind f,
        {
          intros p q hp hq Hf_1,
          rw [reflect_add, add_mul, add_mul, reflect_add],
          rw reflect_term_small Ng n,
          --, reflect_term_small, hp, hq, reflect_term],
        },
        {
          intros r m,
          rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add, ← mul_assoc, ← C_mul],

          rw reflect_term_small Hf,
--          repeat {rw reflect_term_small _},
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
