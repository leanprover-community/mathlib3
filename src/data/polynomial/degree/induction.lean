import tactic
import data.polynomial.degree.basic
import logic.function.basic
import algebra.big_operators.basic


open_locale big_operators
open_locale classical

open function polynomial finsupp finset

namespace reverse

variables {R : Type*} [semiring R] {f : polynomial R}

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


lemma le_ind {P : polynomial R → Prop} {f g : polynomial R}
 {Psum : (P f) → (P g) → (P (f+g))} {Pmon : ∀ r : R , ∀ n : ℕ , P (C r * X^n)} :
 ∀ p : polynomial R, P p :=
 begin
   tidy,
 end


