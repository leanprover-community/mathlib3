/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial.monic
import tactic.linarith
/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `finset.sum` and `finset.prod` respectively.

## Main results

- `polynomial.nat_degree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[comm_semiring R]`,
  but it ought to be true for `[semiring R]` and `list.prod`.
- `polynomial.nat_degree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `polynomial.leading_coeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
  the second coefficient of the characteristic polynomial.
-/

open finset

open_locale big_operators

universes u w

variables {R : Type u} {ι : Type w}

namespace polynomial

variable (s : finset ι)

section comm_semiring
variables [comm_semiring R] (f : ι → polynomial R)

lemma nat_degree_prod_le : (∏ i in s, f i).nat_degree ≤ ∑ i in s, (f i).nat_degree :=
begin
  classical,
  induction s using finset.induction with a s ha hs, { simp },
  rw [prod_insert ha, sum_insert ha],
  transitivity (f a).nat_degree + (∏ x in s, f x).nat_degree,
  apply polynomial.nat_degree_mul_le, linarith,
end

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma leading_coeff_multiset_prod' (m : multiset (polynomial R))
  (h : (m.map leading_coeff).prod ≠ 0) :
  m.prod.leading_coeff = (m.map leading_coeff).prod :=
begin
  revert h, refine multiset.induction _ _ m,
  { intro h, exact leading_coeff_one },
  intros a s hm h,
  simp only [multiset.map_cons, multiset.prod_cons] at ⊢ h,
  rw polynomial.leading_coeff_mul'; { rwa hm, apply right_ne_zero_of_mul h },
end

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma leading_coeff_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
begin
  refine trans (leading_coeff_multiset_prod' (multiset.map f s.1) _) _,
  { convert h, apply multiset.map_map },
  { rw multiset.map_map, refl }
end

/--
The degree of a product of polynomials is equal to
the product of the degrees, provided that the product of leading coefficients is nonzero.

See `nat_degree_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma nat_degree_multiset_prod' (m : multiset (polynomial R))
  (h : (m.map leading_coeff).prod ≠ 0) :
  m.prod.nat_degree = (m.map nat_degree).sum :=
begin
  revert h, refine multiset.induction _ _ m,
  { intro h, exact nat_degree_one },
  intros a s hm h,
  simp only [multiset.map_cons, multiset.prod_cons, multiset.sum_cons] at ⊢ h,
  rw polynomial.nat_degree_mul', rw hm,
  apply right_ne_zero_of_mul h,
  rwa polynomial.leading_coeff_multiset_prod', apply right_ne_zero_of_mul h,
end

lemma nat_degree_multiset_prod_of_monic [nontrivial R] (m : multiset (polynomial R))
  (h : ∀ f ∈ m, monic f) :
  m.prod.nat_degree = (m.map nat_degree).sum :=
begin
  apply nat_degree_multiset_prod',
  suffices : (m.map leading_coeff).prod = 1, { rw this, simp },
  exact (congr_arg _ (multiset.map_congr h)).trans multiset.prod_map_one
end

/--
The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `polynomial.nat_degree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma nat_degree_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  refine trans (nat_degree_multiset_prod' _ _) _,
  { convert h, apply multiset.map_map },
  { rw multiset.map_map, refl }
end

lemma nat_degree_prod_of_monic [nontrivial R] (h : ∀ i ∈ s, (f i).monic) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  refine trans (nat_degree_multiset_prod_of_monic _ _) _,
  { intro _, rw multiset.mem_map, rintros ⟨i, hi, rfl⟩, exact h i hi },
  { rw multiset.map_map, refl }
end

lemma coeff_zero_prod :
  (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0 :=
begin
  classical,
  induction s using finset.induction with a s ha hs,
  { simp only [coeff_one_zero, prod_empty] },
  { simp only [ha, hs, mul_coeff_zero, not_false_iff, prod_insert] }
end

end comm_semiring

section comm_ring
variables [comm_ring R]

open monic
-- Eventually this can be generalized with Vieta's formulas
-- plus the connection between roots and factorization.
lemma prod_X_sub_C_next_coeff [nontrivial R] {s : finset ι} (f : ι → R) :
  next_coeff ∏ i in s, (X - C (f i)) = -∑ i in s, f i :=
by { rw next_coeff_prod; { simp [monic_X_sub_C] } }

lemma prod_X_sub_C_coeff_card_pred [nontrivial R] (s : finset ι) (f : ι → R) (hs : 0 < s.card) :
  (∏ i in s, (X - C (f i))).coeff (s.card - 1) = - ∑ i in s, f i :=
begin
  convert prod_X_sub_C_next_coeff (by assumption),
  rw next_coeff, split_ifs,
  { rw nat_degree_prod_of_monic at h,
    swap, { intros, apply monic_X_sub_C },
    rw sum_eq_zero_iff at h,
    simp_rw nat_degree_X_sub_C at h, contrapose! h, norm_num,
    exact multiset.card_pos_iff_exists_mem.mp hs },
  congr, rw nat_degree_prod_of_monic; { simp [nat_degree_X_sub_C, monic_X_sub_C] },
end

end comm_ring

section no_zero_divisors
variables [comm_ring R] [no_zero_divisors R] (f : ι → polynomial R)

lemma nat_degree_multiset_prod (m : multiset (polynomial R)) (h : ∀ f ∈ m, f ≠ (0 : polynomial R)) :
  m.prod.nat_degree = (m.map nat_degree).sum :=
begin
  apply nat_degree_multiset_prod',
  rw [ne.def, multiset.prod_eq_zero_iff, multiset.mem_map],
  rintros ⟨x, hx, fx_eq⟩,
  exact h x hx (leading_coeff_eq_zero.mp fx_eq)
end

lemma nat_degree_prod (h : ∀ i ∈ s, f i ≠ 0) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  refine trans (nat_degree_multiset_prod _ _) _,
  { simp only [multiset.mem_map], rintros _ ⟨i, hi, rfl⟩, exact h i hi },
  { rw multiset.map_map, refl }
end

lemma leading_coeff_multiset_prod (m : multiset (polynomial R)) :
  m.prod.leading_coeff = (m.map leading_coeff).prod :=
by { rw [← leading_coeff_hom_apply, monoid_hom.map_multiset_prod], refl }

/--
The degree of a product of polynomials is equal to
the sum of the degrees.

See `polynomial.nat_degree_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
lemma nat_degree_prod [nontrivial R] (h : ∀ i ∈ s, f i ≠ 0) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  apply nat_degree_prod',
  rw prod_ne_zero_iff,
  intros x hx, simp [h x hx],
end

/--
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
lemma degree_prod [nontrivial R] : (∏ i in s, f i).degree = ∑ i in s, (f i).degree :=
begin
  classical,
  induction s using finset.induction with a s ha hs,
  { simp },
  { rw [prod_insert ha, sum_insert ha, degree_mul, hs] },
end

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `polynomial.leading_coeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
>>>>>>> mathlib/master
lemma leading_coeff_prod :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
begin
  refine trans (leading_coeff_multiset_prod _) _,
  rw multiset.map_map, refl
end

end no_zero_divisors
end polynomial
