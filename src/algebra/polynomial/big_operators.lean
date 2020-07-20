/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial.monic
import tactic.linarith

open polynomial finset

/-!
# Polynomials

Lemmas for the interaction between polynomials and ∑ and ∏.

## Main results

- `nat_degree_prod_of_monic` : the degree of a product of monic polynomials is the product of
    degrees. We prove this only for [comm_semiring R],
    but it ought to be true for [semiring R] and list.prod.
- `nat_degree_prod` : for polynomials over an integral domain,
    the degree of the product is the sum of degrees
- `leading_coeff_prod` : for polynomials over an integral domain,
    the leading coefficient is the product of leading coefficients
- `prod_X_sub_C_coeff_card_pred` carries most of the content for computing
    the second coefficient of the characteristic polynomial.
-/

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

/-- The leading coefficient of a product of polynomials is equal to the product of the leading coefficients, provided that this product is nonzero.
See `leading_coeff_prod` (without the `'`) for a version for integral domains, where this condition is automatically satisfied. -/
lemma leading_coeff_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
begin
  classical,
  revert h, induction s using finset.induction with a s ha hs, { simp },
  repeat { rw prod_insert ha },
  intro h, rw polynomial.leading_coeff_mul'; { rwa hs, apply right_ne_zero_of_mul h },
end

/-- The degree of a product of polynomials is equal to the product of the degrees, provided that the product of leading coefficients is nonzero.
See `nat_degree_prod` (without the `'`) for a version for integral domains, where this condition is automatically satisfied. -/
lemma nat_degree_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  classical,
  revert h, induction s using finset.induction with a s ha hs, { simp },
  rw [prod_insert ha, prod_insert ha, sum_insert ha],
  intro h, rw polynomial.nat_degree_mul', rw hs,
  apply right_ne_zero_of_mul h,
  rwa polynomial.leading_coeff_prod', apply right_ne_zero_of_mul h,
end

lemma nat_degree_prod_of_monic [nontrivial R] (h : ∀ i ∈ s, (f i).monic) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  apply nat_degree_prod',
  suffices : ∏ i in s, (f i).leading_coeff = 1, { rw this, simp },
  rw prod_eq_one, intros, apply h, assumption,
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

section integral_domain
variables [integral_domain R] (f : ι → polynomial R)

lemma nat_degree_prod (h : ∀ i ∈ s, f i ≠ 0) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  apply nat_degree_prod', rw prod_ne_zero_iff,
  intros x hx, simp [h x hx],
end

lemma leading_coeff_prod :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
by { rw ← leading_coeff_hom_apply, apply monoid_hom.map_prod }

end integral_domain
end polynomial
