/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import data.polynomial.monic
import data.polynomial.ring_division
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
open multiset

open_locale big_operators

universes u w

variables {R : Type u} {ι : Type w}

namespace polynomial

variables (s : finset ι) (t : multiset ι)

section comm_semiring
variables [comm_semiring R] (f : ι → polynomial R)

lemma nat_degree_multiset_prod_le :
  (t.map f).prod.nat_degree ≤ (t.map (λ i, (f i).nat_degree)).sum :=
begin
  refine multiset.induction_on t _ (λ a t ih, _), { simp },
  rw [map_cons, prod_cons, map_cons, sum_cons],
  transitivity (f a).nat_degree + (t.map f).prod.nat_degree,
  { apply polynomial.nat_degree_mul_le },
  { exact add_le_add (le_refl _) ih }
end

lemma nat_degree_prod_le : (∏ i in s, f i).nat_degree ≤ ∑ i in s, (f i).nat_degree :=
nat_degree_multiset_prod_le s.1 f

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma leading_coeff_multiset_prod' (h : (t.map (λ i, (f i).leading_coeff)).prod ≠ 0) :
  (t.map f).prod.leading_coeff = (t.map (λ i, (f i).leading_coeff)).prod :=
begin
  revert h,
  refine multiset.induction_on t _ (λ a t ih ht, _), { simp },
  rw [map_cons, prod_cons] at ht,
  simp only [map_cons, prod_cons],
  rw polynomial.leading_coeff_mul'; { rwa ih, apply right_ne_zero_of_mul ht }
end

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `polynomial.leading_coeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma leading_coeff_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
leading_coeff_multiset_prod' s.1 f h

/--
The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `polynomial.nat_degree_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma nat_degree_multiset_prod' (h : (t.map (λ i, (f i).leading_coeff)).prod ≠ 0) :
  (t.map f).prod.nat_degree = (t.map (λ i, (f i).nat_degree)).sum :=
begin
  revert h,
  refine multiset.induction_on t _ (λ a t ih ht, _), { simp },
  rw [map_cons, prod_cons] at ht ⊢,
  rw [map_cons, sum_cons, polynomial.nat_degree_mul', ih],
  { apply right_ne_zero_of_mul ht },
  { rwa polynomial.leading_coeff_multiset_prod', apply right_ne_zero_of_mul ht },
end

/--
The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `polynomial.nat_degree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
lemma nat_degree_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
nat_degree_multiset_prod' s.1 f h

lemma nat_degree_multiset_prod_of_monic [nontrivial R] (h : ∀ i ∈ t, (f i).monic) :
  (t.map f).prod.nat_degree = (t.map (λ i, (f i).nat_degree)).sum :=
begin
  apply nat_degree_multiset_prod',
  suffices : (t.map (λ i, (f i).leading_coeff)).prod = 1, { rw this, simp },
  convert prod_repeat (1 : R) t.card,
  { simp only [eq_repeat, multiset.card_map, eq_self_iff_true, true_and],
    rintros i hi,
    obtain ⟨i, hi, rfl⟩ := multiset.mem_map.mp hi,
    apply h, assumption },
  { simp }
end

lemma nat_degree_prod_of_monic [nontrivial R] (h : ∀ i ∈ s, (f i).monic) :
  (∏ i in s, f i).nat_degree = ∑ i in s, (f i).nat_degree :=
nat_degree_multiset_prod_of_monic s.1 f h

lemma coeff_zero_multiset_prod :
  (t.map f).prod.coeff 0 = (t.map (λ i, (f i).coeff 0)).prod :=
begin
  refine multiset.induction_on t _ (λ a t ht, _), { simp },
  rw [map_cons, prod_cons, map_cons, prod_cons,
      polynomial.mul_coeff_zero, ht],
end

lemma coeff_zero_prod :
  (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0 :=
coeff_zero_multiset_prod s.1 f

end comm_semiring

section comm_ring
variables [comm_ring R]

open monic
-- Eventually this can be generalized with Vieta's formulas
-- plus the connection between roots and factorization.
lemma multiset_prod_X_sub_C_next_coeff [nontrivial R] {t : multiset ι} (f : ι → R) :
  next_coeff (t.map (λ i, X - C (f i))).prod = -(t.map f).sum :=
begin
  rw next_coeff_multiset_prod,
  { simp only [next_coeff_X_sub_C],
    rw ← multiset.map_map,
    refine (t.map _).sum_hom ⟨has_neg.neg, _, _⟩; simp [add_comm] },
  { intros, apply monic_X_sub_C }
end

lemma prod_X_sub_C_next_coeff [nontrivial R] {s : finset ι} (f : ι → R) :
  next_coeff ∏ i in s, (X - C (f i)) = -∑ i in s, f i :=
multiset_prod_X_sub_C_next_coeff f

lemma multiset_prod_X_sub_C_coeff_card_pred [nontrivial R] (t : multiset ι)
  (f : ι → R) (hs : 0 < t.card) :
  (t.map (λ i, (X - C (f i)))).prod.coeff (t.card - 1) = -(t.map f).sum :=
begin
  convert multiset_prod_X_sub_C_next_coeff (by assumption),
  rw next_coeff, split_ifs,
  { rw nat_degree_multiset_prod_of_monic at h,
    swap, { intros, apply monic_X_sub_C },
    simp_rw [multiset.sum_eq_zero_iff, multiset.mem_map, nat_degree_X_sub_C] at h,
    contrapose! h,
    obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp hs,
    exact ⟨_, ⟨x, hx, rfl⟩, one_ne_zero⟩ },
  congr, rw nat_degree_multiset_prod_of_monic; { simp [nat_degree_X_sub_C, monic_X_sub_C] },
end

lemma prod_X_sub_C_coeff_card_pred [nontrivial R] (s : finset ι) (f : ι → R) (hs : 0 < s.card) :
  (∏ i in s, (X - C (f i))).coeff (s.card - 1) = - ∑ i in s, f i :=
multiset_prod_X_sub_C_coeff_card_pred s.1 f hs

end comm_ring

section no_zero_divisors
variables [comm_ring R] [no_zero_divisors R] (f : ι → polynomial R)

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
  intros x hx, simp [h x hx]
end

lemma nat_degree_multiset_prod [nontrivial R] (s : multiset (polynomial R))
  (h : (0 : polynomial R) ∉ s) :
  nat_degree s.prod = (s.map nat_degree).sum :=
begin
  rw [← s.map_id, nat_degree_multiset_prod'], simp,
  simp_rw [ne.def, multiset.prod_eq_zero_iff, multiset.mem_map, leading_coeff_eq_zero, id],
  rintro ⟨_, h, rfl⟩,
  contradiction
end

/--
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
lemma degree_multiset_prod [nontrivial R] :
  (t.map f).prod.degree = (t.map (λ i, (f i).degree)).sum :=
begin
  refine multiset.induction_on t _ (λ a t ht, _), { simp },
  { rw [map_cons, prod_cons, degree_mul, ht, map_cons, sum_cons] }
end

/--
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
lemma degree_prod [nontrivial R] : (∏ i in s, f i).degree = ∑ i in s, (f i).degree :=
degree_multiset_prod s.1 f

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `polynomial.leading_coeff_multiset_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
lemma leading_coeff_multiset_prod :
  (t.map f).prod.leading_coeff = (t.map (λ i, (f i).leading_coeff)).prod :=
by { rw [← leading_coeff_hom_apply, monoid_hom.map_multiset_prod, multiset.map_map], refl }

/--
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `polynomial.leading_coeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
lemma leading_coeff_prod :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
leading_coeff_multiset_prod s.1 f

end no_zero_divisors
end polynomial
