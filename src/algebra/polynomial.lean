/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
open polynomial finset

/-
# Polynomials

Here we have utility lemmas for polynomials.
For results that are useful for programming, see data/polynomial.lean

## Main results

- `nat_degree_prod_eq_of_monic`: needed for reasoning about the characteristic polynomial
-/

noncomputable theory
open_locale big_operators

universes u w

variables {R : Type u} {α : Type w} [decidable_eq α]
variables (s : finset α)

namespace polynomial

section poly_big_ops

section comm_semiring
variables [comm_semiring R] (f : α → polynomial R)

lemma nat_degree_prod_le : (s.prod f).nat_degree ≤ ∑ i in s, (f i).nat_degree :=
begin
  apply s.induction_on, simp,intros a s anins ih,
  rw [prod_insert anins, sum_insert anins],
  transitivity (f a).nat_degree + (∏ (x : α) in s, (f x)).nat_degree,
  apply polynomial.nat_degree_mul_le, apply add_le_add_left ih,
end

lemma leading_coeff_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
begin
  revert h, apply s.induction_on, simp, intros a s anins ih,
  repeat {rw prod_insert anins},
  intro nz, rw polynomial.leading_coeff_mul'; rwa ih, repeat {apply right_ne_zero_of_mul nz},
end

lemma nat_degree_prod_eq' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (s.prod f).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  revert h, apply s.induction_on, simp, intros a s anins ih,
  rw [prod_insert anins, prod_insert anins, sum_insert anins],
  intro nz, rw polynomial.nat_degree_mul_eq', rw ih, apply right_ne_zero_of_mul nz,
  rwa polynomial.leading_coeff_prod', apply right_ne_zero_of_mul nz,
end

lemma monic_prod_monic :
  (∀ a : α, a ∈ s → monic (f a)) → monic (s.prod f) :=
by { apply prod_induction, apply monic_mul, apply monic_one }

lemma nat_degree_prod_eq_of_monic [nontrivial R] (h : ∀ i : α, i ∈ s → (f i).monic) :
  (s.prod f).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  apply nat_degree_prod_eq',
  suffices : ∏ (i : α) in s, (f i).leading_coeff = 1, { rw this, simp },
  rw prod_eq_one, intros, apply h, assumption,
end


end comm_semiring

section integral_domain

variables [integral_domain R] (f : α → polynomial R)

lemma nat_degree_prod_eq (h : ∀ i ∈ s, f i ≠ 0) :
  (s.prod f).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  apply nat_degree_prod_eq', rw prod_ne_zero_iff,
  intros x hx, simp [h x hx],
end

def leading_coeff_monoid_hom : polynomial R →* R :=
{to_fun := leading_coeff, map_one' := by simp, map_mul' := leading_coeff_mul}

@[simp] lemma coe_leading_coeff_monoid_hom (p : polynomial R) :
  leading_coeff_monoid_hom p = leading_coeff p := rfl

lemma leading_coeff_prod :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
begin
  rw ← coe_leading_coeff_monoid_hom, apply monoid_hom.map_prod,
end

end integral_domain
end poly_big_ops
end polynomial
