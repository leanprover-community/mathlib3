/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
open polynomial finset

/-
# Polynomials

Lemmas for the interaction between polynomials and ∑ and ∏.

## Main results

- `nat_degree_prod_eq_of_monic` : the degree of a product of monic polynomials is the product of degrees
    we prove this only for [comm_semiring R], but it ought to be true for [semiring R] and list.prod
- `nat_degree_prod_eq` : for polynomials over an integral domain,
    the degree of the product is the sum of degrees
-/

noncomputable theory
open_locale big_operators

universes u w

variables {R : Type u} {α : Type w}

namespace polynomial

section comm_semiring_homs

variable [comm_semiring R]

/-- `polynomial.eval` bundled as a ring_hom -/
def eval_ring_hom : R → (polynomial R →+* R) := eval₂_ring_hom (ring_hom.id R)

@[simp]
lemma coe_eval_ring_hom (r : R) (p : polynomial R) : eval_ring_hom r p = eval r p := rfl

/-- A ring hom returning the constant term -/
def coeff_zero_ring_hom : polynomial R →+* R := eval_ring_hom 0

@[simp]
lemma coe_coeff_zero_ring_hom (p : polynomial R) : coeff_zero_ring_hom p = p.coeff 0 :=
by { rw coeff_zero_eq_eval_zero p, refl }

end comm_semiring_homs

section integral_domain_homs

variable [integral_domain R]

/-- `leading_coeff` bundled as a monoid hom-/
def leading_coeff_monoid_hom : polynomial R →* R :=
{to_fun := leading_coeff, map_one' := by simp, map_mul' := leading_coeff_mul}

@[simp] lemma coe_leading_coeff_monoid_hom (p : polynomial R) :
  leading_coeff_monoid_hom p = leading_coeff p := rfl

end integral_domain_homs

section poly_big_ops

variable (s : finset α)

section comm_semiring
variables [comm_semiring R] (f : α → polynomial R)

lemma nat_degree_prod_le : (s.prod f).nat_degree ≤ ∑ i in s, (f i).nat_degree :=
begin
  classical,
  apply s.induction_on, simp,intros a s anins ih,
  rw [prod_insert anins, sum_insert anins],
  transitivity (f a).nat_degree + (∏ (x : α) in s, (f x)).nat_degree,
  apply polynomial.nat_degree_mul_le, apply add_le_add_left ih,
end

lemma leading_coeff_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
begin
  classical,
  revert h, induction s using finset.induction with a s ha hs, { simp },
  repeat { rw prod_insert ha },
  intro h, rw polynomial.leading_coeff_mul'; { rwa hs, apply right_ne_zero_of_mul h },
end

lemma nat_degree_prod_eq' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (s.prod f).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  classical,
  revert h, induction s using finset.induction with a s ha hs, { simp },
  rw [prod_insert ha, prod_insert ha, sum_insert ha],
  intro h, rw polynomial.nat_degree_mul_eq', rw hs,
  apply right_ne_zero_of_mul h,
  rwa polynomial.leading_coeff_prod', apply right_ne_zero_of_mul h,
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

lemma leading_coeff_prod :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
by { rw ← coe_leading_coeff_monoid_hom, apply monoid_hom.map_prod }

end integral_domain
end poly_big_ops
end polynomial
