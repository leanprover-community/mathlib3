/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/

import ring_theory.ideal.operations
import linear_algebra.finsupp_vector_space
import algebra.char_p.basic

/-!
# Multivariate polynomials over commutative rings

This file contains basic facts about multivariate polynomials over commutative rings, for example
that the monomials form a basis.

## Main definitions

* `restrict_total_degree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` of total degree at most `m`.
* `restrict_degree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` such that the degree in each individual variable is at most `m`.

## Main statements

* The multivariate polynomial ring over a commutative ring of positive characteristic has positive
  characteristic.
* `is_basis_monomials`: shows that the monomials form a basis of the vector space of multivariate
  polynomials.

## TODO

Generalise to noncommutative (semi)rings
-/

noncomputable theory

open_locale classical

open set linear_map submodule
open_locale big_operators

universes u v
variables (σ : Type u) (R : Type v) [comm_ring R] (p m : ℕ)

namespace mv_polynomial

section char_p

instance [char_p R p] : char_p (mv_polynomial σ R) p :=
{ cast_eq_zero_iff := λ n, by rw [← C_eq_coe_nat, ← C_0, C_inj, char_p.cast_eq_zero_iff R p] }

end char_p

section homomorphism

lemma map_range_eq_map {R S : Type*} [comm_ring R] [comm_ring S] (p : mv_polynomial σ R)
  (f : R →+* S) :
  finsupp.map_range f f.map_zero p = map f p :=
begin
  rw [← finsupp.sum_single p, finsupp.sum],
  -- It's not great that we need to use an `erw` here,
  -- but hopefully it will become smoother when we move entirely away from `is_semiring_hom`.
  erw [finsupp.map_range_finset_sum (f : R →+ S)],
  rw [← p.support.sum_hom (map f)],
  { refine finset.sum_congr rfl (assume n _, _),
    rw [finsupp.map_range_single, ← monomial, ← monomial, map_monomial], refl, },
  apply_instance
end

end homomorphism

section degree

/-- The submodule of polynomials of total degree less than or equal to `m`.-/
def restrict_total_degree : submodule R (mv_polynomial σ R) :=
finsupp.supported _ _ {n | n.sum (λn e, e) ≤ m }

/-- The submodule of polynomials such that the degree with respect to each individual variable is
less than or equal to `m`.-/
def restrict_degree (m : ℕ) : submodule R (mv_polynomial σ R) :=
finsupp.supported _ _ {n | ∀i, n i ≤ m }

variable {R}

lemma mem_restrict_total_degree (p : mv_polynomial σ R) :
  p ∈ restrict_total_degree σ R m ↔ p.total_degree ≤ m :=
begin
  rw [total_degree, finset.sup_le_iff],
  refl
end

lemma mem_restrict_degree (p : mv_polynomial σ R) (n : ℕ) :
  p ∈ restrict_degree σ R n ↔ (∀s ∈ p.support, ∀i, (s : σ →₀ ℕ) i ≤ n) :=
begin
  rw [restrict_degree, finsupp.mem_supported],
  refl
end

lemma mem_restrict_degree_iff_sup (p : mv_polynomial σ R) (n : ℕ) :
  p ∈ restrict_degree σ R n ↔ ∀i, p.degrees.count i ≤ n :=
begin
  simp only [mem_restrict_degree, degrees, multiset.count_sup, finsupp.count_to_multiset,
    finset.sup_le_iff],
  exact ⟨assume h n s hs, h s hs n, assume h s hs n, h n s hs⟩
end

variables (σ R)

lemma is_basis_monomials :
  is_basis R ((λs, (monomial s 1 : mv_polynomial σ R))) :=
suffices is_basis R (λ (sa : Σ _, unit), (monomial sa.1 1 : mv_polynomial σ R)),
begin
  apply is_basis.comp this (λ (s : σ →₀ ℕ), ⟨s, punit.star⟩),
  split,
  { intros x y hxy,
    simpa using hxy },
  { rintros ⟨x₁, x₂⟩,
    use x₁,
    rw punit_eq punit.star x₂ }
end,
begin
  apply finsupp.is_basis_single (λ _ _, (1 : R)),
  intro _,
  apply is_basis_singleton_one,
end

end degree

end mv_polynomial
