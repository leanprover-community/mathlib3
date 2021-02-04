/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Multivariate functions of the form `α^n → α` are isomorphic to multivariate polynomials in
`n` variables.
-/

import ring_theory.ideal.operations
import linear_algebra.finsupp_vector_space
import algebra.char_p.basic

noncomputable theory

open_locale classical

open set linear_map submodule
open_locale big_operators

namespace mv_polynomial
universes u v
variables {σ : Type u} {α : Type v}

section
variables (σ α) [field α] (m : ℕ)

lemma quotient_mk_comp_C_injective (I : ideal (mv_polynomial σ α)) (hI : I ≠ ⊤) :
  function.injective ((ideal.quotient.mk I).comp mv_polynomial.C) :=
begin
  refine (ring_hom.injective_iff _).2 (λ x hx, _),
  rw [ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem] at hx,
  refine classical.by_contradiction (λ hx0, absurd (I.eq_top_iff_one.2 _) hI),
  have := I.smul_mem (mv_polynomial.C x⁻¹) hx,
  rwa [smul_eq_mul, ← mv_polynomial.C.map_mul, inv_mul_cancel hx0, mv_polynomial.C_1] at this,
end

def restrict_total_degree : submodule α (mv_polynomial σ α) :=
finsupp.supported _ _ {n | n.sum (λn e, e) ≤ m }

lemma mem_restrict_total_degree (p : mv_polynomial σ α) :
  p ∈ restrict_total_degree σ α m ↔ p.total_degree ≤ m :=
begin
  rw [total_degree, finset.sup_le_iff],
  refl
end

end

section
variables (σ α)
def restrict_degree (m : ℕ) [field α] : submodule α (mv_polynomial σ α) :=
finsupp.supported _ _ {n | ∀i, n i ≤ m }
end

lemma mem_restrict_degree [field α] (p : mv_polynomial σ α) (n : ℕ) :
  p ∈ restrict_degree σ α n ↔ (∀s ∈ p.support, ∀i, (s : σ →₀ ℕ) i ≤ n) :=
begin
  rw [restrict_degree, finsupp.mem_supported],
  refl
end

lemma mem_restrict_degree_iff_sup [field α] (p : mv_polynomial σ α) (n : ℕ) :
  p ∈ restrict_degree σ α n ↔ ∀i, p.degrees.count i ≤ n :=
begin
  simp only [mem_restrict_degree, degrees, multiset.count_sup, finsupp.count_to_multiset,
    finset.sup_le_iff],
  exact ⟨assume h n s hs, h s hs n, assume h s hs n, h n s hs⟩
end

lemma map_range_eq_map {β : Type*} [comm_ring α] [comm_ring β] (p : mv_polynomial σ α)
  (f : α →+* β) :
  finsupp.map_range f f.map_zero p = map f p :=
begin
  rw [← finsupp.sum_single p, finsupp.sum],
  -- It's not great that we need to use an `erw` here,
  -- but hopefully it will become smoother when we move entirely away from `is_semiring_hom`.
  erw [finsupp.map_range_finset_sum (f : α →+ β)],
  rw [← p.support.sum_hom (map f)],
  { refine finset.sum_congr rfl (assume n _, _),
    rw [finsupp.map_range_single, ← monomial, ← monomial, map_monomial], refl, },
  apply_instance
end

section
variables (σ α)
lemma is_basis_monomials [field α] :
  is_basis α ((λs, (monomial s 1 : mv_polynomial σ α))) :=
suffices is_basis α (λ (sa : Σ _, unit), (monomial sa.1 1 : mv_polynomial σ α)),
begin
  apply is_basis.comp this (λ (s : σ →₀ ℕ), ⟨s, punit.star⟩),
  split,
  { intros x y hxy,
    simpa using hxy },
  { intros x,
    rcases x with ⟨x₁, x₂⟩,
    use x₁,
    rw punit_eq punit.star x₂ }
end,
begin
  apply finsupp.is_basis_single (λ _ _, (1 : α)),
  intro _,
  apply is_basis_singleton_one,
end
end

end mv_polynomial

namespace mv_polynomial
universe u
variables (σ : Type u) (α : Type u) [field α]

open_locale classical

lemma dim_mv_polynomial : vector_space.dim α (mv_polynomial σ α) = cardinal.mk (σ →₀ ℕ) :=
by rw [← cardinal.lift_inj, ← (is_basis_monomials σ α).mk_eq_dim]

end mv_polynomial

namespace mv_polynomial

variables (σ : Type*) (R : Type*) [comm_ring R] (p : ℕ)

instance [char_p R p] : char_p (mv_polynomial σ R) p :=
{ cast_eq_zero_iff := λ n, by rw [← C_eq_coe_nat, ← C_0, C_inj, char_p.cast_eq_zero_iff R p] }

end mv_polynomial
