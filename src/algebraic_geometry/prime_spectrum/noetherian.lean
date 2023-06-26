/-
Copyright (c) 2020 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Andrew Yang
-/
import algebraic_geometry.prime_spectrum.basic
import topology.noetherian_space
/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties of the prime spectrum a ring is Noetherian.
-/

universes u v

namespace prime_spectrum

open submodule

variables (R : Type u) [comm_ring R] [is_noetherian_ring R]
variables {A : Type u} [comm_ring A] [is_domain A] [is_noetherian_ring A]

/--In a noetherian ring, every ideal contains a product of prime ideals
([samuel, § 3.3, Lemma 3])-/
lemma exists_prime_spectrum_prod_le (I : ideal R) :
  ∃ (Z : multiset (prime_spectrum R)), multiset.prod (Z.map as_ideal) ≤ I :=
begin
  refine is_noetherian.induction (λ (M : ideal R) hgt, _) I,
  by_cases h_prM : M.is_prime,
  { use {⟨M, h_prM⟩},
    rw [multiset.map_singleton, multiset.prod_singleton],
    exact le_rfl },
  by_cases htop : M = ⊤,
  { rw htop,
    exact ⟨0, le_top⟩ },
  have lt_add : ∀ z ∉ M, M < M + span R {z},
  { intros z hz,
    refine lt_of_le_of_ne le_sup_left (λ m_eq, hz _),
    rw m_eq,
    exact ideal.mem_sup_right (mem_span_singleton_self z) },
  obtain ⟨x, hx, y, hy, hxy⟩ := (ideal.not_is_prime_iff.mp h_prM).resolve_left htop,
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx),
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy),
  use Wx + Wy,
  rw [multiset.map_add, multiset.prod_add],
  apply le_trans (submodule.mul_le_mul h_Wx h_Wy),
  rw add_mul,
  apply sup_le (show M * (M + span R {y}) ≤ M, from ideal.mul_le_right),
  rw mul_add,
  apply sup_le (show span R {x} * M ≤ M, from ideal.mul_le_left),
  rwa [span_mul_span, set.singleton_mul_singleton, span_singleton_le_iff_mem],
end

/--In a noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel, § 3.3, Lemma 3]) -/
lemma exists_prime_spectrum_prod_le_and_ne_bot_of_domain
  (h_fA : ¬ is_field A) {I : ideal A} (h_nzI: I ≠ ⊥) :
  ∃ (Z : multiset (prime_spectrum A)), multiset.prod (Z.map as_ideal) ≤ I ∧
    multiset.prod (Z.map as_ideal) ≠ ⊥ :=
begin
  revert h_nzI,
  refine is_noetherian.induction (λ (M : ideal A) hgt, _) I,
  intro h_nzM,
  have hA_nont : nontrivial A,
  apply is_domain.to_nontrivial A,
  by_cases h_topM : M = ⊤,
  { rcases h_topM with rfl,
    obtain ⟨p_id, h_nzp, h_pp⟩ : ∃ (p : ideal A), p ≠ ⊥ ∧ p.is_prime,
    { apply ring.not_is_field_iff_exists_prime.mp h_fA },
    use [({⟨p_id, h_pp⟩} : multiset (prime_spectrum A)), le_top],
    rwa [multiset.map_singleton, multiset.prod_singleton] },
  by_cases h_prM : M.is_prime,
  { use ({⟨M, h_prM⟩} : multiset (prime_spectrum A)),
    rw [multiset.map_singleton, multiset.prod_singleton],
    exact ⟨le_rfl, h_nzM⟩ },
  obtain ⟨x, hx, y, hy, h_xy⟩ := (ideal.not_is_prime_iff.mp h_prM).resolve_left h_topM,
  have lt_add : ∀ z ∉ M, M < M + span A {z},
  { intros z hz,
    refine lt_of_le_of_ne le_sup_left (λ m_eq, hz _),
    rw m_eq,
    exact mem_sup_right (mem_span_singleton_self z) },
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx)),
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy)),
  use Wx + Wy,
  rw [multiset.map_add, multiset.prod_add],
  refine ⟨le_trans (submodule.mul_le_mul h_Wx_le h_Wy_le) _, mt ideal.mul_eq_bot.mp _⟩,
  { rw add_mul,
    apply sup_le (show M * (M + span A {y}) ≤ M, from ideal.mul_le_right),
    rw mul_add,
    apply sup_le (show span A {x} * M ≤ M, from ideal.mul_le_left),
    rwa [span_mul_span, set.singleton_mul_singleton, span_singleton_le_iff_mem] },
  { rintro (hx | hy); contradiction },
end

open topological_space

instance : noetherian_space (prime_spectrum R) :=
begin
  rw (noetherian_space_tfae $ prime_spectrum R).out 0 1,
  have H := ‹is_noetherian_ring R›,
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H,
  exact (closeds_embedding R).dual.well_founded H
end

end prime_spectrum
