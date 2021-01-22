/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ring_theory.jacobson
import field_theory.algebraic_closure
import field_theory.mv_polynomial
import algebraic_geometry.prime_spectrum

/-!
# Nullstellensatz
This file establishes a version of Hilbert's classical Nullstellensatz for `mv_polynomial`s.
The main statement of the theorem is `vanishing_ideal_zero_locus_eq_radical`.

The statement is in terms of new definitions `vanishing_ideal` and `zero_locus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishing_ideal` and `zero_locus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/

open ideal

noncomputable theory

namespace mv_polynomial
open mv_polynomial

variables {k : Type*} [field k]
variables {σ : Type*}

/-- Set of points that are zeroes of all polynomials in an ideal -/
def zero_locus (I : ideal (mv_polynomial σ k)) : set (σ → k) :=
{x : σ → k | ∀ p ∈ I, eval x p = 0}

@[simp] lemma mem_zero_locus_iff {I : ideal (mv_polynomial σ k)} {x : σ → k} :
  x ∈ zero_locus I ↔ ∀ p ∈ I, eval x p = 0 := iff.rfl

lemma zero_locus_anti_mono {I J : ideal (mv_polynomial σ k)} (h : I ≤ J) :
  zero_locus J ≤ zero_locus I :=
λ x hx p hp, hx p $ h hp

lemma zero_locus_bot : zero_locus (⊥ : ideal (mv_polynomial σ k)) = ⊤ :=
eq_top_iff.2 (λ x hx p hp, trans (congr_arg (eval x) (mem_bot.1 hp)) (eval x).map_zero)

lemma zero_locus_top : zero_locus (⊤ : ideal (mv_polynomial σ k)) = ⊥ :=
eq_bot_iff.2 $ λ x hx, one_ne_zero ((eval x).map_one ▸ (hx 1 submodule.mem_top) : (1 : k) = 0)

/-- Ideal of polynomials with common zeroes at all elements of a set -/
def vanishing_ideal (V : set (σ → k)) : ideal (mv_polynomial σ k) :=
{ carrier := {p | ∀ x ∈ V, eval x p = 0},
  zero_mem' := λ x hx, ring_hom.map_zero _,
  add_mem' := λ p q hp hq x hx, by simp only [hq x hx, hp x hx, add_zero, ring_hom.map_add],
  smul_mem' := λ p q hq x hx,
    by simp only [hq x hx, algebra.id.smul_eq_mul, mul_zero, ring_hom.map_mul] }

@[simp] lemma mem_vanishing_ideal_iff {V : set (σ → k)} {p : mv_polynomial σ k} :
  p ∈ vanishing_ideal V ↔ ∀ x ∈ V, eval x p = 0 := iff.rfl

lemma vanishing_ideal_anti_mono {A B : set (σ → k)} (h : A ≤ B) :
  vanishing_ideal B ≤ vanishing_ideal A :=
λ p hp x hx, hp x $ h hx

lemma vanishing_ideal_empty : vanishing_ideal (∅ : set (σ → k)) = ⊤ :=
le_antisymm le_top (λ p hp x hx, absurd hx (set.not_mem_empty x))

lemma le_vanishing_ideal_zero_locus (I : ideal (mv_polynomial σ k)) :
  I ≤ vanishing_ideal (zero_locus I) :=
λ p hp x hx, hx p hp

lemma zero_locus_vanishing_ideal_le (V : set (σ → k)) :
  V ≤ zero_locus (vanishing_ideal V) :=
λ V hV p hp, hp V hV

theorem zero_locus_vanishing_ideal_galois_connection :
  @galois_connection (ideal (mv_polynomial σ k)) (order_dual (set (σ → k))) _ _
    zero_locus vanishing_ideal :=
λ I V, ⟨λ h, le_trans (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono h),
  λ h, le_trans (zero_locus_anti_mono h) (zero_locus_vanishing_ideal_le V)⟩

lemma mem_vanishing_ideal_singleton_iff (x : σ → k) (p : mv_polynomial σ k) :
  p ∈ (vanishing_ideal {x} : ideal (mv_polynomial σ k)) ↔ (eval x p = 0) :=
⟨λ h, h x rfl, λ hpx y hy, hy.symm ▸ hpx⟩

instance vanishing_ideal_singleton_is_maximal {x : σ → k} :
  (vanishing_ideal {x} : ideal (mv_polynomial σ k)).is_maximal :=
begin
  have : (vanishing_ideal {x} : ideal (mv_polynomial σ k)).quotient ≃+* k := ring_equiv.of_bijective
    (ideal.quotient.lift _ (eval x) (λ p h, (mem_vanishing_ideal_singleton_iff x p).mp h))
    begin
      refine ⟨_, λ z, ⟨(ideal.quotient.mk (vanishing_ideal {x})) (C z), by simp⟩⟩,
      refine (ring_hom.injective_iff _).mpr (λ p hp, _),
      obtain ⟨q, rfl⟩ := quotient.mk_surjective p,
      rwa [quotient.lift_mk, ← mem_vanishing_ideal_singleton_iff, ← quotient.eq_zero_iff_mem] at hp,
    end,
  rw [← bot_quotient_is_maximal_iff, ring_equiv.bot_maximal_iff this],
  exact bot_is_maximal,
end

lemma radical_le_vanishing_ideal_zero_locus (I : ideal (mv_polynomial σ k)) :
  I.radical ≤ vanishing_ideal (zero_locus I) :=
begin
  intros p hp x hx,
  rw ← mem_vanishing_ideal_singleton_iff,
  rw radical_eq_Inf at hp,
  refine (mem_Inf.mp hp) ⟨le_trans (le_vanishing_ideal_zero_locus I)
    (vanishing_ideal_anti_mono (λ y hy, hy.symm ▸ hx)), is_maximal.is_prime' _⟩,
end

/-- Transfer a set of points into the language of the prime spectrum,
  `vanishing_ideal_points_to_points` and `points_to_points_zero_locus` give the computation rules -/
def points_to_points : set (σ → k) → set (prime_spectrum (mv_polynomial σ k)) :=
λ V, {J | vanishing_ideal V ≤ J.as_ideal}

@[simp] lemma vanishing_ideal_points_to_points (V : set (σ → k)) :
  prime_spectrum.vanishing_ideal (points_to_points V) = mv_polynomial.vanishing_ideal V :=
le_antisymm
  (λ p hp x hx, (mem_vanishing_ideal_singleton_iff x p).1
    (((prime_spectrum.mem_vanishing_ideal _ _).1 hp) ⟨vanishing_ideal {x}, is_maximal.is_prime' _⟩
    (λ p hp, (vanishing_ideal_anti_mono (λ _ hx', hx'.symm ▸ hx : {x} ≤ V) hp))))
  (λ p hp, (prime_spectrum.mem_vanishing_ideal _ _).2 (λ I hI, hI hp))

variables [is_alg_closed k] [fintype σ]

lemma is_maximal_iff_eq_vanishing_ideal_singleton (I : ideal (mv_polynomial σ k)) :
  I.is_maximal ↔ ∃ (x : σ → k), I = vanishing_ideal {x} :=
begin
  refine ⟨λ hI, _, λ h, let ⟨x, hx⟩ := h in
    hx.symm ▸ (mv_polynomial.vanishing_ideal_singleton_is_maximal)⟩,
  letI : I.is_maximal := hI,
  letI : field I.quotient := quotient.field I,
  let ϕ : k →+* I.quotient := (ideal.quotient.mk I).comp C,
  have hϕ : function.bijective ϕ := ⟨quotient_mk_comp_C_injective _ _ I hI.1,
    is_alg_closed.algebra_map_surjective_of_is_integral' ϕ
      (mv_polynomial.comp_C_integral_of_surjective_of_jacobson _ quotient.mk_surjective)⟩,
  obtain ⟨φ, hφ⟩ := function.surjective.has_right_inverse hϕ.2,
  let x : σ → k := λ s, φ ((ideal.quotient.mk I) (X s)),
  have hx : ∀ s : σ, ϕ (x s) = (ideal.quotient.mk I) (X s) := λ s, hφ ((ideal.quotient.mk I) (X s)),
  have : vanishing_ideal {x} ≤ I,
  { intros p hp,
    rw [← quotient.eq_zero_iff_mem, map_mv_polynomial_eq_eval₂ (ideal.quotient.mk I) p, eval₂_eq'],
    rw [mem_vanishing_ideal_singleton_iff, eval_eq'] at hp,
    convert (trans (congr_arg ϕ hp) ϕ.map_zero),
    simp only [ϕ.map_sum, ϕ.map_mul, ϕ.map_prod, ϕ.map_pow, hx] },
  refine ⟨x, ((mv_polynomial.vanishing_ideal_singleton_is_maximal).eq_of_le hI.1 this).symm⟩,
end

/-- Main statement of the Nullstellensatz -/
@[simp] theorem vanishing_ideal_zero_locus_eq_radical (I : ideal (mv_polynomial σ k)) :
  vanishing_ideal (zero_locus I) = I.radical :=
begin
  rw I.radical_eq_jacobson,
  refine le_antisymm (le_Inf _) (λ p hp x hx, _),
  { rintros J ⟨hJI, hJ⟩,
    obtain ⟨x, hx⟩ := (is_maximal_iff_eq_vanishing_ideal_singleton J).1 hJ,
    refine hx.symm ▸ vanishing_ideal_anti_mono (λ y hy p hp, _),
    rw [← mem_vanishing_ideal_singleton_iff, set.mem_singleton_iff.1 hy, ← hx],
    refine hJI hp },
  { rw ← mem_vanishing_ideal_singleton_iff x p,
    refine (mem_Inf.mp hp) ⟨le_trans (le_vanishing_ideal_zero_locus I)
      (vanishing_ideal_anti_mono (λ y hy, hy.symm ▸ hx)),
        mv_polynomial.vanishing_ideal_singleton_is_maximal⟩ },
end

lemma is_prime.vanishing_ideal_zero_locus (P : ideal (mv_polynomial σ k)) [hP : P.is_prime] :
  vanishing_ideal (zero_locus P) = P :=
trans (vanishing_ideal_zero_locus_eq_radical P) hP.radical

@[simp] lemma points_to_points_zero_locus (I : ideal (mv_polynomial σ k)) :
  points_to_points (mv_polynomial.zero_locus I) = prime_spectrum.zero_locus ↑I :=
le_antisymm (λ J hJ p hp, hJ $ le_vanishing_ideal_zero_locus I hp)
begin
  refine λ J hJ p hp, _,
  rw ← is_prime.vanishing_ideal_zero_locus J.as_ideal,
  refine vanishing_ideal_anti_mono (zero_locus_anti_mono hJ) hp,
end

end mv_polynomial
