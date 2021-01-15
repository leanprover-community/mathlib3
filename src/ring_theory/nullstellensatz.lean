/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ring_theory.jacobson
import field_theory.algebraic_closure
import field_theory.mv_polynomial

/-!
  # Nullstellensatz
  This file establishes a version of Hilbert's classical Nullstellensatz for `mv_polynomial`.
  The main statement of the theorem is `vanishing_ideal_zero_locus_eq_radical`.
-/

open ideal
open mv_polynomial

noncomputable theory

variables {k : Type*} [field k] [is_alg_closed k]
variables {σ : Type*} [fintype σ]

/-- The statement of the theorem is in terms of
-/
def vanishing_ideal (I : ideal (mv_polynomial σ k)) : set (σ → k) :=
  {x : σ → k | ∀ p ∈ I, eval x p = 0}

lemma vanishing_ideal_anti_mono (I J : ideal (mv_polynomial σ k)) (h : I ≤ J) :
  vanishing_ideal J ≤ vanishing_ideal I :=
λ x hx p hp, hx p $ h hp

lemma vanishing_ideal_bot : vanishing_ideal (⊥ : ideal (mv_polynomial σ k)) = ⊤ :=
begin
  refine le_antisymm le_top (λ x hx p hp, _),
  rw mem_bot.1 hp,
  exact (eval x).map_zero,
end

def zero_locus (V : set (σ → k)) : ideal (mv_polynomial σ k) :=
{ carrier := {p | ∀ x ∈ V, eval x p = 0},
  zero_mem' := λ x hx, ring_hom.map_zero _,
  add_mem' := λ p q hp hq x hx, by simp only [hq x hx, hp x hx, add_zero, ring_hom.map_add],
  smul_mem' := λ p q hq x hx,
    by simp only [hq x hx, algebra.id.smul_eq_mul, mul_zero, ring_hom.map_mul] }

lemma zero_locus_anti_mono {A B : set (σ → k)} (h : A ≤ B) : zero_locus B ≤ zero_locus A :=
λ p hp x hx, hp x $ h hx

lemma zero_locus_bot : zero_locus (∅ : set (σ → k)) = ⊤ :=
le_antisymm le_top (λ p hp x hx, absurd hx (set.not_mem_empty x))

lemma le_zero_locus_vanishing_ideal (I : ideal (mv_polynomial σ k)) :
  I ≤ zero_locus (vanishing_ideal I) :=
λ p hp x hx, hx p hp

lemma mem_zero_locus_singleton_iff (x : σ → k) (p : mv_polynomial σ k) :
  p ∈ (zero_locus {x} : ideal (mv_polynomial σ k)) ↔ (eval x p = 0) :=
⟨λ h, h x rfl, λ hpx y hy, hy.symm ▸ hpx⟩

lemma zero_locus_singleton_maximal (x : σ → k) :
  (zero_locus {x} : ideal (mv_polynomial σ k)).is_maximal :=
begin
  have : (zero_locus {x} : ideal (mv_polynomial σ k)).quotient ≃+* k := ring_equiv.of_bijective
    (ideal.quotient.lift _ (eval x) (λ p h, (mem_zero_locus_singleton_iff x p).mp h))
    begin
      refine ⟨_, λ z, ⟨(ideal.quotient.mk (zero_locus {x})) (C z), by simp⟩⟩,
      refine (ring_hom.injective_iff _).mpr (λ p hp, _),
      obtain ⟨q, rfl⟩ := quotient.mk_surjective p,
      rwa [quotient.lift_mk, ← mem_zero_locus_singleton_iff, ← quotient.eq_zero_iff_mem] at hp,
    end,
  rw [← bot_quotient_is_maximal_iff, ring_equiv.bot_maximal_iff this],
  exact bot_is_maximal,
end

lemma is_maximal_iff_eq_zero_locus_singleton (I : ideal (mv_polynomial σ k)) :
  I.is_maximal ↔ ∃ (x : σ → k), I = zero_locus {x} :=
begin
  refine ⟨_, λ h, let ⟨x, hx⟩ := h in hx.symm ▸ zero_locus_singleton_maximal x⟩,
  introsI hI,
  let ϕ : k →+* I.quotient := (ideal.quotient.mk I).comp C,
  -- Sorry half is from other PR #5520, proven using facts about Jacobson rings
  have hϕ : function.bijective ϕ := ⟨quotient_mk_comp_C_injective _ _ I hI.1, sorry⟩,
  obtain ⟨φ, hφ⟩ := function.surjective.has_right_inverse hϕ.2,

  let x : σ → k := λ s, φ ((ideal.quotient.mk I) (X s)),
  have hx : ∀ s : σ, ϕ (x s) = (ideal.quotient.mk I) (X s) :=
    λ s, hφ ((ideal.quotient.mk I) (X s)),
  have : zero_locus {x} ≤ I,
  { intros p hp,
    rw [← quotient.eq_zero_iff_mem, map_mv_polynomial_eq_eval₂ (ideal.quotient.mk I) p, eval₂_eq'],
    rw [mem_zero_locus_singleton_iff, eval_eq'] at hp,
    convert (trans (congr_arg ϕ hp) ϕ.map_zero),
    simp only [ϕ.map_sum, ϕ.map_mul, ϕ.map_prod, ϕ.map_pow, hx] },
  refine ⟨x, (is_maximal.eq_of_le (zero_locus_singleton_maximal x) hI.1 this).symm⟩,
end

/-- Main statement of the Nullstellensatz -/
theorem vanishing_ideal_zero_locus_eq_radical (I : ideal (mv_polynomial σ k)) :
  zero_locus (vanishing_ideal (I)) = I.radical :=
begin
  rw (radical_eq_jacobson I),
  refine le_antisymm _ _,
  { refine le_Inf _,
    rintros J ⟨hJI, hJ⟩,
    obtain ⟨x, hx⟩ := (is_maximal_iff_eq_zero_locus_singleton J).1 hJ,
    refine hx.symm ▸ zero_locus_anti_mono (λ y hy p hp, _),
    rw [← mem_zero_locus_singleton_iff, set.mem_singleton_iff.1 hy, ← hx],
    refine hJI hp },
  { refine λ p hp x hx, _,
    rw ← mem_zero_locus_singleton_iff x p,
    refine (mem_Inf.mp hp) ⟨le_trans (le_zero_locus_vanishing_ideal I)
      (zero_locus_anti_mono (λ y hy, hy.symm ▸ hx)), zero_locus_singleton_maximal x⟩ },
end
