/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.dedekind_domain.ideal
import ring_theory.discrete_valuation_ring
import ring_theory.localization.at_prime
import ring_theory.localization.submodule
import ring_theory.valuation.tfae

/-!
# Dedekind domains

This file defines an equivalent notion of a Dedekind domain (or Dedekind ring),
namely a Noetherian integral domain where the localization at all nonzero prime ideals is a DVR
(TODO: and shows that implies the main definition).

## Main definitions

 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is Noetherian, and the localization at every nonzero prime ideal is a DVR.

## Main results
 - `is_localization.at_prime.discrete_valuation_ring_of_dedekind_domain` shows that
   `is_dedekind_domain` implies the localization at each nonzero prime ideal is a DVR.
 - `is_dedekind_domain.is_dedekind_domain_dvr` is one direction of the equivalence of definitions
   of a Dedekind domain

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [comm_ring A] [is_domain A] [field K]

open_locale non_zero_divisors polynomial

/--
A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

/-- Localizing a domain of Krull dimension `≤ 1` gives another ring of Krull dimension `≤ 1`.

Note that the same proof can/should be generalized to preserving any Krull dimension,
once we have a suitable definition.
-/
lemma ring.dimension_le_one.localization {R : Type*} (Rₘ : Type*) [comm_ring R] [is_domain R]
  [comm_ring Rₘ] [algebra R Rₘ] {M : submonoid R} [is_localization M Rₘ] (hM : M ≤ R⁰)
  (h : ring.dimension_le_one R) : ring.dimension_le_one Rₘ :=
begin
  introsI p hp0 hpp,
  refine ideal.is_maximal_def.mpr ⟨hpp.ne_top, ideal.maximal_of_no_maximal (λ P hpP hPm, _)⟩,
  have hpP' : (⟨p, hpp⟩ : {p : ideal Rₘ // p.is_prime}) < ⟨P, hPm.is_prime⟩ := hpP,
  rw ← (is_localization.order_iso_of_prime M Rₘ).lt_iff_lt at hpP',
  haveI : ideal.is_prime (ideal.comap (algebra_map R Rₘ) p) :=
    ((is_localization.order_iso_of_prime M Rₘ) ⟨p, hpp⟩).2.1,
  haveI : ideal.is_prime (ideal.comap (algebra_map R Rₘ) P) :=
    ((is_localization.order_iso_of_prime M Rₘ) ⟨P, hPm.is_prime⟩).2.1,
  have hlt : ideal.comap (algebra_map R Rₘ) p < ideal.comap (algebra_map R Rₘ) P := hpP',
  refine h.not_lt_lt ⊥ (ideal.comap _ _) (ideal.comap _ _) ⟨_, hpP'⟩,
  exact is_localization.bot_lt_comap_prime _ _ hM _ hp0
end

/-- The localization of a Dedekind domain is a Dedekind domain. -/
lemma is_localization.is_dedekind_domain [is_dedekind_domain A] {M : submonoid A} (hM : M ≤ A⁰)
  (Aₘ : Type*) [comm_ring Aₘ] [is_domain Aₘ] [algebra A Aₘ]
  [is_localization M Aₘ] : is_dedekind_domain Aₘ :=
begin
  have : ∀ (y : M), is_unit (algebra_map A (fraction_ring A) y),
  { rintros ⟨y, hy⟩,
    exact is_unit.mk0 _ (mt is_fraction_ring.to_map_eq_zero_iff.mp (non_zero_divisors.ne_zero
      (hM hy))) },
  letI : algebra Aₘ (fraction_ring A) := ring_hom.to_algebra (is_localization.lift this),
  haveI : is_scalar_tower A Aₘ (fraction_ring A) := is_scalar_tower.of_algebra_map_eq
    (λ x, (is_localization.lift_eq this x).symm),
  haveI : is_fraction_ring Aₘ (fraction_ring A) :=
    is_fraction_ring.is_fraction_ring_of_is_domain_of_is_localization M _ _,
  refine (is_dedekind_domain_iff _ (fraction_ring A)).mpr ⟨_, _, _⟩,
  { exact is_localization.is_noetherian_ring M _ (by apply_instance) },
  { exact is_dedekind_domain.dimension_le_one.localization Aₘ hM },
  { intros x hx,
    obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_is_localization M _,
    obtain ⟨z, hz⟩ := (is_integrally_closed_iff _).mp is_dedekind_domain.is_integrally_closed hy,
    refine ⟨is_localization.mk' Aₘ z ⟨y, y_mem⟩, (is_localization.lift_mk'_spec _ _ _ _).mpr _⟩,
    rw [hz, set_like.coe_mk, ← algebra.smul_def],
    refl },
end

/-- The localization of a Dedekind domain at every nonzero prime ideal is a Dedekind domain. -/
lemma is_localization.at_prime.is_dedekind_domain [is_dedekind_domain A]
  (P : ideal A) [P.is_prime] (Aₘ : Type*) [comm_ring Aₘ] [is_domain Aₘ] [algebra A Aₘ]
  [is_localization.at_prime Aₘ P] : is_dedekind_domain Aₘ :=
is_localization.is_dedekind_domain A P.prime_compl_le_non_zero_divisors Aₘ

lemma is_localization.at_prime.not_is_field
  {P : ideal A} (hP : P ≠ ⊥) [pP : P.is_prime]
  (Aₘ : Type*) [comm_ring Aₘ] [algebra A Aₘ] [is_localization.at_prime Aₘ P] :
  ¬ (is_field Aₘ) :=
begin
  intro h,
  letI := h.to_field,
  obtain ⟨x, x_mem, x_ne⟩ := P.ne_bot_iff.mp hP,
  exact (local_ring.maximal_ideal.is_maximal _).ne_top (ideal.eq_top_of_is_unit_mem _
    ((is_localization.at_prime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
    (is_unit_iff_ne_zero.mpr ((map_ne_zero_iff (algebra_map A Aₘ)
      (is_localization.injective Aₘ P.prime_compl_le_non_zero_divisors)).mpr x_ne))),
end

/-- In a Dedekind domain, the localization at every nonzero prime ideal is a DVR. -/
lemma is_localization.at_prime.discrete_valuation_ring_of_dedekind_domain [is_dedekind_domain A]
  {P : ideal A} (hP : P ≠ ⊥) [pP : P.is_prime]
  (Aₘ : Type*) [comm_ring Aₘ] [is_domain Aₘ] [algebra A Aₘ] [is_localization.at_prime Aₘ P] :
  discrete_valuation_ring Aₘ :=
begin
  classical,
  letI : is_noetherian_ring Aₘ := is_localization.is_noetherian_ring P.prime_compl _
    is_dedekind_domain.is_noetherian_ring,
  letI : local_ring Aₘ := is_localization.at_prime.local_ring Aₘ P,
  have hnf := is_localization.at_prime.not_is_field A hP Aₘ,
  exact ((discrete_valuation_ring.tfae Aₘ hnf).out 0 2).mpr
    (is_localization.at_prime.is_dedekind_domain A P _)
end

/-- Dedekind domains, in the sense of Noetherian integrally closed domains of Krull dimension ≤ 1,
are also Dedekind domains in the sense of Noetherian domains where the localization at every
nonzero prime ideal is a DVR. -/
theorem is_dedekind_domain.is_dedekind_domain_dvr [is_dedekind_domain A] :
  is_dedekind_domain_dvr A :=
{ is_noetherian_ring := is_dedekind_domain.is_noetherian_ring,
  is_dvr_at_nonzero_prime := λ P hP pP, by exactI
    is_localization.at_prime.discrete_valuation_ring_of_dedekind_domain A hP _ }
