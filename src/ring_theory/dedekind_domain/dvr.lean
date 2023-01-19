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
(TODO: and shows that it is equivalent to the main definition).

## Main definitions

 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is Noetherian, and the localization at every nonzero prime ideal is a DVR.

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

/-- The localization of a Dedekind domain at every nonzero prime ideal is a Dedekind domain. -/
lemma is_localization.at_prime.is_dedekind_domain [is_dedekind_domain A]
  (P : ideal A) (hP : P ≠ ⊥) [P.is_prime] (Aₘ : Type*) [comm_ring Aₘ] [is_domain Aₘ] [algebra A Aₘ]
  [is_localization.at_prime Aₘ P] : is_dedekind_domain Aₘ :=
begin
  letI : algebra Aₘ (fraction_ring A) := _,
  haveI : is_fraction_ring Aₘ (fraction_ring A) := _,
  refine (is_dedekind_domain_iff _ (fraction_ring A)).mpr ⟨_, _, _⟩,
end

lemma ideal.exists_mem_iff_ne_bot {R : Type*} [semiring R] {I : ideal R} :
  (∃ x ∈ I, x ≠ (0 : R)) ↔ I ≠ ⊥ :=
by simp only [ne.def, ← ideal.mem_bot, ← not_bot_lt_iff, not_not, set_like.lt_iff_le_and_exists,
    bot_le, true_and]

lemma is_localization.at_prime.not_is_field
  (P : ideal A) (hP : P ≠ ⊥) [pP : P.is_prime]
  (Aₘ : Type*) [comm_ring Aₘ] [is_domain Aₘ] [algebra A Aₘ] [is_localization.at_prime Aₘ P] :
  ¬ (is_field Aₘ) :=
begin
  intro h,
  letI := h.to_field,
  obtain ⟨x, x_mem, x_ne⟩ := ideal.exists_mem_iff_ne_bot.mpr hP,
  exact (local_ring.maximal_ideal.is_maximal _).ne_top (ideal.eq_top_of_is_unit_mem _
    ((is_localization.at_prime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
    (is_unit_iff_ne_zero.mpr ((map_ne_zero_iff (algebra_map A Aₘ)
      (is_localization.injective Aₘ P.prime_compl_le_non_zero_divisors)).mpr x_ne))),
end

/-- In a Dedekind domain, the localization at every nonzero prime ideal is a DVR. -/
lemma is_localization.at_prime.discrete_valuation_ring_of_dedekind_domain [is_dedekind_domain A]
  (P : ideal A) (hP : P ≠ ⊥) [pP : P.is_prime]
  (Aₘ : Type*) [comm_ring Aₘ] [is_domain Aₘ] [algebra A Aₘ] [is_localization.at_prime Aₘ P] :
  discrete_valuation_ring Aₘ :=
begin
  classical,
  letI : is_noetherian_ring Aₘ := is_localization.is_noetherian_ring P.prime_compl _
    is_dedekind_domain.is_noetherian_ring,
  letI : local_ring Aₘ := is_localization.at_prime.local_ring Aₘ P,
  refine ((discrete_valuation_ring.tfae Aₘ (is_localization.at_prime.not_is_field A P hP Aₘ)).out 0 6).mpr
    (λ I hI, _),
  let J : ideal A := ideal.comap (algebra_map A Aₘ) I,
  letI := ideal.cancel_comm_monoid_with_zero,
  let n : ℕ := multiset.count P (unique_factorization_monoid.normalized_factors J),
end
