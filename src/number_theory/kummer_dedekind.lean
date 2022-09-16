/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/

import ring_theory.adjoin_root
import ring_theory.dedekind_domain.ideal
import ring_theory.algebra_tower

/-!
# Kummer-Dedekind theorem

This file proves the monogenic version of the Kummer-Dedekind theorem on the splitting of prime
ideals in an extension of the ring of integers. This states that if `I` is a prime ideal of
Dedekind domain `R` and `S = R[α]` for some `α` that is integral over `R` with minimal polynomial
`f`, then the prime factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the
same number of prime factors, and each prime factors of `I * S` can be paired with a prime factor
of `f mod I` in a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

 * `normalized_factors_map_equiv_normalized_factors_min_poly_mk` : The bijection in the
    Kummer-Dedekind theorem. This is the pairing between the prime factors of `I * S` and the prime
    factors of `f mod I`.

## Main results

 * `normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map` : The Kummer-Dedekind
    theorem.
 * `ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebra_map R S)` is irreducible if
    `(map I^.quotient.mk (minpoly R pb.gen))` is irreducible, where `pb` is a power basis of `S`
    over `R`.

## TODO

 * Define the conductor ideal and prove the Kummer-Dedekind theorem in full generality.

 * Prove the converse of `ideal.irreducible_map_of_irreducible_minpoly`.

 * Prove that `normalized_factors_map_equiv_normalized_factors_min_poly_mk` can be expressed as
    `normalized_factors_map_equiv_normalized_factors_min_poly_mk g = ⟨I, G(α)⟩` for `g` a prime
    factor of `f mod I` and `G` a lift of `g` to `R[X]`.

## References

 * [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

namespace kummer_dedekind

open_locale big_operators polynomial classical

open ideal polynomial double_quot unique_factorization_monoid

variables {R : Type*} [comm_ring R]
variables {S : Type*} [comm_ring S] [is_domain S] [is_dedekind_domain S] [algebra R S]
variables (pb : power_basis R S) {I : ideal R}

local attribute [instance] ideal.quotient.field

variables [is_domain R]

/-- The first half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the prime
    factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
    over `R`, taken `mod I`.-/
noncomputable def normalized_factors_map_equiv_normalized_factors_min_poly_mk (hI : is_maximal I)
  (hI' : I ≠ ⊥) : {J : ideal S | J ∈ normalized_factors (I.map (algebra_map R S) )} ≃
    {d : (R ⧸ I)[X] | d ∈ normalized_factors (map I^.quotient.mk (minpoly R pb.gen)) } :=
((normalized_factors_equiv_of_quot_equiv ↑(pb.quotient_equiv_quotient_minpoly_map I)
  --show that `I * S` ≠ ⊥
  (show I.map (algebra_map R S) ≠ ⊥,
    by rwa [ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective, ← ne.def])
  --show that the ideal spanned by `(minpoly R pb.gen) mod I` is non-zero
  (by {by_contra, exact (show (map I^.quotient.mk (minpoly R pb.gen) ≠ 0), from
    polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))
    (span_singleton_eq_bot.mp h) } )).trans
  (normalized_factors_equiv_span_normalized_factors
    (show (map I^.quotient.mk (minpoly R pb.gen)) ≠ 0, from
      polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))).symm)

/-- The second half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the
    bijection `factors_equiv'` defined in the first half preserves multiplicities. -/
theorem multiplicity_factors_map_eq_multiplicity (hI : is_maximal I) (hI' : I ≠ ⊥) {J : ideal S}
  (hJ : J ∈ normalized_factors (I.map (algebra_map R S))) :
  multiplicity J (I.map (algebra_map R S)) =
    multiplicity ↑(normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' ⟨J, hJ⟩)
    (map I^.quotient.mk (minpoly R pb.gen)) :=
by rw [normalized_factors_map_equiv_normalized_factors_min_poly_mk, equiv.coe_trans,
       function.comp_app,
       multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity,
       normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity]

/-- The **Kummer-Dedekind Theorem**. -/
theorem normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map (hI : is_maximal I)
  (hI' : I ≠ ⊥) : normalized_factors (I.map (algebra_map R S)) = multiset.map
  (λ f, ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm f : ideal S))
      (normalized_factors (polynomial.map I^.quotient.mk (minpoly R pb.gen))).attach :=
begin
  ext J,
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalized_factors (I.map (algebra_map R S)), swap,
  { rw [multiset.count_eq_zero.mpr hJ, eq_comm, multiset.count_eq_zero, multiset.mem_map],
    simp only [multiset.mem_attach, true_and, not_exists],
    rintros J' rfl,
    exact hJ
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm J').prop },

  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := multiplicity_factors_map_eq_multiplicity pb hI hI' hJ,
  rw [multiplicity_eq_count_normalized_factors, multiplicity_eq_count_normalized_factors,
      unique_factorization_monoid.normalize_normalized_factor _ hJ,
      unique_factorization_monoid.normalize_normalized_factor,
      part_enat.coe_inj]
    at this,
  refine this.trans _,
  -- Get rid of the `map` by applying the equiv to both sides.
  generalize hJ' : (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI')
    ⟨J, hJ⟩ = J',
  have : ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm
    J' : ideal S) = J,
  { rw [← hJ', equiv.symm_apply_apply _ _, subtype.coe_mk] },
  subst this,
  -- Get rid of the `attach` by applying the subtype `coe` to both sides.
  rw [multiset.count_map_eq_count' (λ f,
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm f
        : ideal S)),
      multiset.attach_count_eq_count_coe],
  { exact subtype.coe_injective.comp (equiv.injective _) },
  { exact (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).prop },
  { exact irreducible_of_normalized_factor _
    (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).prop },
  { exact polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen) },
  { exact irreducible_of_normalized_factor _ hJ },
  { rwa [← bot_eq_zero, ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective] },
end

theorem ideal.irreducible_map_of_irreducible_minpoly (hI : is_maximal I) (hI' : I ≠ ⊥)
  (hf : irreducible (map I^.quotient.mk (minpoly R pb.gen))) :
  irreducible (I.map (algebra_map R S)) :=
begin
  have mem_norm_factors : normalize (map I^.quotient.mk (minpoly R pb.gen)) ∈ normalized_factors
    (map I^.quotient.mk (minpoly R pb.gen)) := by simp [normalized_factors_irreducible hf],
  suffices : ∃ x, normalized_factors (I.map (algebra_map R S)) = {x},
  { obtain ⟨x, hx⟩ := this,
    have h := normalized_factors_prod (show I.map (algebra_map R S) ≠ 0, by
      rwa [← bot_eq_zero, ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective]),
    rw [associated_iff_eq, hx, multiset.prod_singleton] at h,
    rw ← h,
    exact irreducible_of_normalized_factor x
      (show x ∈ normalized_factors (I.map (algebra_map R S)), by simp [hx]) },
  rw normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map pb hI hI',
  use ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm
    ⟨normalize (map I^.quotient.mk (minpoly R pb.gen)), mem_norm_factors⟩ : ideal S),
  rw multiset.map_eq_singleton,
  use ⟨normalize (map I^.quotient.mk (minpoly R pb.gen)), mem_norm_factors⟩,
  refine ⟨_, rfl⟩,
  apply multiset.map_injective subtype.coe_injective,
  rw [multiset.attach_map_coe, multiset.map_singleton, subtype.coe_mk],
  exact normalized_factors_irreducible hf
end

end kummer_dedekind
