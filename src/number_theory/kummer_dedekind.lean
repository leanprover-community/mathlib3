/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/

import field_theory.minpoly
import ring_theory.adjoin_root
import ring_theory.dedekind_domain.ideal
import ring_theory.ideal.operations
import ring_theory.polynomial.basic
import ring_theory.power_basis
import ring_theory.unique_factorization_domain
import data.polynomial.field_division
import ring_theory.chain_of_divisors
import algebra.algebra.basic

/-!
# Kummer-Dedekind theorem

This file proves the Kummer-Dedekind theorem on the splitting of prime ideals in an extension
of the ring of integers.

## Main definitions

 * `factors_equiv'` : The bijection in the Kummer-Dedekind theorem

## Main results

 * `normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map` : The Kummer-Dedekind
    theorem
 * `ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebra_map R S)` is irreducible if
    `(map I^.quotient.mk (minpoly R pb.gen))` is irreducible, where `pb` is a power basis of `S`
    over `R`

## TODO
 * Define the conductor ideal and prove the Kummer-Dedekind theorem in full generality
 * Prove the converse of `ideal.irreducible_map_of_irreducible_minpoly`

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

open_locale big_operators

open ideal polynomial double_quot unique_factorization_monoid

open_locale classical

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]

variables {S : Type*} [comm_ring S] [algebra R S]

lemma temporary (f : polynomial R) (r : R) :
  adjoin_root.of f r = adjoin_root.mk f (polynomial.C r) := rfl

open alg_equiv

variable [decidable_eq (ideal S)]

noncomputable instance {I: ideal R} [hI : is_maximal I] : field (R ⧸ I) :=
((ideal.quotient.maximal_ideal_iff_is_field_quotient I).mp hI).to_field

namespace kummer_dedekind

variables [is_domain R] [is_dedekind_domain R] [is_domain S] [is_dedekind_domain S] [algebra R S]
variables  (pb : power_basis R S) {I : ideal R}

noncomputable def factors_equiv (hI : is_maximal I) :
  {J : ideal S | J ∣ I.map (algebra_map R S) } ≃o
    {J : ideal (polynomial $ R ⧸ I ) | J ∣ ideal.span { map I^.quotient.mk (minpoly R pb.gen) }} :=
ideal_factors_equiv_of_quot_equiv (pb.quotient_equiv_quotient_minpoly_map I)

lemma factors_equiv_is_dvd_iso (hI : is_maximal I) (l l' : ideal S)
  (hl : l ∣  I.map (algebra_map R S)) (hl' : l'∣ I.map (algebra_map R S) ) :
  (factors_equiv pb hI ⟨l, hl⟩ : ideal (polynomial $ R ⧸ I )) ∣
    (factors_equiv pb hI ⟨l', hl'⟩) ↔ l ∣ l' :=
begin
  suffices : factors_equiv pb hI ⟨l', hl'⟩ ≤ factors_equiv pb hI ⟨l, hl⟩
    ↔ (⟨l', hl'⟩ : {J : ideal S | J ∣ I.map (algebra_map R S)}) ≤ ⟨l, hl⟩,
  rwa [subtype.mk_le_mk, ← subtype.coe_le_coe, ← dvd_iff_le, ← dvd_iff_le] at this,
  exact (factors_equiv pb hI).le_iff_le,
end

lemma mem_normalized_factors_factors_equiv_of_mem_normalized_factors (hI : is_maximal I)
  (hI' : I.map (algebra_map R S) ≠ ⊥) (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0)
  (J : ideal S) (hJ : J ∈ normalized_factors (I.map (algebra_map R S) )) :
  ↑(factors_equiv pb hI ⟨J, dvd_of_mem_normalized_factors hJ⟩) ∈ normalized_factors
    (ideal.span ({ map I^.quotient.mk (minpoly R pb.gen) } : set (polynomial $ R ⧸ I) ) ) :=
begin
  refine mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors hI' _ hJ _,
  { by_contra ; exact hpb (span_singleton_eq_bot.mp h)},
  { rintros ⟨l, hl⟩ ⟨l', hl'⟩,
    rw [subtype.coe_mk, subtype.coe_mk],
    apply factors_equiv_is_dvd_iso pb hI l l' hl hl' },
end

lemma factors_equiv_symm_mem (hI : I.is_maximal) (hI' : map (algebra_map R S) I ≠ ⊥)
  (hpb : polynomial.map (ideal.quotient.mk I) (minpoly R pb.gen) ≠ 0)
  (j : {J : ideal (polynomial (R ⧸ I)) | J ∈ normalized_factors
   (ideal.span ({polynomial.map I^.quotient.mk (minpoly R pb.gen)} : set (polynomial (R ⧸ I))))})
  (hj' : ↑j ∣ span {polynomial.map I^.quotient.mk (minpoly R pb.gen)}) :
  (((factors_equiv pb hI).symm) ⟨j, hj'⟩ : ideal S) ∈ normalized_factors (I.map (algebra_map R S)):=
begin
  refine mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors _ hI' j.prop _,
  { rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact hpb },
  { rintros ⟨l, hl⟩ ⟨l', hl'⟩,
    rw ← factors_equiv_is_dvd_iso pb hI,
    simp only [subtype.coe_mk, subtype.coe_eta, rel_iso.coe_fn_to_equiv,
      order_iso.apply_symm_apply],
    all_goals { simp only [rel_iso.coe_fn_to_equiv], exact ((factors_equiv pb hI).symm _).prop } },
end

noncomputable! def normalized_factors_equiv (hI : is_maximal I) (hI' : I.map (algebra_map R S) ≠ ⊥)
  (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0) :
  {J : ideal S | J ∈ normalized_factors (I.map (algebra_map R S)) } ≃
  {J : ideal (polynomial $ R ⧸ I ) | J ∈ normalized_factors
    (ideal.span ({ map I^.quotient.mk (minpoly R pb.gen) } : set (polynomial $ R ⧸ I))) } :=
{ to_fun := λ j, ⟨factors_equiv pb hI ⟨↑j, dvd_of_mem_normalized_factors j.prop⟩,
    mem_normalized_factors_factors_equiv_of_mem_normalized_factors pb hI hI' hpb ↑j j.prop ⟩,
  inv_fun := λ j, ⟨(factors_equiv pb hI).symm ⟨↑j, dvd_of_mem_normalized_factors j.prop⟩,
    factors_equiv_symm_mem pb hI hI' hpb j _⟩,
  left_inv := λ ⟨j, hj⟩, by simp,
  right_inv := λ ⟨j, hj⟩, by simp }

lemma normalized_factors_equiv_multiplicity_eq_multiplicity (hI : is_maximal I)
  (hI' : I.map (algebra_map R S) ≠ ⊥) (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0)
  {J : ideal S} (hJ : J ∈ normalized_factors (I.map (algebra_map R S))) :
  multiplicity J (I.map (algebra_map R S)) = multiplicity
  (normalized_factors_equiv pb hI hI' hpb ⟨J, hJ⟩ : ideal (polynomial $ R ⧸ I))
    (ideal.span ({ map I^.quotient.mk (minpoly R pb.gen) } : set (polynomial $ R ⧸ I))) :=
begin
  simp only [normalized_factors_equiv, subtype.coe_mk, equiv.coe_fn_mk],
  have temp := multiplicity_factor_dvd_iso_eq_multiplicity_of_mem_normalized_factor hI' _  hJ
  (by { rintros ⟨l, hl⟩ ⟨l', hl'⟩,
    rw [subtype.coe_mk, subtype.coe_mk],
    apply factors_equiv_is_dvd_iso pb hI l l' hl hl' }),
  have : (factors_equiv pb hI : {J : ideal S | J ∣ I.map (algebra_map R S) } ≃
    {J : ideal (polynomial $ R ⧸ I ) | J ∣ ideal.span { map I^.quotient.mk (minpoly R pb.gen) }})
    ⟨J, dvd_of_mem_normalized_factors hJ⟩ = factors_equiv pb hI
      ⟨J, dvd_of_mem_normalized_factors hJ⟩ := rfl,
  simp only [this] at temp,
  exact temp.symm,
  { by_contra ; exact hpb (span_singleton_eq_bot.mp h) }
end

open submodule.is_principal multiplicity



/-- The first half of the **Kummer-Dedekind Theorem** in the monogenic case,
  stating that the prime factors of `I*S` are in bijection with those of the minimal poly of
  the generator of `S` over `R`, taken `mod I`-/
noncomputable def normalized_factors_map_equiv_normalized_factors_min_poly_mk (hI : is_maximal I)
  (hI' : I.map (algebra_map R S) ≠ ⊥) (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0) :
 {J : ideal S | J ∈ normalized_factors (I.map (algebra_map R S) )} ≃
    {d : polynomial $ R ⧸ I  | d ∈ normalized_factors (map I^.quotient.mk (minpoly R pb.gen)) } :=
(normalized_factors_equiv pb hI hI' hpb).trans
  (normalized_factors_equiv_span_normalized_factors hpb).symm

/-- The second half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the
    bijection `factors_equiv'` defined in the first half preserves multiplicities. -/
theorem multiplicity_factors_map_eq_multiplicity (hI : is_maximal I)
  (hI' : I.map (algebra_map R S) ≠ ⊥) (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0)
  {J : ideal S}  (hJ : J ∈ normalized_factors (I.map (algebra_map R S))) :
  multiplicity J (I.map (algebra_map R S)) =
    multiplicity ↑(normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb ⟨J, hJ⟩)
    (map I^.quotient.mk (minpoly R pb.gen)) :=
by rw [normalized_factors_map_equiv_normalized_factors_min_poly_mk, equiv.coe_trans,
       function.comp_app,
       multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity,
       normalized_factors_equiv_multiplicity_eq_multiplicity ]

/-- The **Kummer-Dedekind Theorem** -/
theorem normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map
  (hI : is_maximal I) (hI' : I.map (algebra_map R S) ≠ ⊥)
  (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0) :
  normalized_factors (I.map (algebra_map R S)) =
    multiset.map (λ f,
    ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb).symm f : ideal S))
      (normalized_factors (polynomial.map I^.quotient.mk (minpoly R pb.gen))).attach :=
begin
  ext J,
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalized_factors (I.map (algebra_map R S)), swap,
  { rw [multiset.count_eq_zero.mpr hJ, eq_comm, multiset.count_eq_zero, multiset.mem_map],
    simp only [multiset.mem_attach, true_and, not_exists],
    rintros J' rfl,
    exact hJ
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb).symm J').prop },

  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := multiplicity_factors_map_eq_multiplicity pb hI hI' hpb hJ,
  rw [multiplicity_eq_count_normalized_factors, multiplicity_eq_count_normalized_factors,
      unique_factorization_monoid.normalize_normalized_factor _ hJ,
      unique_factorization_monoid.normalize_normalized_factor,
      part_enat.coe_inj]
    at this,
  refine this.trans _,
  -- Get rid of the `map` by applying the equiv to both sides.
  generalize hJ' : (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb)
    ⟨J, hJ⟩ = J',
  have : ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb).symm
    J' : ideal S) = J,
  { rw [← hJ', equiv.symm_apply_apply _ _, subtype.coe_mk] },
  subst this,
  -- Get rid of the `attach` by applying the subtype `coe` to both sides.
  rw [multiset.count_map_eq_count' (λ f,
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb).symm f
        : ideal S)),
      multiset.attach_count_eq_count_coe],
  { exact subtype.coe_injective.comp (equiv.injective _) },
  { exact (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb _).prop },
  { exact irreducible_of_normalized_factor _
    (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb _).prop },
  { assumption },
  { exact irreducible_of_normalized_factor _ hJ },
  { assumption },
end

theorem ideal.irreducible_map_of_irreducible_minpoly (hI : is_maximal I)
  (hI' : I.map (algebra_map R S) ≠ ⊥) (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0)
  (hf : irreducible (map I^.quotient.mk (minpoly R pb.gen))) :
  irreducible (I.map (algebra_map R S)) :=
begin
  have mem_norm_factors: normalize (map I^.quotient.mk (minpoly R pb.gen)) ∈ normalized_factors
    (map I^.quotient.mk (minpoly R pb.gen)) := by simp [normalized_factors_irreducible hf],
  suffices : ∃ x, normalized_factors (I.map (algebra_map R S)) = {x},
  { obtain ⟨x, hx⟩ := this,
    have h := normalized_factors_prod hI',
    rw [associated_iff_eq, hx, multiset.prod_singleton] at h,
    rw ← h,
    exact irreducible_of_normalized_factor x
      (show x ∈ normalized_factors (I.map (algebra_map R S)), by simp [hx]) },
  rw normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map pb hI hI' hpb,
  use ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' hpb).symm
    ⟨normalize (map I^.quotient.mk (minpoly R pb.gen)), mem_norm_factors⟩ : ideal S),
  rw multiset.map_eq_singleton,
  use ⟨normalize (map I^.quotient.mk (minpoly R pb.gen)), mem_norm_factors⟩,
  refine ⟨by {rw normalized_factors_irreducible hf, refl}, rfl⟩,
end

end kummer_dedekind
