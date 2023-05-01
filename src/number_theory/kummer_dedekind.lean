/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/

import ring_theory.algebra_tower
import ring_theory.dedekind_domain.ideal
import ring_theory.is_adjoin_root

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

 * Prove the Kummer-Dedekind theorem in full generality.

 * Prove the converse of `ideal.irreducible_map_of_irreducible_minpoly`.

 * Prove that `normalized_factors_map_equiv_normalized_factors_min_poly_mk` can be expressed as
    `normalized_factors_map_equiv_normalized_factors_min_poly_mk g = ⟨I, G(α)⟩` for `g` a prime
    factor of `f mod I` and `G` a lift of `g` to `R[X]`.

## References

 * [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

variables (R : Type*) {S : Type*} [comm_ring R] [comm_ring S] [algebra R S]

open ideal polynomial double_quot unique_factorization_monoid algebra ring_hom

local notation R`<`:std.prec.max_plus x `>` := adjoin R ({x} : set S)

/-- Let `S / R` be a ring extension and `x : S`, then the conductor of `R<x>` is the
    biggest ideal of `S` contained in `R<x>`. -/
def conductor (x : S) : ideal S :=
{ carrier := {a | ∀ (b : S), a * b ∈ R<x> },
  zero_mem' := λ b, by simpa only [zero_mul] using subalgebra.zero_mem _,
  add_mem' := λ a b ha hb c, by simpa only [add_mul] using subalgebra.add_mem _ (ha c) (hb c),
  smul_mem' := λ c a ha b, by simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * b) }

variables {R} {x : S}

lemma conductor_eq_of_eq {y : S} (h : (R<x> : set S) = R<y>):
  conductor R x = conductor R y :=
ideal.ext $ λ a, forall_congr $ λ b, set.ext_iff.mp h _

lemma conductor_subset_adjoin : (conductor R x : set S) ⊆ R<x> :=
λ y hy, by simpa only [mul_one] using hy 1

lemma mem_conductor_iff {y : S} : y ∈ conductor R x ↔ ∀ (b : S), y * b ∈ R<x> :=
⟨λ h, h, λ h, h⟩

lemma conductor_eq_top_of_adjoin_eq_top (h : R<x> = ⊤) : conductor R x = ⊤ :=
by simp only [ideal.eq_top_iff_one, mem_conductor_iff, h, mem_top, forall_const]

lemma conductor_eq_top_of_power_basis (pb : power_basis R S) : conductor R pb.gen = ⊤ :=
conductor_eq_top_of_adjoin_eq_top pb.adjoin_gen_eq_top

variables {I : ideal R}

/-- This technical lemma tell us that if `C` is the conductor of `R<x>` and `I` is an ideal of `R`
  then `p * (I * S) ⊆ I * R<x>` for any `p` in `C ∩ R` -/
lemma prod_mem_ideal_map_of_mem_conductor {p : R} {z : S}
  (hp : p ∈ ideal.comap (algebra_map R S) (conductor R x)) (hz' : z ∈ (I.map (algebra_map R S))) :
  (algebra_map R S p) * z ∈
    algebra_map R<x> S '' ↑(I.map (algebra_map R R<x>)) :=
begin
  rw [ideal.map, ideal.span, finsupp.mem_span_image_iff_total] at hz',
  obtain ⟨l, H, H'⟩ := hz',
  rw finsupp.total_apply at H',
  rw [← H', mul_comm, finsupp.sum_mul],
  have lem : ∀ {a : R}, a ∈ I → (l a • (algebra_map R S a) * (algebra_map R S p)) ∈
    (algebra_map R<x> S) '' (I.map (algebra_map R R<x>)),
  { intros a ha,
    rw [algebra.id.smul_eq_mul, mul_assoc, mul_comm, mul_assoc, set.mem_image],
    refine exists.intro (algebra_map R R<x> a * ⟨l a * algebra_map R S p,
      show l a * algebra_map R S p ∈ R<x>, from _ ⟩) _,
    { rw mul_comm,
      exact mem_conductor_iff.mp (ideal.mem_comap.mp hp) _ },
    refine ⟨_, by simpa only [ring_hom.map_mul, mul_comm (algebra_map R S p) (l a)]⟩,
    rw mul_comm,
    apply ideal.mul_mem_left (I.map (algebra_map R R<x>)) _
      (ideal.mem_map_of_mem _ ha) },
  refine finset.sum_induction _ (λ u, u ∈ (algebra_map R<x> S) ''
    (I.map (algebra_map R R<x>)))
    (λ a b, _) _ _,
  rintro ⟨z, hz, rfl⟩ ⟨y, hy, rfl⟩,
  rw [← ring_hom.map_add],
  exact ⟨z + y, ideal.add_mem _ (set_like.mem_coe.mp hz) hy, rfl⟩,
  { refine ⟨0, set_like.mem_coe.mpr $ ideal.zero_mem _, ring_hom.map_zero _⟩ },
  { intros y hy,
    exact lem ((finsupp.mem_supported _ l).mp H hy) },
end

/-- A technical result telling us that `(I * S) ∩ R<x> = I * R<x>` for any ideal `I` of `R`. -/
lemma comap_map_eq_map_adjoin_of_coprime_conductor
  (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (h_alg : function.injective (algebra_map R<x> S)):
  (I.map (algebra_map R S)).comap (algebra_map R<x> S) = I.map (algebra_map R R<x>) :=
begin
  apply le_antisymm,
  { -- This is adapted from [Neukirch1992]. Let `C = (conductor R x)`. The idea of the proof
    -- is that since `I` and `C ∩ R` are coprime, we have
    -- `(I * S) ∩ R<x> ⊆ (I + C) * ((I * S) ∩ R<x>) ⊆ I * R<x> + I * C * S ⊆ I * R<x>`.
    intros y hy,
    obtain ⟨z, hz⟩ := y,
    obtain ⟨p, hp, q, hq, hpq⟩ := submodule.mem_sup.mp ((ideal.eq_top_iff_one _).mp hx),
    have temp : (algebra_map R S p)*z + (algebra_map R S q)*z = z,
    { simp only [←add_mul, ←ring_hom.map_add (algebra_map R S), hpq, map_one, one_mul] },
    suffices : z ∈ algebra_map R<x> S '' (I.map (algebra_map R R<x>)) ↔ (⟨z, hz⟩ : R<x>) ∈
      I.map (algebra_map R R<x>),
    { rw [← this, ← temp],
      obtain ⟨a, ha⟩ := (set.mem_image _ _ _).mp (prod_mem_ideal_map_of_mem_conductor hp
        (show z ∈ I.map (algebra_map R S), by rwa ideal.mem_comap at hy )),
      use a + (algebra_map R R<x> q) * ⟨z, hz⟩,
      refine ⟨ ideal.add_mem (I.map (algebra_map R R<x>)) ha.left _,
        by simpa only [ha.right, map_add, alg_hom.map_mul, add_right_inj] ⟩,
      rw mul_comm,
        exact ideal.mul_mem_left (I.map (algebra_map R R<x>)) _ (ideal.mem_map_of_mem _ hq) },
    refine ⟨ λ h, _, λ h, (set.mem_image _ _ _).mpr (exists.intro ⟨z, hz⟩ ⟨by simp [h], rfl⟩ ) ⟩,
    { obtain ⟨x₁, hx₁, hx₂⟩ := (set.mem_image _ _ _).mp h,
      have : x₁ = ⟨z, hz⟩,
      { apply h_alg,
        simpa [hx₂], },
      rwa ← this }  },

  { -- The converse inclusion is trivial
    have : algebra_map R S = (algebra_map _ S).comp (algebra_map R R<x>) := by { ext, refl },
    rw [this, ← ideal.map_map],
    apply ideal.le_comap_map }
end

/-- The canonical morphism of rings from `R<x> ⧸ (I*R<x>)` to `S ⧸ (I*S)` is an isomorphism
    when `I` and `(conductor R x) ∩ R` are coprime. -/
noncomputable def quot_adjoin_equiv_quot_map (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (h_alg : function.injective (algebra_map R<x> S)) :
  R<x> ⧸ (I.map (algebra_map R R<x>)) ≃+* S ⧸ (I.map (algebra_map R S)) :=
ring_equiv.of_bijective (ideal.quotient.lift (I.map (algebra_map R R<x>))
  (((I.map (algebra_map R S))^.quotient.mk).comp (algebra_map R<x> S )) (λ r hr,
    begin
      have : algebra_map R S = (algebra_map R<x> S).comp
        (algebra_map R R<x>) := by { ext, refl },
      rw [ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem, this, ← ideal.map_map],
      exact ideal.mem_map_of_mem _ hr
    end))
begin
  split,
  { --the kernel of the map is clearly `(I * S) ∩ R<x>`. To get injectivity, we need to show that
    --this is contained in `I * R<x>`, which is the content of the previous lemma.
    refine ring_hom.lift_injective_of_ker_le_ideal _ _ (λ u hu, _),
    rwa [ring_hom.mem_ker, ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem,
      ← ideal.mem_comap, comap_map_eq_map_adjoin_of_coprime_conductor hx h_alg] at hu },
  { -- Surjectivity follows from the surjectivity of the canonical map `R<x> → S ⧸ (I * S)`,
    -- which in turn follows from the fact that `I * S + (conductor R x) = S`.
    refine ideal.quotient.lift_surjective_of_surjective _ _ (λ y, _),
    obtain ⟨z, hz⟩ := ideal.quotient.mk_surjective y,
    have : z ∈ conductor R x ⊔ (I.map (algebra_map R S)),
    { suffices : conductor R x ⊔ (I.map (algebra_map R S)) = ⊤,
      { simp only [this] },
      rw ideal.eq_top_iff_one at hx ⊢,
      replace hx := ideal.mem_map_of_mem (algebra_map R S) hx,
      rw [ideal.map_sup, ring_hom.map_one] at hx,
      exact (sup_le_sup (show  ((conductor R x).comap (algebra_map R S)).map (algebra_map R S) ≤
        conductor R x, from ideal.map_comap_le) (le_refl (I.map (algebra_map R S)))) hx },
    rw [← ideal.mem_quotient_iff_mem_sup, hz, ideal.mem_map_iff_of_surjective] at this,
    obtain ⟨u, hu, hu'⟩ := this,
    use ⟨u, conductor_subset_adjoin hu⟩,
    simpa only [← hu'],
    { exact ideal.quotient.mk_surjective } }
end

@[simp]
lemma quot_adjoin_equiv_quot_map_apply_mk (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (h_alg : function.injective (algebra_map R<x> S)) (a : R<x>) :
   quot_adjoin_equiv_quot_map hx h_alg ((I.map (algebra_map R R<x>))^.quotient.mk a)
   = (I.map (algebra_map R S))^.quotient.mk ↑a :=
rfl

namespace kummer_dedekind

open_locale big_operators polynomial classical

variables [is_domain R] [is_integrally_closed R]
variables [is_domain S] [is_dedekind_domain S]
variable [no_zero_smul_divisors R S]

local attribute [instance] ideal.quotient.field

/-- The first half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the prime
    factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
    over `R`, taken `mod I`.-/
noncomputable def normalized_factors_map_equiv_normalized_factors_min_poly_mk (hI : is_maximal I)
  (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (hx' : is_integral R x) :
  {J : ideal S | J ∈ normalized_factors (I.map (algebra_map R S) )} ≃
    {d : (R ⧸ I)[X] | d ∈ normalized_factors (map I^.quotient.mk (minpoly R x))} :=
(normalized_factors_equiv_of_quot_equiv
  ((quot_adjoin_equiv_quot_map hx
    (by { apply no_zero_smul_divisors.algebra_map_injective (algebra.adjoin R {x}) S,
          exact subalgebra.no_zero_smul_divisors_top (algebra.adjoin R {x}) })).symm.trans
  (((algebra.adjoin.power_basis' hx').quotient_equiv_quotient_minpoly_map I).to_ring_equiv.trans
    (quot_equiv_of_eq (show (ideal.span ({(minpoly R (algebra.adjoin.power_basis' hx').gen).map
    I^.quotient.mk})) = (ideal.span ({(minpoly R x).map I^.quotient.mk})),
      by rw algebra.adjoin.power_basis'_minpoly_gen hx'))))
  --show that `I * S` ≠ ⊥
  (show I.map (algebra_map R S) ≠ ⊥,
    by rwa [ne.def, map_eq_bot_iff_of_injective (no_zero_smul_divisors.algebra_map_injective R S),
         ← ne.def])
  --show that the ideal spanned by `(minpoly R pb.gen) mod I` is non-zero
  (by {by_contra, exact (show (map I^.quotient.mk (minpoly R x) ≠ 0), from
    polynomial.map_monic_ne_zero (minpoly.monic hx')) (span_singleton_eq_bot.mp h) } )).trans
  (normalized_factors_equiv_span_normalized_factors
    (show (map I^.quotient.mk (minpoly R x)) ≠ 0, from
      polynomial.map_monic_ne_zero (minpoly.monic hx'))).symm

/-- The second half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the
    bijection `factors_equiv'` defined in the first half preserves multiplicities. -/
theorem multiplicity_factors_map_eq_multiplicity (hI : is_maximal I) (hI' : I ≠ ⊥)
  (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤) (hx' : is_integral R x)
  {J : ideal S} (hJ : J ∈ normalized_factors (I.map (algebra_map R S))) :
  multiplicity J (I.map (algebra_map R S)) =
    multiplicity ↑(normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx'
      ⟨J, hJ⟩) (map I^.quotient.mk (minpoly R x)) :=
by rw [normalized_factors_map_equiv_normalized_factors_min_poly_mk, equiv.coe_trans,
       function.comp_app,
       multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity,
       normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity]

/-- The **Kummer-Dedekind Theorem**. -/
theorem normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map (hI : is_maximal I)
  (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (hx' : is_integral R x) :
  normalized_factors (I.map (algebra_map R S)) =
    multiset.map
      (λ f, ((normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx').symm f :
        ideal S))
      (normalized_factors (polynomial.map I^.quotient.mk (minpoly R x))).attach :=
begin
  ext J,
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalized_factors (I.map (algebra_map R S)), swap,
  { rw [multiset.count_eq_zero.mpr hJ, eq_comm, multiset.count_eq_zero, multiset.mem_map],
    simp only [multiset.mem_attach, true_and, not_exists],
    rintros J' rfl,
    exact hJ
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx').symm J').prop },

  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := multiplicity_factors_map_eq_multiplicity hI hI' hx hx' hJ,
  rw [multiplicity_eq_count_normalized_factors, multiplicity_eq_count_normalized_factors,
      unique_factorization_monoid.normalize_normalized_factor _ hJ,
      unique_factorization_monoid.normalize_normalized_factor,
      part_enat.coe_inj]
    at this,
  refine this.trans _,
  -- Get rid of the `map` by applying the equiv to both sides.
  generalize hJ' : (normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx')
    ⟨J, hJ⟩ = J',
  have : ((normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx').symm J' :
    ideal S) = J,
  { rw [← hJ', equiv.symm_apply_apply _ _, subtype.coe_mk] },
  subst this,
  -- Get rid of the `attach` by applying the subtype `coe` to both sides.
  rw [multiset.count_map_eq_count' (λ f,
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx').symm f
        : ideal S)),
      multiset.attach_count_eq_count_coe],
  { exact subtype.coe_injective.comp (equiv.injective _) },
  { exact (normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx' _).prop},
  { exact irreducible_of_normalized_factor _
    (normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx' _).prop },
  { exact polynomial.map_monic_ne_zero (minpoly.monic hx') },
  { exact irreducible_of_normalized_factor _ hJ },
  { rwa [← bot_eq_zero, ne.def, map_eq_bot_iff_of_injective
    (no_zero_smul_divisors.algebra_map_injective R S)] },
end

theorem ideal.irreducible_map_of_irreducible_minpoly (hI : is_maximal I) (hI' : I ≠ ⊥)
  (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (hx' : is_integral R x) (hf : irreducible (map I^.quotient.mk (minpoly R x))) :
  irreducible (I.map (algebra_map R S)) :=
begin
  have mem_norm_factors : normalize (map I^.quotient.mk (minpoly R x)) ∈ normalized_factors
    (map I^.quotient.mk (minpoly R x)) := by simp [normalized_factors_irreducible hf],
  suffices : ∃ y, normalized_factors (I.map (algebra_map R S)) = {y},
  { obtain ⟨y, hy⟩ := this,
    have h := normalized_factors_prod (show I.map (algebra_map R S) ≠ 0, by rwa [← bot_eq_zero,
      ne.def, map_eq_bot_iff_of_injective (no_zero_smul_divisors.algebra_map_injective R S)]),
    rw [associated_iff_eq, hy, multiset.prod_singleton] at h,
    rw ← h,
    exact irreducible_of_normalized_factor y
      (show y ∈ normalized_factors (I.map (algebra_map R S)), by simp [hy]) },
  rw normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map hI hI' hx hx',
  use ((normalized_factors_map_equiv_normalized_factors_min_poly_mk hI hI' hx hx').symm
    ⟨normalize (map I^.quotient.mk (minpoly R x)), mem_norm_factors⟩ : ideal S),
  rw multiset.map_eq_singleton,
  use ⟨normalize (map I^.quotient.mk (minpoly R x)), mem_norm_factors⟩,
  refine ⟨_, rfl⟩,
  apply multiset.map_injective subtype.coe_injective,
  rw [multiset.attach_map_coe, multiset.map_singleton, subtype.coe_mk],
  exact normalized_factors_irreducible hf
end

end kummer_dedekind
