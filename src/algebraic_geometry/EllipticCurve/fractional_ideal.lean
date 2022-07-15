/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.dedekind_domain.adic_valuation
import topology.algebra.uniform_group

/-!
# Factorization of fractional ideals of Dedekind domains
Every nonzero fractional ideal `I` of a Dedekind domain `R` can be factored as a product
`∏_v v^{n_v}` over the maximal ideals of `R`, where the exponents `n_v` are integers. We define
`fractional_ideal.count K v I` (abbreviated as `val_v(I)` in the documentation) to be `n_v`, and we
prove some of its properties. If `I = 0`, we define `val_v(I) = 0`.

## Main definitions
- `fractional_ideal.count` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of
  `R` such that `I = a⁻¹J`, then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we
  set `val_v(I) = 0`.

## Main results
- `ideal.factorization` : The ideal `I` equals the finprod `∏_v v^(val_v(I))`.
- `fractional_ideal.factorization` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an
ideal of `R` such that `I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`.
- `fractional_ideal.factorization_principal` : For a nonzero `k = r/s ∈ K`, the fractional ideal
`(k)` is equal to the product `∏_v v^(val_v(r) - val_v(s))`.
- `fractional_ideal.finite_factors` : If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many
  maximal ideals of `R`.

## Implementation notes
Since we are only interested in nonzero fractional ideals, we chose to define `val_v(I) = 0` so that
every `val_v` is in `ℤ` and we can avoid having to use `with_top ℤ`.

## Tags
dedekind domain, fractional ideal, factorization
-/

noncomputable theory
open_locale big_operators classical non_zero_divisors

open set function

/-! ### Factorization of fractional ideals of Dedekind domains -/

variables {R : Type*} {K : Type*} [comm_ring R] [field K] [algebra R K] [is_fraction_ring R K]

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `J` is nonzero. -/
lemma fractional_ideal.ideal_factor_ne_zero {I : fractional_ideal R⁰ K}
  (hI : I ≠ 0) {a : R} {J : ideal R}
  (haJ : I = fractional_ideal.span_singleton R⁰ ((algebra_map R K) a)⁻¹ * ↑J) :
  J ≠ 0 :=
begin
  intro h,
  rw [h, ideal.zero_eq_bot, fractional_ideal.coe_to_fractional_ideal_bot, mul_zero] at haJ,
  exact hI haJ
end

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `a` is nonzero. -/
lemma fractional_ideal.constant_factor_ne_zero {I : fractional_ideal R⁰ K}
  (hI : I ≠ 0) {a : R} {J : ideal R}
  (haJ : I = fractional_ideal.span_singleton R⁰ ((algebra_map R K) a)⁻¹ * ↑J) :
  (ideal.span {a} : ideal R) ≠ 0 :=
begin
  intro h,
  rw [ideal.zero_eq_bot, ideal.span_singleton_eq_bot] at h,
  rw [h, ring_hom.map_zero, inv_zero, fractional_ideal.span_singleton_zero, zero_mul] at haJ,
  exact hI haJ
end

open is_dedekind_domain

variables [is_domain R] [is_dedekind_domain R] (v : height_one_spectrum R)

/-- Only finitely many maximal ideals of `R` divide a given nonzero ideal. -/
lemma ideal.finite_factors {I : ideal R} (hI : I ≠ 0) :
  {v : height_one_spectrum R | v.as_ideal ∣ I}.finite :=
begin
  haveI h_fin := unique_factorization_monoid.fintype_subtype_dvd I hI,
  let f' : finset (ideal R) := finset.map
    ⟨(λ J : {x // x ∣ I}, J.val), subtype.coe_injective⟩ h_fin.elems,
  have h_eq : { v : height_one_spectrum R | v.as_ideal ∣ I } =
    { v : height_one_spectrum R | v.as_ideal ∈ f' },
  { ext v,
    rw [mem_set_of_eq, mem_set_of_eq, finset.mem_map],
    simp_rw exists_prop,
    rw [subtype.exists, embedding.coe_fn_mk],
    simp_rw [exists_and_distrib_right, exists_eq_right],
    split,
    { intro h, use h, exact fintype.complete ⟨v.as_ideal, h⟩ },
    { intro h, obtain ⟨hv, -⟩ := h, exact hv } },
  rw h_eq,
  have hv : ∀ v : height_one_spectrum R, v.as_ideal = v.as_ideal := λ v, rfl,
  have hv_inj : injective (λ (v : height_one_spectrum R), v.as_ideal),
  { intros v w hvw,
    dsimp only at hvw,
    rw [hv v, hv w] at hvw,
    ext, rw hvw },
  exact finite.preimage_embedding ⟨(λ v : height_one_spectrum R, v.as_ideal), hv_inj⟩
    (finite_mem_finset f')
end

/-- Only finitely many maximal ideals of `R` divide a given nonzero principal ideal. -/
lemma finite_factors (d : R) (hd : (ideal.span {d} : ideal R) ≠ 0) :
  {v : height_one_spectrum R | v.as_ideal ∣ (ideal.span {d} : ideal R)}.finite :=
ideal.finite_factors hd

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that the
multiplicity of `v` in the factorization of `I`, denoted `(val_v(I))`, is nonzero. -/
lemma associates.finite_factors (I : ideal R) (hI : I ≠ 0) :
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) = 0 :=
begin
  have h_supp : {v : height_one_spectrum R |
    ¬((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) = 0} =
    { v : height_one_spectrum R | v.as_ideal ∣ I },
  { ext v,
    rw [mem_set_of_eq, mem_set_of_eq, int.coe_nat_eq_zero],
    exact associates.count_ne_zero_iff_dvd hI v.irreducible },
  rw [filter.eventually_cofinite, h_supp],
  exact ideal.finite_factors hI
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))` is not the unit ideal. -/
lemma ideal.finite_mul_support {I : ideal R} (hI : I ≠ 0):
  (mul_support (λ (v : height_one_spectrum R),
  v.as_ideal^(associates.mk v.as_ideal).count (associates.mk I).factors)).finite :=
begin
  have h_subset : {v : height_one_spectrum R |
    v.as_ideal^
    (associates.mk v.as_ideal).count (associates.mk I).factors ≠ 1} ⊆
    {v : height_one_spectrum R |
    ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) ≠ 0},
  { intros v hv,
    rw mem_set_of_eq at hv ⊢,
    intro h_zero,
    rw int.coe_nat_eq_zero at h_zero,
    have hv' : v.as_ideal^
      (associates.mk v.as_ideal).count (associates.mk I).factors = 1,
    { rw [h_zero, pow_zero _] },
    exact hv hv' },
  exact finite.subset (filter.eventually_cofinite.mp (associates.finite_factors I hI)) h_subset
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`. -/
lemma ideal.finite_mul_support_coe {I : ideal R} (hI : I ≠ 0):
  (mul_support (λ (v : height_one_spectrum R),
  (v.as_ideal : fractional_ideal R⁰ K)^
  ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ))).finite :=
begin
  rw mul_support,
  simp_rw [ne.def, zpow_coe_nat, ← fractional_ideal.coe_ideal_pow,
    fractional_ideal.coe_ideal_eq_one_iff],
  exact ideal.finite_mul_support hI
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
lemma ideal.finite_mul_support_inv {I : ideal R} (hI : I ≠ 0):
  (mul_support (λ (v : height_one_spectrum R),
  (v.as_ideal : fractional_ideal R⁰ K)^
  -((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ))).finite :=
begin
  rw mul_support,
  simp_rw [zpow_neg, ne.def, inv_eq_one],
  exact ideal.finite_mul_support_coe hI
end

/-- For every nonzero ideal `I` of `v`, `v^(val_v(I) + 1)` does not divide `∏_v v^(val_v(I))`. -/
lemma ideal.finprod_not_dvd (I : ideal R) (hI : I ≠ 0) :
¬ (v.as_ideal)^
  ((associates.mk v.as_ideal).count (associates.mk I).factors + 1) ∣
    (∏ᶠ (v : height_one_spectrum R), (v.as_ideal)^
      (associates.mk v.as_ideal).count (associates.mk I).factors) :=
begin
  have hf := ideal.finite_mul_support hI,
  have h_ne_zero : v.as_ideal ^
    (associates.mk v.as_ideal).count (associates.mk I).factors ≠ 0 := pow_ne_zero _ v.ne_bot,
  rw [← mul_finprod_cond_ne v hf, pow_add, pow_one, finprod_cond_ne _ _ hf],
  intro h_contr,
  have hv_prime : prime v.as_ideal := ideal.prime_of_is_prime v.ne_bot v.is_prime,
  obtain ⟨w, hw, hvw'⟩ :=
  prime.exists_mem_finset_dvd hv_prime ((mul_dvd_mul_iff_left h_ne_zero).mp h_contr),
  have hw_prime : prime w.as_ideal := ideal.prime_of_is_prime w.ne_bot w.is_prime,
  have hvw := prime.dvd_of_dvd_pow hv_prime hvw',
  rw [prime.dvd_prime_iff_associated hv_prime hw_prime, associated_iff_eq] at hvw,
  exact (finset.mem_erase.mp hw).1 (height_one_spectrum.ext w v (eq.symm hvw))
end

lemma associates.finprod_ne_zero (I : ideal R) :
  associates.mk (∏ᶠ (v : height_one_spectrum R), v.as_ideal ^
    (associates.mk v.as_ideal).count (associates.mk I).factors) ≠ 0 :=
begin
  rw [associates.mk_ne_zero, finprod_def],
  split_ifs,
  { rw finset.prod_ne_zero_iff,
    intros v hv,
    apply pow_ne_zero _ v.ne_bot },
  { exact one_ne_zero }
end

/-- The multiplicity of `v` in `∏_v v^(val_v(I))` equals `val_v(I)`. -/
lemma ideal.finprod_count (I : ideal R) (hI : I ≠ 0) :
(associates.mk v.as_ideal).count (associates.mk (∏ᶠ (v : height_one_spectrum R), (v.as_ideal)^
    (associates.mk v.as_ideal).count (associates.mk I).factors)).factors =
    (associates.mk v.as_ideal).count (associates.mk I).factors :=
begin
  have h_ne_zero := associates.finprod_ne_zero I,
  have hv : irreducible (associates.mk v.as_ideal) := v.associates_irreducible,
  have h_dvd := finprod_mem_dvd _ (ideal.finite_mul_support hI),
  have h_not_dvd := ideal.finprod_not_dvd v I hI,
  rw [← associates.mk_dvd_mk, associates.dvd_eq_le, associates.mk_pow,
    associates.prime_pow_dvd_iff_le h_ne_zero hv] at h_dvd h_not_dvd,
  rw not_le at h_not_dvd,
  apply nat.eq_of_le_of_lt_succ h_dvd h_not_dvd
end

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`. -/
lemma ideal.factorization (I : ideal R) (hI : I ≠ 0) : ∏ᶠ (v : height_one_spectrum R), (v.as_ideal)^
  (associates.mk v.as_ideal).count (associates.mk I).factors = I :=
begin
  rw [← associated_iff_eq, ← associates.mk_eq_mk_iff_associated],
  apply associates.eq_of_eq_counts,
  { apply associates.finprod_ne_zero I },
  { apply associates.mk_ne_zero.mpr hI },
  intros v hv,
  obtain ⟨J, hJv⟩ := associates.exists_rep v,
  rw [← hJv, associates.irreducible_mk] at hv,
  have hJ_ne_zero : J ≠ 0 := irreducible.ne_zero hv,
  rw unique_factorization_monoid.irreducible_iff_prime at hv,
  rw ← hJv,
  apply ideal.finprod_count ⟨J, ideal.is_prime_of_prime hv, hJ_ne_zero⟩ I hI
end

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarded as fractional
ideals of `R`. -/
lemma ideal.factorization_coe (I : ideal R) (hI : I ≠ 0) :
  ∏ᶠ (v : height_one_spectrum R), (v.as_ideal : fractional_ideal R⁰ K)^
    ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) = I :=
begin
  conv_rhs {rw ← ideal.factorization I hI },
  rw fractional_ideal.coe_ideal_finprod,
  simp_rw [fractional_ideal.coe_ideal_pow, zpow_coe_nat],
  { exact le_refl _ }
end

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`. -/
lemma fractional_ideal.factorization (I : fractional_ideal R⁰ K) (hI : I ≠ 0)
  {a : R} {J : ideal R}
  (haJ : I = fractional_ideal.span_singleton R⁰ ((algebra_map R K) a)⁻¹ * ↑J) :
  ∏ᶠ (v : height_one_spectrum R), (v.as_ideal : fractional_ideal R⁰ K)^
    ((associates.mk v.as_ideal).count (associates.mk J).factors -
    (associates.mk v.as_ideal).count (associates.mk (ideal.span {a})).factors : ℤ) = I :=
begin
  have hJ_ne_zero : J ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI haJ,
  have hJ := ideal.factorization_coe J hJ_ne_zero,
  have ha_ne_zero : ideal.span {a} ≠ 0 := fractional_ideal.constant_factor_ne_zero hI haJ,
  have ha := ideal.factorization_coe (ideal.span {a} : ideal R) ha_ne_zero,
  rw [haJ, ← fractional_ideal.div_span_singleton, fractional_ideal.div_eq_mul_inv,
    ← fractional_ideal.coe_ideal_span_singleton, ← hJ, ← ha, ← finprod_inv_distrib],
  simp_rw ← zpow_neg,
  rw ← finprod_mul_distrib,
  apply finprod_congr,
  intro v,
  rw [← zpow_add₀ ((@fractional_ideal.coe_ideal_ne_zero_iff R _ K _ _ _ _).mpr v.ne_bot),
    sub_eq_add_neg],
  apply ideal.finite_mul_support_coe hJ_ne_zero,
  apply ideal.finite_mul_support_inv ha_ne_zero,
  { apply_instance }
end

/-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`. -/
lemma fractional_ideal.factorization_principal (I : fractional_ideal R⁰ K)
  (hI : I ≠ 0) (k : K) (hk : I = fractional_ideal.span_singleton R⁰ k) :
  ∏ᶠ v : height_one_spectrum R, (v.as_ideal : fractional_ideal R⁰ K)^
    ((associates.mk v.as_ideal).count (associates.mk (ideal.span
    {classical.some (is_localization.mk'_surjective R⁰ k)} : ideal R)).factors -
    (associates.mk v.as_ideal).count (associates.mk (ideal.span { (classical.some
    (classical.some_spec (is_localization.mk'_surjective R⁰ k)) :
    R⁰)} : ideal R)).factors : ℤ) = I :=
begin
  set n : R := classical.some(is_localization.mk'_surjective R⁰ k) with hn,
  set d : R⁰ := (classical.some (classical.some_spec
    (is_localization.mk'_surjective R⁰ k))) with hd,
  have hd_ne_zero : (algebra_map R K) (d : R) ≠ 0 := map_ne_zero_of_mem_non_zero_divisors
    _ (is_fraction_ring.injective R K) d.property,
  have haJ' : I = fractional_ideal.span_singleton R⁰ ((algebra_map R K) d)⁻¹ *
    ↑(ideal.span {n} : ideal R),
  { rw [hk, fractional_ideal.coe_ideal_span_singleton,
      fractional_ideal.span_singleton_mul_span_singleton],
    apply congr_arg,
    rw [eq_inv_mul_iff_mul_eq₀ hd_ne_zero, mul_comm,
      ← is_localization.eq_mk'_iff_mul_eq, eq_comm],
    exact classical.some_spec (classical.some_spec (is_localization.mk'_surjective
      R⁰ k)) },
  exact fractional_ideal.factorization I hI haJ'
end
