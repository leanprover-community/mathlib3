/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import algebraic_geometry.EllipticCurve.valuation

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
every `val_v` is in `ℤ` and we can avoid having to use `with_top (ℤ)`.

## Tags
dedekind domain, fractional ideal, factorization
-/

noncomputable theory
open_locale big_operators classical

open set function

/-! ### Factorization of fractional ideals of Dedekind domains -/

variables {A : Type*} [comm_ring A] (B : submonoid A) (C : Type*) [comm_ring C] [algebra A C]

lemma fractional_ideal.coe_finprod [is_localization B C] {α : Type*} {f : α → ideal A}
  (hB : B ≤ non_zero_divisors A) :
  ((∏ᶠ a : α, f a : ideal A) : fractional_ideal B C) = ∏ᶠ a : α, (f a : fractional_ideal B C)  :=
begin
  have h_coe : ⇑(fractional_ideal.coe_ideal_hom B C).to_monoid_hom = coe := rfl,
  rw [← h_coe, monoid_hom.map_finprod_of_injective
    (fractional_ideal.coe_ideal_hom B C).to_monoid_hom, h_coe],
  exact fractional_ideal.coe_to_fractional_ideal_injective hB,
end

/-- If a prime `p` divides a `finprod`, then it must divide one of its factors. -/
lemma prime.exists_mem_finprod_dvd {α : Type*} {N : Type*} [comm_monoid_with_zero N] {f : α → N}
  {p : N} (hp : prime p) (hf : finite (mul_support f)) :
  p ∣  ∏ᶠ i, f i →  ∃ (a : α), p ∣ f a :=
begin
  rw finprod_eq_prod _ hf,
  intro h,
  obtain ⟨a, -, ha_dvd⟩ := prime.exists_mem_finset_dvd hp h,
  exact ⟨a, ha_dvd⟩,
end

variables {R : Type*} {K : Type*} [comm_ring R] [field K] [algebra R K]

/-- The discrete topology on the units of the fractional ideals. -/
instance ufi_ts : topological_space (units (fractional_ideal (non_zero_divisors R) K)) := ⊥

/-- The units of the fractional ideals with the discrete topology are a topological group.  -/
instance ufi_tg : topological_group (units (fractional_ideal (non_zero_divisors R) K)) :=
{ continuous_mul := continuous_of_discrete_topology,
  continuous_inv := continuous_of_discrete_topology, }

variables [is_fraction_ring R K]

lemma fractional_ideal.coe_ideal_eq_one_iff {I : ideal R} :
  (I : fractional_ideal (non_zero_divisors R) K) = 1 ↔ I = 1 :=
begin
  rw [← fractional_ideal.coe_ideal_top, ideal.one_eq_top],
  exact injective.eq_iff fractional_ideal.coe_ideal_injective,
end

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `J` is nonzero. -/
lemma fractional_ideal.ideal_factor_ne_zero {I : fractional_ideal (non_zero_divisors R) K}
  (hI : I ≠ 0) {a : R} {J : ideal R}
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  J ≠ 0 :=
begin
  intro h,
  rw [h, ideal.zero_eq_bot, fractional_ideal.coe_to_fractional_ideal_bot, mul_zero] at haJ,
  exact hI haJ,
end

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `a` is nonzero. -/
lemma fractional_ideal.constant_factor_ne_zero {I : fractional_ideal (non_zero_divisors R) K}
  (hI : I ≠ 0) {a : R} {J : ideal R}
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  (ideal.span{a} : ideal R) ≠ 0 :=
begin
  intro h,
  rw [ideal.zero_eq_bot, ideal.span_singleton_eq_bot] at h,
  rw [h, ring_hom.map_zero, inv_zero, fractional_ideal.span_singleton_zero, zero_mul] at haJ,
  exact hI haJ,
end

variables [is_domain R] [is_dedekind_domain R] (v : maximal_spectrum R)

/-- Only finitely many maximal ideals of `R` divide a given nonzero ideal. -/
lemma ideal.finite_factors {I : ideal R} (hI : I ≠ 0) :
  finite { v : maximal_spectrum R | v.val.val ∣ I } :=
begin
  haveI h_fin := unique_factorization_monoid.fintype_subtype_dvd I hI,
  let f' : finset (ideal R) := finset.map
    ⟨(λ J : {x // x ∣ I}, J.val), subtype.coe_injective⟩ h_fin.elems,
  have h_eq : { v : maximal_spectrum R | v.val.val ∣ I } =
    { v : maximal_spectrum R | v.val.val ∈ f' },
  { ext v,
    rw [mem_set_of_eq, mem_set_of_eq, finset.mem_map],
    simp_rw exists_prop,
    rw [subtype.exists, embedding.coe_fn_mk],
    simp_rw [exists_and_distrib_right, exists_eq_right],
    split,
    { intro h, use h, exact fintype.complete ⟨v.val.val, h⟩},
    { intro h, obtain ⟨hv, -⟩ := h, exact hv, }},
  rw h_eq,
  have hv : ∀ v : maximal_spectrum R, v.val.val = v.val.val := λ v, rfl,
  have hv_inj : injective (λ (v : maximal_spectrum R), v.val.val),
  { intros v w hvw,
    dsimp only at hvw,
    rw [hv v, hv w] at hvw,
    ext,
    rw [← subtype.val_eq_coe, ← subtype.val_eq_coe, ← subtype.val_eq_coe,
      ← subtype.val_eq_coe, hvw],},
  exact finite.preimage_embedding ⟨(λ v : maximal_spectrum R, v.val.val), hv_inj⟩
    (finite_mem_finset (f')),
end

/-- Only finitely many maximal ideals of `R` divide a given nonzero principal ideal. -/
lemma finite_factors (d : R) (hd : (ideal.span{d} : ideal R) ≠ 0) :
  finite { v : maximal_spectrum R | v.val.val ∣ (ideal.span({d}) : ideal R)} :=
ideal.finite_factors hd

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that the
multiplicity of `v` in the factorization of `I`, denoted `(val_v(I))`, is nonzero. -/
lemma associates.finite_factors (I : ideal R) (hI : I ≠ 0) :
  ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  ((associates.mk v.val.val).count (associates.mk I).factors : ℤ) = 0 :=
begin
  have h_supp : {v : maximal_spectrum R |
    ¬((associates.mk v.val.val).count (associates.mk I).factors : ℤ) = 0} =
    { v : maximal_spectrum R | v.val.val ∣ I },
  { ext v,
    rw mem_set_of_eq, rw mem_set_of_eq,
    rw [int.coe_nat_eq_zero, subtype.val_eq_coe],
    exact associates.count_ne_zero_iff_dvd hI (ideal.irreducible_of_maximal v),},
  rw [filter.eventually_cofinite, h_supp],
  exact ideal.finite_factors hI,
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))` is not the unit ideal. -/
lemma ideal.finite_mul_support {I : ideal R} (hI : I ≠ 0):
  (mul_support (λ (v : maximal_spectrum R),
  v.val.val^(associates.mk v.val.val).count (associates.mk I).factors)).finite :=
begin
  have h_subset : {v : maximal_spectrum R |
    v.val.val^
    (associates.mk v.val.val).count (associates.mk I).factors ≠ 1} ⊆
    {v : maximal_spectrum R |
    ((associates.mk v.val.val).count (associates.mk I).factors : ℤ) ≠ 0},
  { intros v hv,
    rw mem_set_of_eq at hv ⊢,
    intro h_zero,
    rw int.coe_nat_eq_zero at h_zero,
    have hv' : v.val.val^
      (associates.mk v.val.val).count (associates.mk I).factors = 1,
    { rw [h_zero, pow_zero _],},
    exact hv hv', },
  exact finite.subset (filter.eventually_cofinite.mp (associates.finite_factors I hI)) h_subset,
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`. -/
lemma ideal.finite_mul_support_coe {I : ideal R} (hI : I ≠ 0):
  (mul_support (λ (v : maximal_spectrum R),
  (v.val.val : fractional_ideal (non_zero_divisors R) K)^
  ((associates.mk v.val.val).count (associates.mk I).factors : ℤ))).finite :=
begin
  rw mul_support,
  simp_rw [ne.def, zpow_coe_nat, ← fractional_ideal.coe_ideal_pow,
    fractional_ideal.coe_ideal_eq_one_iff],
  exact ideal.finite_mul_support hI,
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
lemma ideal.finite_mul_support_inv {I : ideal R} (hI : I ≠ 0):
  (mul_support (λ (v : maximal_spectrum R),
  (v.val.val : fractional_ideal (non_zero_divisors R) K)^
  -((associates.mk v.val.val).count (associates.mk I).factors : ℤ))).finite :=
begin
  rw mul_support,
  simp_rw [zpow_neg₀, ne.def, inv_eq_one₀],
  exact ideal.finite_mul_support_coe hI,
end

/-- For every nonzero ideal `I` of `v`, `v^(val_v(I) + 1)` does not divide `∏_v v^(val_v(I))`. -/
lemma ideal.finprod_not_dvd (I : ideal R) (hI : I ≠ 0) :
¬ (v.val.val)^
  ((associates.mk v.val.val).count (associates.mk I).factors + 1) ∣
    (∏ᶠ (v : maximal_spectrum R), (v.val.val)^
      (associates.mk v.val.val).count (associates.mk I).factors) :=
begin
  have hf := ideal.finite_mul_support hI,
  have h_ne_zero : v.val.val ^
    (associates.mk v.val.val).count (associates.mk I).factors ≠ 0 := pow_ne_zero _ v.property,
  rw [← mul_finprod_cond_ne v hf, pow_add, pow_one, finprod_cond_ne _ _ hf],
  intro h_contr,
  have hv_prime : prime v.val.val := ideal.prime_of_is_prime v.property v.val.property,
  obtain ⟨w, hw, hvw'⟩ :=
  prime.exists_mem_finset_dvd hv_prime ((mul_dvd_mul_iff_left h_ne_zero).mp h_contr),
  have hw_prime : prime w.val.val := ideal.prime_of_is_prime w.property w.val.property,
  have hvw := prime.dvd_of_dvd_pow hv_prime hvw',
  rw [prime.dvd_prime_iff_associated hv_prime hw_prime, associated_iff_eq, subtype.val_eq_coe,
    subtype.val_eq_coe, subtype.val_eq_coe, subtype.val_eq_coe] at hvw,
  exact (finset.mem_erase.mp hw).1 (eq.symm (subtype.coe_injective(subtype.coe_injective hvw))),
end

lemma associates.finprod_ne_zero (I : ideal R) :
  associates.mk (∏ᶠ (v : maximal_spectrum R), v.val.val ^
    (associates.mk v.val.val).count (associates.mk I).factors) ≠ 0 :=
begin
  rw [associates.mk_ne_zero, finprod_def],
  split_ifs,
  { rw finset.prod_ne_zero_iff,
    intros v hv,
    apply pow_ne_zero _ v.property, },
  { exact one_ne_zero, }
end

/-- The multiplicity of `v` in `∏_v v^(val_v(I))` equals `val_v(I)`. -/
lemma ideal.finprod_count (I : ideal R) (hI : I ≠ 0) :
(associates.mk v.val.val).count (associates.mk (∏ᶠ (v : maximal_spectrum R), (v.val.val)^
    (associates.mk v.val.val).count (associates.mk I).factors)).factors =
    (associates.mk v.val.val).count (associates.mk I).factors :=
begin
  have h_ne_zero := associates.finprod_ne_zero I,
  have hv : irreducible (associates.mk v.val.val) := associates.irreducible_of_maximal v,
  have h_dvd := finprod_mem_dvd _ (ideal.finite_mul_support hI),
  have h_not_dvd := ideal.finprod_not_dvd v I hI,
  rw [← associates.mk_dvd_mk, associates.dvd_eq_le, associates.mk_pow,
    associates.prime_pow_dvd_iff_le h_ne_zero hv] at h_dvd h_not_dvd,
  rw not_le at h_not_dvd,
  apply nat.eq_of_le_of_lt_succ h_dvd h_not_dvd,
end

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`. -/
lemma ideal.factorization (I : ideal R) (hI : I ≠ 0) : ∏ᶠ (v : maximal_spectrum R), (v.val.val)^
  (associates.mk v.val.val).count (associates.mk I).factors = I :=
begin
  rw [← associated_iff_eq, ← associates.mk_eq_mk_iff_associated],
  apply associates.eq_of_eq_counts,
  { apply associates.finprod_ne_zero I },
  { apply associates.mk_ne_zero.mpr hI},
  intros v hv,
  obtain ⟨J, hJv⟩ := associates.exists_rep v,
  rw [← hJv, associates.irreducible_mk] at hv,
  have hJ_ne_zero : J ≠ 0 := irreducible.ne_zero hv,
  rw unique_factorization_monoid.irreducible_iff_prime at hv,
  rw ← hJv,
  apply ideal.finprod_count ⟨⟨J, ideal.is_prime_of_prime hv⟩, hJ_ne_zero⟩ I hI,
end

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarded as fractional
ideals of `R`. -/
lemma ideal.factorization_coe (I : ideal R) (hI : I ≠ 0) :
  ∏ᶠ (v : maximal_spectrum R), (v.val.val : fractional_ideal (non_zero_divisors R) K)^
    ((associates.mk v.val.val).count (associates.mk I).factors : ℤ) = I :=
begin
  conv_rhs{rw ← ideal.factorization I hI},
  rw fractional_ideal.coe_finprod,
  simp_rw [fractional_ideal.coe_ideal_pow, zpow_coe_nat],
  { exact le_refl _ }
end

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`. -/
lemma fractional_ideal.factorization (I : fractional_ideal (non_zero_divisors R) K) (hI : I ≠ 0)
  {a : R} {J : ideal R}
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  ∏ᶠ (v : maximal_spectrum R), (v.val.val : fractional_ideal (non_zero_divisors R) K)^
    ((associates.mk v.val.val).count (associates.mk J).factors -
    (associates.mk v.val.val).count (associates.mk (ideal.span{a})).factors : ℤ) = I :=
begin
  have hJ_ne_zero : J ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI haJ,
  have hJ := ideal.factorization_coe J hJ_ne_zero,
  have ha_ne_zero : ideal.span{a} ≠ 0 := fractional_ideal.constant_factor_ne_zero hI haJ,
  have ha := ideal.factorization_coe (ideal.span{a} : ideal R) ha_ne_zero,
  rw [haJ, ← fractional_ideal.div_span_singleton, fractional_ideal.div_eq_mul_inv,
    ← fractional_ideal.coe_ideal_span_singleton, ← hJ, ← ha, ← finprod_inv_distrib₀],
  simp_rw ← zpow_neg₀,
  rw ← finprod_mul_distrib,
  apply finprod_congr,
  intro v,
  rw [← zpow_add₀ ((@fractional_ideal.coe_ideal_ne_zero_iff R _ K _ _ _ _).mpr v.property),
    sub_eq_add_neg],
  apply ideal.finite_mul_support_coe hJ_ne_zero,
  apply ideal.finite_mul_support_inv ha_ne_zero,
  { apply_instance },
end

/-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`. -/
lemma fractional_ideal.factorization_principal (I : fractional_ideal (non_zero_divisors R) K)
  (hI : I ≠ 0) (k : K) (hk : I = fractional_ideal.span_singleton (non_zero_divisors R) k) :
  ∏ᶠ (v : maximal_spectrum R), (v.val.val : fractional_ideal (non_zero_divisors R) K)^
    ((associates.mk v.val.val).count (associates.mk (ideal.span
    {classical.some (is_localization.mk'_surjective (non_zero_divisors R) k)} : ideal R)).factors -
    (associates.mk v.val.val).count (associates.mk (ideal.span { (classical.some
    (classical.some_spec (is_localization.mk'_surjective (non_zero_divisors R) k)) :
    ↥(non_zero_divisors R))} : ideal R)).factors : ℤ) = I :=
begin
  set n : R := classical.some(is_localization.mk'_surjective (non_zero_divisors R) k) with hn,
  set d : ↥(non_zero_divisors R) := (classical.some (classical.some_spec
    (is_localization.mk'_surjective (non_zero_divisors R) k))) with hd,
  have hd_ne_zero : (algebra_map R K) (d : R) ≠ 0 := map_ne_zero_of_mem_non_zero_divisors
    _ (is_fraction_ring.injective R K) d.property,
  have haJ' : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) d)⁻¹ *
    ↑(ideal.span {n} : ideal R),
  { rw [hk, fractional_ideal.coe_ideal_span_singleton,
      fractional_ideal.span_singleton_mul_span_singleton],
    apply congr_arg,
    rw [eq_inv_mul_iff_mul_eq₀ hd_ne_zero, mul_comm,
      ← is_localization.eq_mk'_iff_mul_eq, eq_comm],
    exact classical.some_spec (classical.some_spec (is_localization.mk'_surjective
      (non_zero_divisors R) k)), },
exact fractional_ideal.factorization I hI haJ',
end

variables (K)

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`,
then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we set `val_v(I) = 0`. -/
def fractional_ideal.count (I : fractional_ideal (non_zero_divisors R) K) : ℤ :=
dite (I = 0) (λ (hI : I = 0), 0) (λ hI : ¬ I = 0,
let a := classical.some (fractional_ideal.exists_eq_span_singleton_mul I) in let
J := classical.some (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))
in ((associates.mk v.val.val).count (associates.mk J).factors -
    (associates.mk v.val.val).count (associates.mk (ideal.span{a})).factors : ℤ))

/-- `val_v(I)` does not depend on the choice of `a` and `J` used to represent `I`. -/
lemma fractional_ideal.count_well_defined  {I : fractional_ideal (non_zero_divisors R) K}
  (hI : I ≠ 0)  {a : R} {J : ideal R}
  (h_aJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  fractional_ideal.count K v I = ((associates.mk v.val.val).count (associates.mk J).factors -
    (associates.mk v.val.val).count (associates.mk (ideal.span{a})).factors : ℤ) :=
begin
  set a₁ := classical.some (fractional_ideal.exists_eq_span_singleton_mul I) with h_a₁,
  set J₁ := classical.some (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))
    with h_J₁,
  have h_a₁J₁ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a₁)⁻¹ *
    ↑J₁ :=
(classical.some_spec (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))).2,
  have h_a₁_ne_zero : a₁ ≠ 0 :=
  (classical.some_spec (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))).1,
  have h_J₁_ne_zero : J₁ ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI h_a₁J₁,
  have h_a_ne_zero : ideal.span{a} ≠ 0 := fractional_ideal.constant_factor_ne_zero hI h_aJ,
  have h_J_ne_zero : J ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI h_aJ,
  have h_a₁' : fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a₁) ≠ 0,
  { rw [ne.def, fractional_ideal.span_singleton_eq_zero_iff, ← (algebra_map R K).map_zero,
      injective.eq_iff (is_localization.injective K (le_refl (non_zero_divisors R)))],
    exact h_a₁_ne_zero,},
  have h_a' : fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a) ≠ 0,
  { rw [ne.def, fractional_ideal.span_singleton_eq_zero_iff, ← (algebra_map R K).map_zero,
      injective.eq_iff (is_localization.injective K (le_refl (non_zero_divisors R)))],
    rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot] at h_a_ne_zero,
    exact h_a_ne_zero,},
  have hv : irreducible (associates.mk v.val.val),
  { rw associates.irreducible_mk,
    exact ideal.irreducible_of_maximal v,},
  rw [h_a₁J₁, ← fractional_ideal.div_span_singleton, ← fractional_ideal.div_span_singleton,
    div_eq_div_iff h_a₁' h_a', ← fractional_ideal.coe_ideal_span_singleton,
    ← fractional_ideal.coe_ideal_span_singleton, ← fractional_ideal.coe_ideal_mul,
    ← fractional_ideal.coe_ideal_mul] at h_aJ,
  rw [fractional_ideal.count, dif_neg hI, sub_eq_sub_iff_add_eq_add, ← int.coe_nat_add,
    ← int.coe_nat_add, int.coe_nat_inj', ← associates.count_mul _ _ hv,
    ← associates.count_mul _ _ hv, associates.mk_mul_mk, associates.mk_mul_mk,
    fractional_ideal.coe_ideal_injective h_aJ],
  { rw [ne.def, associates.mk_eq_zero], exact h_J_ne_zero },
  { rw [ne.def, associates.mk_eq_zero, ideal.zero_eq_bot, ideal.span_singleton_eq_bot],
    exact h_a₁_ne_zero, },
  { rw [ne.def, associates.mk_eq_zero], exact h_J₁_ne_zero },
  { rw [ne.def, associates.mk_eq_zero], exact h_a_ne_zero },
end

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. -/
lemma fractional_ideal.count_mul {I I' : fractional_ideal (non_zero_divisors R) K} (hI : I ≠ 0)
  (hI' : I' ≠ 0) : fractional_ideal.count K v (I*I')  = fractional_ideal.count K v (I) +
  fractional_ideal.count K v (I') :=
begin
  have hv : irreducible (associates.mk v.val.val),
  { apply associates.irreducible_of_maximal },
  obtain ⟨a, J, ha, haJ⟩ := fractional_ideal.exists_eq_span_singleton_mul I,
  have ha_ne_zero : associates.mk (ideal.span {a} : ideal R) ≠ 0,
  { rw [ne.def, associates.mk_eq_zero, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact ha },
  have hJ_ne_zero : associates.mk J ≠ 0,
  { rw [ne.def, associates.mk_eq_zero], exact fractional_ideal.ideal_factor_ne_zero hI haJ },
  obtain ⟨a', J', ha', haJ'⟩ := fractional_ideal.exists_eq_span_singleton_mul I',
  have ha'_ne_zero : associates.mk (ideal.span {a'} : ideal R) ≠ 0,
  { rw [ne.def, associates.mk_eq_zero, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact ha' },
  have hJ'_ne_zero : associates.mk J' ≠ 0,
  { rw [ne.def, associates.mk_eq_zero], exact fractional_ideal.ideal_factor_ne_zero hI' haJ' },
  have h_prod : I*I' = fractional_ideal.span_singleton (non_zero_divisors R)
    ((algebra_map R K) (a*a'))⁻¹ * ↑(J*J'),
    { rw [haJ, haJ', mul_assoc, mul_comm ↑J, mul_assoc, ← mul_assoc,
      fractional_ideal.span_singleton_mul_span_singleton,
      fractional_ideal.coe_ideal_mul, ring_hom.map_mul, mul_inv₀, mul_comm ↑J] },
  rw [fractional_ideal.count_well_defined K v hI haJ,
    fractional_ideal.count_well_defined K v hI' haJ',
    fractional_ideal.count_well_defined K v (mul_ne_zero hI hI') h_prod,
    ← associates.mk_mul_mk, associates.count_mul hJ_ne_zero hJ'_ne_zero hv,
    ← ideal.span_singleton_mul_span_singleton, ← associates.mk_mul_mk,
    associates.count_mul ha_ne_zero ha'_ne_zero hv],
  push_cast,
  ring,
end

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. If `I` or `I'` is zero, then
`val_v(I*I') = 0`. -/
lemma fractional_ideal.count_mul' (I I' : fractional_ideal (non_zero_divisors R) K) :
  fractional_ideal.count K v (I*I')  = (if I ≠ 0 ∧ I' ≠ 0 then  fractional_ideal.count K v (I) +
    fractional_ideal.count K v (I') else 0) :=
begin
  split_ifs,
  { exact fractional_ideal.count_mul K v h.1 h.2 },
  { push_neg at h,
    by_cases hI : I = 0,
    { rw [hI, zero_mul, fractional_ideal.count, dif_pos (eq.refl _)], },
    { rw [(h hI), mul_zero, fractional_ideal.count, dif_pos (eq.refl _)], }}
end

/-- val_v(0) = 0. -/
lemma fractional_ideal.count_zero :
  fractional_ideal.count K v (0 : fractional_ideal (non_zero_divisors R) K) = 0 :=
by rw [fractional_ideal.count, dif_pos (eq.refl _)]

/-- val_v(1) = 0. -/
lemma fractional_ideal.count_one :
  fractional_ideal.count K v (1 : fractional_ideal (non_zero_divisors R) K) = 0 :=
begin
  have h_one : (1 : fractional_ideal (non_zero_divisors R) K) = fractional_ideal.span_singleton
    (non_zero_divisors R) ((algebra_map R K) (1))⁻¹ * ↑(1 : ideal R),
  { rw [(algebra_map R K).map_one, ideal.one_eq_top, fractional_ideal.coe_ideal_top, mul_one,
      inv_one, fractional_ideal.span_singleton_one], },
  rw [fractional_ideal.count_well_defined K v one_ne_zero h_one, ideal.span_singleton_one,
    ideal.one_eq_top, sub_self],
end

/-- For every `n ∈ ℕ` and every ideal `I`, `val_v(I^n) = n*val_v(I)`. -/
lemma fractional_ideal.count_pow (n : ℕ) (I : fractional_ideal (non_zero_divisors R) K) :
  fractional_ideal.count K v (I^n) = n * fractional_ideal.count K v I :=
begin
  induction n with n h,
  { rw [pow_zero, int.coe_nat_zero, zero_mul, fractional_ideal.count_one] },
  { rw pow_succ, rw fractional_ideal.count_mul',
    by_cases hI : I = 0,
    { have h_neg : ¬ (I ≠ 0 ∧ I ^ n ≠ 0),
      { rw [not_and, not_not, ne.def], intro h, exact absurd hI h, },
      rw [if_neg h_neg, hI, fractional_ideal.count_zero, mul_zero], },
    { rw [if_pos (and.intro hI (pow_ne_zero n hI)), h, nat.succ_eq_add_one], ring, }},
end

/--`val_v(v) = 1`, when `v` is regarded as a fractional ideal. -/
lemma fractional_ideal.count_self :
  fractional_ideal.count K v (v.val.val : fractional_ideal (non_zero_divisors R) K)  = 1 :=
begin
  have hv : (v.val.val : fractional_ideal (non_zero_divisors R) K) ≠ 0,
  { rw fractional_ideal.coe_ideal_ne_zero_iff,
    exact v.property  },
  have h_self : (v.val.val : fractional_ideal (non_zero_divisors R) K) =
    fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) 1)⁻¹ *
    ↑(v.val.val),
  { rw [(algebra_map R K).map_one, inv_one, fractional_ideal.span_singleton_one, one_mul], },
  have hv_irred : irreducible (associates.mk v.val.val),
  { apply associates.irreducible_of_maximal v },
  rw [fractional_ideal.count_well_defined K v hv h_self, associates.count_self hv_irred,
    ideal.span_singleton_one, ← ideal.one_eq_top, associates.mk_one, associates.factors_one,
    associates.count_zero hv_irred, int.coe_nat_zero, sub_zero, int.coe_nat_one],
end

/--`val_v(v) = n` for every `n ∈ ℕ`. -/
lemma fractional_ideal.count_pow_self (n : ℕ) :
  fractional_ideal.count K v ((v.val.val : fractional_ideal (non_zero_divisors R) K)^n) = n :=
by rw [fractional_ideal.count_pow, fractional_ideal.count_self, mul_one]

/--`val_v(I⁻ⁿ) = -val_v(Iⁿ)` for every `n ∈ ℤ`. -/
lemma fractional_ideal.count_inv (n : ℤ) (I : fractional_ideal (non_zero_divisors R) K) :
  fractional_ideal.count K v (I^-n) = - fractional_ideal.count K v (I^n) :=
begin
  by_cases hI : I = 0,
  {by_cases hn : n = 0,
    { rw [hn, neg_zero, zpow_zero, fractional_ideal.count_one, neg_zero], },
    { rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), fractional_ideal.count_zero,
        neg_zero], }},
  { rw [eq_neg_iff_add_eq_zero,
    ←  fractional_ideal.count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
    ← zpow_add₀ hI, neg_add_self, zpow_zero],
    exact fractional_ideal.count_one K v, }
end

/--`val_v(Iⁿ) = n*val_v(I)` for every `n ∈ ℤ`. -/
lemma fractional_ideal.count_zpow (n : ℤ) (I : fractional_ideal (non_zero_divisors R) K) :
  fractional_ideal.count K v (I^n) = n * fractional_ideal.count K v I :=
begin
  cases n,
  { rw [int.of_nat_eq_coe, zpow_coe_nat],
    exact fractional_ideal.count_pow K v n I, },
  { rw [int.neg_succ_of_nat_coe, fractional_ideal.count_inv, zpow_coe_nat,
      fractional_ideal.count_pow], ring, }
end

/--`val_v(v) = n` for every `n ∈ ℤ`. -/
lemma fractional_ideal.count_zpow_self (n : ℤ) :
  fractional_ideal.count K v
  ((v.val.val : fractional_ideal (non_zero_divisors R) K)^n) = n :=
by rw [fractional_ideal.count_zpow, fractional_ideal.count_self, mul_one]

/-- If `v ≠ w` are two maximal ideals of `R`, then `val_v(w) = 0`. -/
lemma fractional_ideal.count_maximal_coprime (w : maximal_spectrum R) (hw : w ≠ v) :
  fractional_ideal.count K v (w.val.val : fractional_ideal (non_zero_divisors R) K) = 0 :=
begin
  have hw_fact : (w.val.val : fractional_ideal (non_zero_divisors R) K) =
   fractional_ideal.span_singleton
    (non_zero_divisors R) ((algebra_map R K) (1))⁻¹ * ↑(w.val.val),
  { rw [(algebra_map R K).map_one, inv_one, fractional_ideal.span_singleton_one, one_mul], },
  have hw_ne_zero : (w.val.val : fractional_ideal (non_zero_divisors R) K) ≠ 0,
  { rw fractional_ideal.coe_ideal_ne_zero_iff,
    exact w.property  },
  have hv : irreducible (associates.mk v.val.val) := by apply associates.irreducible_of_maximal v,
  have hw' : irreducible (associates.mk w.val.val) := by apply associates.irreducible_of_maximal w,
  rw [fractional_ideal.count_well_defined K v hw_ne_zero hw_fact, ideal.span_singleton_one,
    ← ideal.one_eq_top, associates.mk_one, associates.factors_one, associates.count_zero hv,
    int.coe_nat_zero, sub_zero, int.coe_nat_eq_zero, ← pow_one (associates.mk w.val.val),
    associates.factors_prime_pow hw', associates.count_some hv, multiset.repeat_one,
    multiset.count_eq_zero, multiset.mem_singleton],
  simp only [subtype.val_eq_coe],
  rw [associates.mk_eq_mk_iff_associated, associated_iff_eq, ← ne.def,
    injective.ne_iff subtype.coe_injective, injective.ne_iff subtype.coe_injective],
  exact ne.symm hw,
end

/-- `val_v(∏_{w ≠ v} w^{exps w}) = 0`. -/
lemma fractional_ideal.count_finprod_coprime (exps : maximal_spectrum R → ℤ) :
  fractional_ideal.count K v (∏ᶠ (w : maximal_spectrum R) (H : w ≠ v), ↑(w.val.val) ^ exps w) = 0 :=
begin
  apply finprod_mem_induction (λ I, fractional_ideal.count K v I = 0),
  { exact fractional_ideal.count_one K v },
  { intros I I' hI hI',
    by_cases h : I ≠ 0 ∧ I' ≠ 0,
    { rw [fractional_ideal.count_mul' K v, if_pos h, hI, hI', add_zero] },
    { rw [fractional_ideal.count_mul' K v, if_neg h], }},
  { intros w hw,
    rw [fractional_ideal.count_zpow, fractional_ideal.count_maximal_coprime K v w hw, mul_zero] }
end

/-- If `exps` is finitely supported, then `val_v(∏_w w^{exps w}) = exps v`. -/
lemma fractional_ideal.count_finprod (exps : maximal_spectrum R → ℤ)
(h_exps : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite, exps v = 0 ) :
fractional_ideal.count K v (∏ᶠ (v : maximal_spectrum R),
  (v.val.val : fractional_ideal (non_zero_divisors R) K)^(exps v)) = exps v :=
begin
  have h_supp : (mul_support (λ (i : maximal_spectrum R), ↑(i.val.val) ^ exps i)).finite,
  { have h_subset : {v : maximal_spectrum R |
      (v.val.val : fractional_ideal (non_zero_divisors R) K) ^ exps v ≠ 1} ⊆
      {v : maximal_spectrum R | exps v ≠ 0},
    { intros v hv,
      by_contradiction h,
      rw [nmem_set_of_eq, not_not] at h,
      rw [mem_set_of_eq, h, zpow_zero] at hv,
      exact hv (eq.refl 1),},
    exact finite.subset h_exps h_subset, },
    rw [← mul_finprod_cond_ne v h_supp, fractional_ideal.count_mul,
      fractional_ideal.count_zpow_self, fractional_ideal.count_finprod_coprime, add_zero],
  { apply zpow_ne_zero,
    exact fractional_ideal.coe_ideal_ne_zero_iff.mpr v.property, },
  { rw [finprod_cond_ne _ _ h_supp, finset.prod_ne_zero_iff],
    intros w hw,
    apply zpow_ne_zero,
    exact fractional_ideal.coe_ideal_ne_zero_iff.mpr w.property, }
end

variable {K}
/-- If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
lemma fractional_ideal.finite_factors {I : fractional_ideal (non_zero_divisors R) K} (hI : I ≠ 0)
  {a : R} {J : ideal R}
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  ∀ᶠ v : maximal_spectrum R in filter.cofinite,
  (((associates.mk v.val.val).count (associates.mk J).factors : ℤ) -
    ((associates.mk v.val.val).count (associates.mk (ideal.span {a})).factors) = 0) :=
begin
  have ha_ne_zero : ideal.span{a} ≠ 0 := fractional_ideal.constant_factor_ne_zero hI haJ,
  have hJ_ne_zero : J ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI haJ,
  rw filter.eventually_cofinite,
  have h_subset : {v : maximal_spectrum R | ¬((associates.mk v.val.val).count
    (associates.mk J).factors : ℤ) -
    ↑((associates.mk v.val.val).count (associates.mk (ideal.span {a})).factors) = 0} ⊆
    {v : maximal_spectrum R | v.val.val ∣ J} ∪
    {v : maximal_spectrum R | v.val.val ∣ (ideal.span {a})},
  { intros v hv,
    have hv_irred : irreducible v.val.val := ideal.irreducible_of_maximal v,
    by_contradiction h_nmem,
    rw [mem_union_eq, mem_set_of_eq, mem_set_of_eq] at h_nmem,
    push_neg at h_nmem,
    rw [← associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred, not_not,
    ← associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred, not_not]
      at h_nmem,
    rw [mem_set_of_eq, h_nmem.1, h_nmem.2, sub_self] at hv,
    exact hv (eq.refl 0),
   },
  exact finite.subset (finite.union
    (ideal.finite_factors (fractional_ideal.ideal_factor_ne_zero hI haJ))
    (ideal.finite_factors (fractional_ideal.constant_factor_ne_zero hI haJ)))
    h_subset,
end

/-! ### Topological groups
These lemmas will be PR'd to `topology/algebra/topological_group`. -/

/-- A homomorphism of topological groups is continuous if and only if it is continuous at 1. -/
@[to_additive "A homomorphism of topological additive groups is continuous if and only if it is
continuous at 0."]
lemma continuous_iff_continuous_at_one {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] [group α] [group β] [topological_group α] [topological_group β] {
  f : α →* β} : continuous f ↔ continuous_at f 1 :=
begin
  rw continuous_iff_continuous_at,
  refine ⟨λ hf, hf 1, λ hf, _⟩,
  intros x  U hUx,
  rw [filter.mem_map, ← map_mul_left_nhds_one, filter.mem_map],
  rw [← map_mul_left_nhds_one, filter.mem_map, ← monoid_hom.map_one f] at hUx,
  convert continuous_at.preimage_mem_nhds hf hUx,
  ext y,
  simp only [mem_preimage, monoid_hom.map_mul],
end

/-- A homomorphism of topological groups is continuous if and only if its kernel is open. -/
@[to_additive continuous_iff_open_add_kernel "A homomorphism of topological additive groups is
continuous if and only if its kernel is open."]
lemma continuous_iff_open_kernel {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [discrete_topology β] [group α] [group β] [topological_group α] [topological_group β]
  {f : α →* β} : continuous f ↔ is_open (f⁻¹' {1}) :=
begin
  refine ⟨λ hf, _, λ hf, _⟩,
  { apply continuous.is_open_preimage hf _ (singletons_open_iff_discrete.mpr (infer_instance) 1) },
  { rw continuous_iff_continuous_at_one,
    intros U hU,
    rw [monoid_hom.map_one, discrete_topology_iff_nhds.mp, filter.mem_pure] at hU,
    rw [filter.mem_map, mem_nhds_iff],
    exact ⟨f ⁻¹' {1}, λ x hx, by apply (singleton_subset_iff.mpr hU) hx, hf,
      by rw [mem_preimage, mem_singleton_iff, monoid_hom.map_one]⟩,
    { apply_instance }}
end
