/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.dedekind_domain.ideal
/-!
# Factorization of ideals of Dedekind domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Every nonzero ideal `I` of a Dedekind domain `R` can be factored as a product `∏_v v^{n_v}` over the
maximal ideals of `R`, where the exponents `n_v` are natural numbers.
TODO: Extend the results in this file to fractional ideals of `R`.
## Main results
- `ideal.finite_factors` : Only finitely many maximal ideals of `R` divide a given nonzero ideal.
- `ideal.finprod_height_one_spectrum_factorization` : The ideal `I` equals the finprod
  `∏_v v^(val_v(I))`,where `val_v(I)` denotes the multiplicity of `v` in the factorization of `I`
  and `v` runs over the maximal ideals of `R`.
## Tags
dedekind domain, ideal, factorization
-/

noncomputable theory
open_locale big_operators classical non_zero_divisors

open set function unique_factorization_monoid is_dedekind_domain
  is_dedekind_domain.height_one_spectrum

/-! ### Factorization of ideals of Dedekind domains -/

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type*} [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

/-- Given a maximal ideal `v` and an ideal `I` of `R`, `max_pow_dividing` returns the maximal
  power of `v` dividing `I`. -/
def is_dedekind_domain.height_one_spectrum.max_pow_dividing (I : ideal R) : ideal R :=
v.as_ideal^(associates.mk v.as_ideal).count (associates.mk I).factors

/-- Only finitely many maximal ideals of `R` divide a given nonzero ideal. -/
lemma ideal.finite_factors {I : ideal R} (hI : I ≠ 0) :
  {v : height_one_spectrum R | v.as_ideal ∣ I}.finite :=
begin
  rw [← set.finite_coe_iff, set.coe_set_of],
  haveI h_fin := fintype_subtype_dvd I hI,
  refine finite.of_injective (λ v, (⟨(v : height_one_spectrum R).as_ideal, v.2⟩ : {x // x ∣ I})) _,
  intros v w hvw,
  simp only at hvw,
  exact subtype.coe_injective ((height_one_spectrum.ext_iff ↑v ↑w).mpr hvw)
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that the
  multiplicity of `v` in the factorization of `I`, denoted `val_v(I)`, is nonzero. -/
lemma associates.finite_factors {I : ideal R} (hI : I ≠ 0) :
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
    ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) = 0 :=
begin
  have h_supp : {v : height_one_spectrum R |
    ¬((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) = 0} =
    {v : height_one_spectrum R | v.as_ideal ∣ I},
  { ext v,
    simp_rw int.coe_nat_eq_zero,
    exact associates.count_ne_zero_iff_dvd hI v.irreducible, },
  rw [filter.eventually_cofinite, h_supp],
  exact ideal.finite_factors hI,
end

namespace ideal

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
  `v^(val_v(I))` is not the unit ideal. -/
lemma finite_mul_support {I : ideal R} (hI : I ≠ 0) :
  (mul_support (λ (v : height_one_spectrum R), v.max_pow_dividing I)).finite :=
begin
  have h_subset : {v : height_one_spectrum R | v.max_pow_dividing I ≠ 1} ⊆
    {v : height_one_spectrum R |
      ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) ≠ 0},
  { intros v hv h_zero,
    have hv' : v.max_pow_dividing I = 1,
    { rw [is_dedekind_domain.height_one_spectrum.max_pow_dividing, int.coe_nat_eq_zero.mp h_zero,
        pow_zero _] },
    exact hv hv', },
  exact finite.subset (filter.eventually_cofinite.mp (associates.finite_factors hI)) h_subset,
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`. -/
lemma finite_mul_support_coe {I : ideal R} (hI : I ≠ 0) :
  (mul_support (λ (v : height_one_spectrum R),
    (v.as_ideal : fractional_ideal R⁰ K) ^
      ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ))).finite :=
begin
  rw mul_support,
  simp_rw [ne.def, zpow_coe_nat, ← fractional_ideal.coe_ideal_pow,
    fractional_ideal.coe_ideal_eq_one],
  exact finite_mul_support hI,
end

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
lemma finite_mul_support_inv {I : ideal R} (hI : I ≠ 0) :
  (mul_support (λ (v : height_one_spectrum R),
    (v.as_ideal : fractional_ideal R⁰ K) ^
      -((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ))).finite :=
begin
  rw mul_support,
  simp_rw [zpow_neg, ne.def, inv_eq_one],
  exact finite_mul_support_coe hI,
end

/-- For every nonzero ideal `I` of `v`, `v^(val_v(I) + 1)` does not divide `∏_v v^(val_v(I))`. -/
lemma finprod_not_dvd (I : ideal R) (hI : I ≠ 0) :
  ¬ (v.as_ideal) ^ ((associates.mk v.as_ideal).count (associates.mk I).factors + 1) ∣
      (∏ᶠ (v : height_one_spectrum R), v.max_pow_dividing I) :=
begin
  have hf := finite_mul_support hI,
  have h_ne_zero : v.max_pow_dividing I ≠ 0 := pow_ne_zero _ v.ne_bot,
  rw [← mul_finprod_cond_ne v hf, pow_add, pow_one, finprod_cond_ne _ _ hf],
  intro h_contr,
  have hv_prime : prime v.as_ideal := ideal.prime_of_is_prime v.ne_bot v.is_prime,
  obtain ⟨w, hw, hvw'⟩ :=
    prime.exists_mem_finset_dvd hv_prime ((mul_dvd_mul_iff_left h_ne_zero).mp h_contr),
  have hw_prime : prime w.as_ideal := ideal.prime_of_is_prime w.ne_bot w.is_prime,
  have hvw := prime.dvd_of_dvd_pow hv_prime hvw',
  rw [prime.dvd_prime_iff_associated hv_prime hw_prime, associated_iff_eq] at hvw,
  exact (finset.mem_erase.mp hw).1 (height_one_spectrum.ext w v (eq.symm hvw)),
end

end ideal

lemma associates.finprod_ne_zero (I : ideal R) :
  associates.mk (∏ᶠ (v : height_one_spectrum R), v.max_pow_dividing I) ≠ 0 :=
begin
  rw [associates.mk_ne_zero, finprod_def],
  split_ifs,
  { rw finset.prod_ne_zero_iff,
    intros v hv,
    apply pow_ne_zero _ v.ne_bot, },
  { exact one_ne_zero, }
end

namespace ideal

/-- The multiplicity of `v` in `∏_v v^(val_v(I))` equals `val_v(I)`. -/
lemma finprod_count (I : ideal R) (hI : I ≠ 0) : (associates.mk v.as_ideal).count
  (associates.mk (∏ᶠ (v : height_one_spectrum R), v.max_pow_dividing I)).factors =
  (associates.mk v.as_ideal).count (associates.mk I).factors :=
begin
  have h_ne_zero := associates.finprod_ne_zero I,
  have hv : irreducible (associates.mk v.as_ideal) := v.associates_irreducible,
  have h_dvd := finprod_mem_dvd v (ideal.finite_mul_support hI),
  have h_not_dvd := ideal.finprod_not_dvd v I hI,
  simp only [is_dedekind_domain.height_one_spectrum.max_pow_dividing] at h_dvd h_ne_zero h_not_dvd,
  rw [← associates.mk_dvd_mk, associates.dvd_eq_le, associates.mk_pow,
    associates.prime_pow_dvd_iff_le h_ne_zero hv] at h_dvd h_not_dvd,
  rw not_le at h_not_dvd,
  apply nat.eq_of_le_of_lt_succ h_dvd h_not_dvd,
end

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`. -/
lemma finprod_height_one_spectrum_factorization (I : ideal R) (hI : I ≠ 0) :
  ∏ᶠ (v : height_one_spectrum R), v.max_pow_dividing I = I :=
begin
  rw [← associated_iff_eq, ← associates.mk_eq_mk_iff_associated],
  apply associates.eq_of_eq_counts,
  { apply associates.finprod_ne_zero I },
  { apply associates.mk_ne_zero.mpr hI },
  intros v hv,
  obtain ⟨J, hJv⟩ := associates.exists_rep v,
  rw [← hJv, associates.irreducible_mk] at hv,
  rw ← hJv,
  apply ideal.finprod_count ⟨J, ideal.is_prime_of_prime (irreducible_iff_prime.mp hv),
    irreducible.ne_zero hv⟩ I hI,
end

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarded as fractional
ideals of `R`. -/
lemma finprod_height_one_spectrum_factorization_coe (I : ideal R) (hI : I ≠ 0) :
  ∏ᶠ (v : height_one_spectrum R), (v.as_ideal : fractional_ideal R⁰ K) ^
    ((associates.mk v.as_ideal).count (associates.mk I).factors : ℤ) = I :=
begin
  conv_rhs { rw ← ideal.finprod_height_one_spectrum_factorization I hI },
  rw fractional_ideal.coe_ideal_finprod R⁰ K (le_refl _),
  simp_rw [is_dedekind_domain.height_one_spectrum.max_pow_dividing, fractional_ideal.coe_ideal_pow,
    zpow_coe_nat],
end

end ideal
