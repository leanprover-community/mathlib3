/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import number_theory.cyclotomic.primitive_roots
import ring_theory.discriminant

/-!
# Discriminant of cyclotomic fields
We compute the discriminant of a `p ^ n`-th cyclotomic extension.

## Main results
* `is_cyclotomic_extension.discr_odd_prime` : if `p` is an odd prime such that
  `is_cyclotomic_extension {p} K L` and `irreducible (cyclotomic p K)`, then
  `discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` for any
  `hζ : is_primitive_root ζ p`.

-/

universes u v

open algebra polynomial nat is_primitive_root power_basis

open_locale polynomial cyclotomic

namespace is_primitive_root

variables {n : ℕ+} {K : Type u} [field K] [char_zero K] {ζ : K}
variables [is_cyclotomic_extension {n} ℚ K]

/-- The discriminant of the power basis given by a primitive root of unity `ζ` is the same as the
discriminant of the power basis given by `ζ - 1`. -/
lemma discr_zeta_eq_discr_zeta_sub_one (hζ : is_primitive_root ζ n) :
  discr ℚ (hζ.power_basis ℚ).basis = discr ℚ (hζ.sub_one_power_basis ℚ).basis :=
begin
  haveI : number_field K := number_field.mk,
  have H₁ : (aeval (hζ.power_basis ℚ).gen) (X - 1 : ℤ[X]) = (hζ.sub_one_power_basis ℚ).gen :=
    by simp,
  have H₂ : (aeval (hζ.sub_one_power_basis ℚ).gen) (X + 1 : ℤ[X]) = (hζ.power_basis ℚ).gen :=
    by simp,
  refine discr_eq_discr_of_to_matrix_coeff_is_integral _
    (λ i j, to_matrix_is_integral H₁ _ _ _ _)
    (λ i j, to_matrix_is_integral H₂ _ _ _ _),
  { exact hζ.is_integral n.pos },
  { refine minpoly.gcd_domain_eq_field_fractions' _ (hζ.is_integral n.pos) },
  { exact is_integral_sub (hζ.is_integral n.pos) is_integral_one },
  { refine minpoly.gcd_domain_eq_field_fractions' _ _,
    exact is_integral_sub (hζ.is_integral n.pos) is_integral_one }
end

end is_primitive_root

namespace is_cyclotomic_extension

variables {p : ℕ+} {k : ℕ} {K : Type u} {L : Type v} {ζ : L} [field K] [field L]
variables [algebra K L]

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.power_basis K` is `(-1) ^ ((p ^ (k + 1).totient) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
lemma discr_prime_pow_ne_two [is_cyclotomic_extension {p ^ (k + 1)} K L] [hp : fact (p : ℕ).prime]
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
  (hk : p ^ (k + 1) ≠ 2) :
  discr K (hζ.power_basis K).basis =
  (-1) ^ (((p ^ (k + 1) : ℕ).totient) / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) :=
begin
  haveI hne := is_cyclotomic_extension.ne_zero' (p ^ (k + 1)) K L,
  have hp2 : p = 2 → 1 ≤ k,
  { intro hp,
    refine one_le_iff_ne_zero.2 (λ h, _),
    rw [h, hp, zero_add, pow_one] at hk,
    exact hk rfl },

  rw [discr_power_basis_eq_norm, finrank _ hirr, hζ.power_basis_gen _,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, pnat.pow_coe, totient_prime_pow hp.out
    (succ_pos k)],
  congr' 1,
  { by_cases hptwo : p = 2,
    { obtain ⟨k₁, hk₁⟩ := nat.exists_eq_succ_of_ne_zero (one_le_iff_ne_zero.1 (hp2 hptwo)),
      rw [hk₁, succ_sub_one, hptwo, pnat.coe_bit0, pnat.one_coe, succ_sub_succ_eq_sub, tsub_zero,
        mul_one, pow_succ, mul_assoc, nat.mul_div_cancel_left _ zero_lt_two,
        nat.mul_div_cancel_left _ zero_lt_two],
      by_cases hk₁zero : k₁ = 0,
      { simp [hk₁zero] },
      obtain ⟨k₂, rfl⟩ := nat.exists_eq_succ_of_ne_zero hk₁zero,
      rw [pow_succ, mul_assoc, pow_mul (-1 : K), pow_mul (-1 : K), neg_one_sq, one_pow, one_pow] },
    { simp only [succ_sub_succ_eq_sub, tsub_zero],
      replace hptwo : ↑p ≠ 2,
      { intro h,
        rw [← pnat.one_coe, ← pnat.coe_bit0, pnat.coe_inj] at h,
        exact hptwo h },
      obtain ⟨a, ha⟩ := even_sub_one_of_prime_ne_two hp.out hptwo,
      rw [mul_comm ((p : ℕ) ^ k), mul_assoc, ha],
      nth_rewrite 0 [← mul_one a],
      nth_rewrite 4 [← mul_one a],
      rw [← nat.mul_succ, mul_comm a, mul_assoc, mul_assoc 2, nat.mul_div_cancel_left _
        zero_lt_two, nat.mul_div_cancel_left _ zero_lt_two, ← mul_assoc, mul_comm
        (a * (p : ℕ) ^ k), pow_mul, ← ha],
      congr' 1,
      refine odd.neg_one_pow (nat.even.sub_odd (nat.succ_le_iff.2 (mul_pos (tsub_pos_iff_lt.2
        hp.out.one_lt) (pow_pos hp.out.pos _))) (even.mul_right (nat.even_sub_one_of_prime_ne_two
        hp.out hptwo) _) odd_one) } },
  { have H := congr_arg derivative (cyclotomic_prime_pow_mul_X_pow_sub_one K p k),
    rw [derivative_mul, derivative_sub, derivative_one, sub_zero, derivative_pow,
      derivative_X, mul_one, derivative_sub, derivative_one, sub_zero, derivative_pow,
      derivative_X, mul_one, ← pnat.pow_coe, hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H,
    replace H := congr_arg (λ P, aeval ζ P) H,
    simp only [aeval_add, aeval_mul, minpoly.aeval, zero_mul, add_zero, aeval_nat_cast,
      _root_.map_sub, aeval_one, aeval_X_pow] at H,
    replace H := congr_arg (algebra.norm K) H,
    have hnorm : (norm K) (ζ ^ (p : ℕ) ^ k - 1) = p ^ ((p : ℕ) ^ k),
    { by_cases hp : p = 2,
      { exact hζ.pow_sub_one_norm_prime_pow_of_one_le hirr rfl.le (hp2 hp) },
      { exact hζ.pow_sub_one_norm_prime_ne_two hirr rfl.le hp } },
    rw [monoid_hom.map_mul, hnorm, monoid_hom.map_mul, ← map_nat_cast (algebra_map K L),
      algebra.norm_algebra_map, finrank _ hirr, pnat.pow_coe, totient_prime_pow hp.out (succ_pos k),
      nat.sub_one, nat.pred_succ, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_pow,
      hζ.norm_eq_one hk hirr, one_pow, mul_one, cast_pow, ← coe_coe, ← pow_mul, ← mul_assoc,
      mul_comm (k + 1), mul_assoc] at H,
    { have := mul_pos (succ_pos k) (tsub_pos_iff_lt.2 hp.out.one_lt),
      rw [← succ_pred_eq_of_pos this, mul_succ, pow_add _ _ ((p : ℕ) ^ k)] at H,
      replace H := (mul_left_inj' (λ h, _)).1 H,
      { simpa only [← pnat.pow_coe, H, mul_comm _ (k + 1)] },
      { replace h := pow_eq_zero h,
        rw [coe_coe] at h,
        simpa using hne.1 } },
    all_goals { apply_instance } },
  all_goals { apply_instance }
end

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.power_basis K` is `(-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
lemma discr_prime_pow_ne_two' [is_cyclotomic_extension {p ^ (k + 1)} K L] [hp : fact (p : ℕ).prime]
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
  (hk : p ^ (k + 1) ≠ 2) :
  discr K (hζ.power_basis K).basis =
  (-1) ^ (((p : ℕ) ^ k  * (p - 1)) / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) :=
by simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow_ne_two hζ hirr hk

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ k} K L`, then the discriminant of
`hζ.power_basis K` is `(-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1))`
if `irreducible (cyclotomic (p ^ k) K))`. Beware that in the cases `p ^ k = 1` and `p ^ k = 2`
the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform result.
See also `is_cyclotomic_extension.discr_prime_pow_eq_unit_mul_pow`. -/
lemma discr_prime_pow [hcycl : is_cyclotomic_extension {p ^ k} K L] [hp : fact (p : ℕ).prime]
  (hζ : is_primitive_root ζ ↑(p ^ k)) (hirr : irreducible (cyclotomic (↑(p ^ k) : ℕ) K)) :
  discr K (hζ.power_basis K).basis =
  (-1) ^ (((p ^ k : ℕ).totient) / 2) * p ^ ((p : ℕ) ^ (k - 1) * ((p - 1) * k - 1)) :=
begin
  unfreezingI { cases k },
  { simp only [coe_basis, pow_zero, power_basis_gen, totient_one, mul_zero, mul_one, show 1 / 2 = 0,
      by refl, discr, trace_matrix],
    have hζone : ζ = 1 := by simpa using hζ,
    rw [hζ.power_basis_dim _, hζone, ← (algebra_map K L).map_one,
      minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebra_map K L).injective, nat_degree_X_sub_C],
    simp only [trace_matrix, map_one, one_pow, matrix.det_unique, trace_form_apply, mul_one],
    rw [← (algebra_map K L).map_one, trace_algebra_map, finrank _ hirr],
    { simp },
    { apply_instance },
    { exact hcycl } },
  { by_cases hk : p ^ (k + 1) = 2,
    { have hp : p = 2,
      { rw [← pnat.coe_inj, pnat.coe_bit0, pnat.one_coe, pnat.pow_coe, ← pow_one 2] at hk,
      replace hk := eq_of_prime_pow_eq (prime_iff.1 hp.out) (prime_iff.1 nat.prime_two)
        (succ_pos _) hk,
      rwa [show 2 = ((2 : ℕ+) : ℕ), by simp, pnat.coe_inj] at hk },
      rw [hp, ← pnat.coe_inj, pnat.pow_coe, pnat.coe_bit0, pnat.one_coe] at hk,
      nth_rewrite 1 [← pow_one 2] at hk,
      replace hk := nat.pow_right_injective rfl.le hk,
      rw [add_left_eq_self] at hk,
      simp only [hp, hk, pow_one, pnat.coe_bit0, pnat.one_coe] at hζ,
      simp only [hp, hk, show 1 / 2 = 0, by refl, coe_basis, pow_one, power_basis_gen,
        pnat.coe_bit0, pnat.one_coe, totient_two, pow_zero, mul_one, mul_zero],
      rw [power_basis_dim, hζ.eq_neg_one_of_two_right, show (-1 : L) = algebra_map K L (-1),
        by simp, minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebra_map K L).injective,
        nat_degree_X_sub_C],
      simp only [discr, trace_matrix, matrix.det_unique, fin.default_eq_zero, fin.coe_zero,
        pow_zero, trace_form_apply, mul_one],
      rw [← (algebra_map K L).map_one, trace_algebra_map, finrank _ hirr, hp, hk],
      { simp },
      { apply_instance },
      { exact hcycl } },
    { exact discr_prime_pow_ne_two hζ hirr hk } }
end

/-- If `p` is a prime and `is_cyclotomic_extension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of `hζ.power_basis K` is `u * p ^ n`. Often this is enough and
less cumbersome to use than `is_cyclotomic_extension.discr_prime_pow`. -/
lemma discr_prime_pow_eq_unit_mul_pow [is_cyclotomic_extension {p ^ k} K L]
  [hp : fact (p : ℕ).prime] (hζ : is_primitive_root ζ ↑(p ^ k))
  (hirr : irreducible (cyclotomic (↑(p ^ k) : ℕ) K)) :
  ∃ (u : ℤˣ) (n : ℕ), discr K (hζ.power_basis K).basis = u * p ^ n :=
begin
  rw [discr_prime_pow hζ hirr],
  by_cases heven : even (((p ^ k : ℕ).totient) / 2),
  { refine ⟨1, (p : ℕ) ^ (k - 1) * ((p - 1) * k - 1), by simp [heven.neg_one_pow]⟩ },
  { exact ⟨-1, (p : ℕ) ^ (k - 1) * ((p - 1) * k - 1),
      by simp [(odd_iff_not_even.2 heven).neg_one_pow]⟩ },
end

/-- If `p` is an odd prime and `is_cyclotomic_extension {p} K L`, then
`discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` if
`irreducible (cyclotomic p K)`. -/
lemma discr_odd_prime [is_cyclotomic_extension {p} K L] [hp : fact (p : ℕ).prime]
  (hζ : is_primitive_root ζ p) (hirr : irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
  discr K (hζ.power_basis K).basis = (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  haveI : is_cyclotomic_extension {p ^ (0 + 1)} K L,
  { rw [zero_add, pow_one],
    apply_instance },
  have hζ' : is_primitive_root ζ ↑(p ^ (0 + 1)) := by simpa using hζ,
  convert discr_prime_pow_ne_two hζ' (by simpa [hirr]) (by simp [hodd]),
  { rw [zero_add, pow_one, totient_prime hp.out] },
  { rw [pow_zero, one_mul, zero_add, mul_one, nat.sub_sub] }
end

end is_cyclotomic_extension
