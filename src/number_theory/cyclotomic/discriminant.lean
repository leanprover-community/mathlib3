/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import number_theory.cyclotomic.primitive_roots
import ring_theory.discriminant

/-!
# Discriminant of cyclotomic fields
We compute the discriminant of a `p`-th cyclotomic extension.

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
  have H₁ : (aeval (hζ.power_basis ℚ).gen) (X - 1 : ℤ[X]) = (hζ.sub_one_power_basis ℚ).gen :=
    by simp,
  have H₂ : (aeval (hζ.sub_one_power_basis ℚ).gen) (X + 1 : ℤ[X]) = (hζ.power_basis ℚ).gen :=
    by simp,
  refine discr_eq_discr_of_to_matrix_coeff_is_integral _
    (λ i j, to_matrix_is_integral H₁ _  _ _ _)
    (λ i j, to_matrix_is_integral H₂ _  _ _ _),
  { exact hζ.is_integral n.pos },
  { refine minpoly.gcd_domain_eq_field_fractions _ (hζ.is_integral n.pos) },
  { exact is_integral_sub (hζ.is_integral n.pos) is_integral_one },
  { refine minpoly.gcd_domain_eq_field_fractions _ _,
    exact is_integral_sub (hζ.is_integral n.pos) is_integral_one }
end

end is_primitive_root

namespace is_cyclotomic_extension

variables {p : ℕ+} (k : ℕ) {K : Type u} {L : Type v} {ζ : L} [field K] [field L]
variables [algebra K L] [ne_zero ((p : ℕ) : K)]

/-- If `p` is an odd prime and `is_cyclotomic_extension {p} K L`, then
`discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)`. -/
lemma discr_odd_prime [is_cyclotomic_extension {p} K L] [hp : fact (p : ℕ).prime]
  (hζ : is_primitive_root ζ p) (hirr : irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
  discr K (hζ.power_basis K).basis =
  (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  have hodd' : (p : ℕ) ≠ 2 := λ hn, by exact hodd.symm (pnat.coe_inj.1 hn.symm),
  have hpos := pos_iff_ne_zero.2 (λ h, (tsub_pos_of_lt (prime.one_lt hp.out)).ne.symm h),

  rw [discr_power_basis_eq_norm, finrank _ hirr, hζ.power_basis_gen _,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, totient_prime hp.out],
  congr' 1,
  { have h := even_sub_one_of_prime_ne_two hp.out hodd',
    rw [← mul_one 2, ← nat.div_mul_div_comm (even_iff_two_dvd.1 h) (one_dvd _), nat.div_one,
      mul_one, mul_comm, pow_mul],
    congr' 1,
    exact (nat.even.sub_odd (one_le_iff_ne_zero.2 hpos.ne') h $ odd_iff.2 rfl).neg_one_pow },
  { have H := congr_arg derivative (cyclotomic_prime_mul_X_sub_one K p),
    rw [derivative_mul, derivative_sub, derivative_one, derivative_X, sub_zero, mul_one,
      derivative_sub, derivative_one, sub_zero, derivative_X_pow] at H,
    replace H := congr_arg (λ P, aeval ζ P) H,
    simp only [hζ.minpoly_eq_cyclotomic_of_irreducible hirr, aeval_add, _root_.map_mul, aeval_one,
      _root_.map_sub, aeval_X, minpoly.aeval, add_zero, aeval_nat_cast, aeval_X_pow] at H,
    replace H := congr_arg (algebra.norm K) H,
    rw [monoid_hom.map_mul, hζ.sub_one_norm_prime hirr hodd, monoid_hom.map_mul, monoid_hom.map_pow,
      hζ.norm_eq_one hodd hirr, one_pow, mul_one, ← map_nat_cast (algebra_map K L),
      norm_algebra_map, finrank _ hirr, totient_prime hp.out, ← succ_pred_eq_of_pos hpos, pow_succ,
      mul_comm _ (p : K), coe_coe, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H,
    simpa [(mul_right_inj' $ ne_zero.ne ↑↑p).1 H],
    apply_instance },
  { apply_instance },
end

end is_cyclotomic_extension
