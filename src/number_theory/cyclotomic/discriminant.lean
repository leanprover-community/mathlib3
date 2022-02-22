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
* `is_cyclotomic_extension.discr_odd_prime` : if `p` is an odd prime and
  `is_cyclotomic_extension {p} K L`, then
  `discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` for any primitive `n`-th
  root `ζ`.

## Implementation details
We prove the result for any `K` such that `linear_ordered_field K` and
`irreducible (cyclotomic p K)`. In practice these assumptions are satisfied for `K = ℚ`.

-/

universes u v
variables {p : ℕ+} (k : ℕ) {K : Type u} {L : Type v} {ζ : L} [linear_ordered_field K] [field L]
variables [algebra K L] [ne_zero ((p : ℕ) : K)]

open algebra polynomial nat is_primitive_root

namespace is_cyclotomic_extension

local attribute [instance] is_cyclotomic_extension.finite_dimensional

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
    rw [← mul_one 2, ← nat.div_mul_div (even_iff_two_dvd.1 h) (one_dvd _), nat.div_one, mul_one,
      mul_comm, pow_mul],
    congr' 1,
    exact neg_one_pow_of_odd (even.sub_odd (one_le_iff_ne_zero.2 hpos.ne.symm) h (odd_iff.2 rfl)) },
  { have H := congr_arg derivative (cyclotomic_prime_mul_X_sub_one K p),
    rw [derivative_mul, derivative_sub, derivative_one, derivative_X, sub_zero, mul_one,
      derivative_sub, derivative_one, sub_zero, derivative_X_pow] at H,
    replace H := congr_arg (λ P, aeval ζ P) H,
    simp only [hζ.minpoly_eq_cyclotomic_of_irreducible hirr, aeval_add, _root_.map_mul, aeval_one,
      _root_.map_sub, aeval_X, minpoly.aeval, add_zero, aeval_nat_cast, aeval_X_pow] at H,
    replace H := congr_arg (algebra.norm K) H,
    rw [monoid_hom.map_mul, hζ.sub_one_norm_prime hirr hodd, monoid_hom.map_mul,
      monoid_hom.map_pow, norm_eq_one K hζ (odd_iff.2 (or_iff_not_imp_left.1
      (nat.prime.eq_two_or_odd hp.out) hodd')), one_pow, mul_one, ← map_nat_cast
      (algebra_map K L), norm_algebra_map, finrank _ hirr, totient_prime hp.out,
      ← succ_pred_eq_of_pos hpos, pow_succ, mul_comm _ (p : K), coe_coe,
      ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H,
    simpa [(mul_right_inj' (cast_ne_zero.2 hp.out.ne_zero : (p : K) ≠ 0)).1 H],
    apply_instance },
  { apply_instance },
end

end is_cyclotomic_extension
