import ring_theory.power_series.well_known
import data.complex.basic
import combinatorics.catalan

open complex
open ring_hom
open finset nat

namespace power_series

variables (A A' : Type*) [field A]  [algebra ℚ A]

def maclaurin_sqrt_one_add_x : power_series A :=
  mk $ λ n, algebra_map ℚ A ((-1)^(n+1)*(n+1)*(catalan n)*(4^n * (2*n-1))⁻¹)

example (A: Type*) [field A] [algebra ℚ A] :
      (maclaurin_sqrt_one_add_x A)*(maclaurin_sqrt_one_add_x A) = 1+X :=
begin
  ext1 n,
  rw coeff_mul,
  rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
  rw sum_range_succ,
  rcases lt_trichotomy n 1 with a | b | c,
  {-- n=0 case
    sorry,
  /-
    rw lt_one_iff at a,
    subst a,
    rw range_zero,
    rw finset.sum_empty,
    simp only [coeff_mk, maclaurin_sqrt_one_add_x, tsub_zero,
      coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
    simp only [map_add, coeff_one, coeff_X],
    simp only [←map_mul, ←map_add],
    norm_num,
    -/
  },
  {
    rw b,
    rw sum_range_one,
    simp only [coeff_mk, maclaurin_sqrt_one_add_x, tsub_zero,
      coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
    simp only [map_add, coeff_one, coeff_X],
    simp only [←map_mul, ←map_add],
    rw [if_neg, if_pos, zero_add, ←map_one (algebra_map ℚ A),
        (algebra_map ℚ A).injective.eq_iff],
    norm_num,
    refl,
    exact one_ne_zero,

    /-all_goals { sorry },

    norm_num,
    simp only [ring_hom.map_inv, pow_one, cast_zero, zero_add, neg_mul, mul_one, catalan_zero, cast_one, pow_zero, mul_zero,
  zero_sub, mul_neg, one_mul, map_neg, map_one, neg_one_sq, catalan_one, mul_inv_rev, map_mul, map_add, map_sub,
  map_bit0],-- from     squeeze_simp [ring_hom.map_inv],--squeeze it!
    norm_num,
    rw [← two_mul, ← mul_assoc],
    norm_num,
    rw ← inv_eq_one_div,
    rw mul_inv_cancel,
    have h1 : algebra_map ℚ A (4 : ℚ) = 4 := by simp only [map_bit0, map_one],
    have h2 : algebra_map ℚ A (0 : ℚ) = 0 := by simp only [map_zero],
    rw [←h1, ←h2],
    have : (13 : ℚ) ≠ (0 : ℚ),
    { norm_num, },
    exact (algebra_map ℚ A).injective.ne four_ne_zero,
    exact four_ne_zero,
    intro fouriszero,

    have key := four_ne_zero,
    have idea : (4:A) = 0 ↔ (1 : A) = 0,
    {
      calc
        4 = 0 ↔ 4 * 4⁻¹ = 0 * 4⁻¹ : sorry
          ... ↔ 1 = 0             : sorry,
    }

    sorry,
    --rw mul_inv_self,
    -/


  },
  {
    induction c with k hk,
    rw sum_range_succ,
    rw sum_range_one,
    simp only [coeff_mk, maclaurin_sqrt_one_add_x, tsub_zero,
      coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
    simp only [map_add, coeff_one, coeff_X],
    simp only [←map_mul, ←map_add],
    rw [if_neg, if_neg, zero_add], -- ←map_one (algebra_map ℚ A), (algebra_map ℚ A).injective.eq_iff],
    rw [ ← map_zero (algebra_map ℚ A),   (algebra_map ℚ A).injective.eq_iff],
    norm_num,
    rw catalan_two,
    norm_num,
    exact of_to_bool_ff rfl,
    exact two_ne_zero,
  },
end

end power_series
