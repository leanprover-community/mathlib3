import ring_theory.power_series.well_known
import ring_theory.power_series.sincos_id
import data.complex.basic
import combinatorics.catalan

open complex
open ring_hom
open finset nat

namespace power_series

#check exp
#check exp ℂ



#check rescale
#check I
#check I^2
#check two_mul


example : 2 • exp ℂ = exp ℂ + exp ℂ := two_smul ℕ (exp ℂ)

variables (A A' : Type*) [field A]  [algebra ℚ A]

example : cos ℂ = (2:ℂ)⁻¹ • (rescale I (exp ℂ) + rescale (-I) (exp ℂ)) :=
begin
  ext1 n,
  rw [map_smul, map_add, coeff_rescale, coeff_rescale, neg_pow I, mul_assoc, ← one_add_mul],
  cases nat.even_or_odd n with neven nodd,
  { --Even
    unfold even at neven,
    cases neven with r hr,
    rw hr,
    rw ← bit0,
    rw I_pow_bit0,
    rw neg_pow_bit0,
    rw one_pow,
    rw one_add_one_eq_two,
    rw smul_eq_mul,
    rw ← mul_assoc,
    rw inv_mul_cancel,
    rw one_mul,
    rw cos,
    rw exp,
    rw coeff_mk,
    rw if_pos,
    rw coeff_mk,
    rw bit0_div_two,
    rw ← mul_one_div,
    rw map_mul,
    rw map_pow,
    rw map_neg,
    rw map_one,
    apply even_bit0,
    norm_num,
  },
  {
    --Odd
    cases nodd with r hr,
    rw hr,
    rw two_mul,
    rw ← bit0,
    rw ← bit1,
    rw neg_pow_bit1,
    rw one_pow,
    rw add_neg_self,
    rw zero_mul,
    rw smul_zero,
    rw cos,
    rw coeff_mk,
    rw if_neg,
    apply not_even_bit1,
    }
end



def maclaurin_sqrt_one_add_x : power_series A :=
  mk $ λ n, algebra_map ℚ A ((-1)^(n+1)*(n+1)*(catalan n)*(4^n * 2^(n-1))⁻¹)

example (A: Type*) [field A] [algebra ℚ A] : (maclaurin_sqrt_one_add_x A)*(maclaurin_sqrt_one_add_x A) = 1+X :=
begin
  ext1 n,
  rcases lt_trichotomy n 1 with a | b | c,
  {
    sorry,
  },
  {
    rw b,
    rw coeff_mul,
    rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
    rw sum_range_succ,
    rw sum_range_one,
    simp only [coeff_zero_eq_constant_coeff, tsub_zero,
      map_add, coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
  },
  {
    sorry,
  },
end

end power_series
