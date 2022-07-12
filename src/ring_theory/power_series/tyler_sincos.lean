import ring_theory.power_series.well_known
import ring_theory.power_series.sincos_id
import data.complex.basic

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
/-begin
  exact two_smul ℕ (exp ℂ),
  --rw [two_smul],
  --simp only [two_smul, nsmul_eq_mul, nat.cast_bit0, nat.cast_one],
end-/



theorem sin_is_sin : sin ℂ = rescale (I^4) (sin ℂ) :=
begin
  rw [I_pow_bit0,neg_one_sq, rescale_one,ring_hom.id_apply],
  --squeeze_simp,
end

#check nat.mod

variables {A : Type*} [ring A] [algebra ℚ A]

lemma coeff_sin_bit0 (n : ℕ) : coeff A (bit0 n) (sin A) = 0 :=
by rw [sin, coeff_mk, if_pos (even_bit0 n)]

lemma nat.bit1_div_bit0 (a b : ℕ) : bit1 a / bit0 b = a / b :=
begin
  have := nat.div_two_mul_two_add_one_of_odd (odd_bit1 a),
  rw [mul_two, ←bit0, ←bit1, nat.bit1_eq_bit1] at this,
  rw [bit0_eq_two_mul, ←nat.div_div_eq_div_mul, this],
end

lemma coeff_sin_bit1 (n : ℕ) : coeff A (bit1 n) (sin A) = (-1) ^ n * coeff A (bit1 n) (exp A) :=
by rw [sin, coeff_mk, if_neg (nat.not_even_bit1 n), nat.bit1_div_bit0, nat.div_one,
  ←mul_one_div, map_mul, map_pow, map_neg, map_one, coeff_exp]
#check sub_self

example : cos ℂ = (2:ℂ)⁻¹ • (rescale I (exp ℂ) + rescale (-I) (exp ℂ)) :=
begin
  ext1 n,
  rw [map_smul, map_add, coeff_rescale, coeff_rescale, neg_pow I, mul_assoc, ← one_add_mul],
  cases nat.even_or_odd n with neven nodd,
  { unfold even at neven,
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
    rw bit0,
    rw ← two_mul,


    --[←bit0, I_pow_bit0, neg_pow_bit0, one_pow, sub_self, zero_mul, smul_zero, coeff_sin_bit0]
    --rw [two_mul, ←bit0, ←bit1, neg_pow_bit1, one_pow, sub_neg_eq_add, ←bit0],
    --rw [I_pow_bit1, mul_comm ((-1) ^ k) I, mul_assoc, ←mul_assoc, smul_eq_mul,
    --    inv_mul_cancel_left₀, coeff_sin_bit1],
    --exact mul_ne_zero two_ne_zero' I_ne_zero
    --sorry,
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

end

#check sin_id

    #check has_smul ℚ ℂ


end power_series
