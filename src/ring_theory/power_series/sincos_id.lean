import ring_theory.power_series.well_known
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



theorem sin_id : (sin ℂ) =  (2*I)⁻¹ • (rescale I (exp ℂ) - rescale (-I) (exp ℂ ) ) :=
begin
  --sorry,
  ext1,
  --simp only [exp, rescale, coeff_mk, coe_mk, factorial,
    --nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul],
  --try to show that is even or odd

  cases nat.even_or_odd n with neven nodd,
  { -- n is even here
    unfold even at neven,
    cases neven with r nisrpr,
    have idea : n=2*r,
    {
      rw nisrpr,
      rw two_mul,
    },
    rw idea,
    rw [],
    simp only [mul_inv_rev, inv_I, neg_mul, coeff_smul,
      map_sub, coeff_rescale, coeff_exp,
        one_div, algebra.id.smul_eq_mul],
    rw [pow_mul,pow_mul],
    rw [I_pow_bit0],
    simp only [coeff_mk, even.mul_right,
      even_two, if_true, pow_one, neg_sq, I_sq,
      sub_self, mul_zero, neg_zero'],
    simp only [sin, coeff_mk, even.mul_right, even_two, if_true],
  },
  {-- n is odd here
    unfold odd at nodd,
    cases nodd with k nis2kp1,
    rw nis2kp1,
    simp only [mul_inv_rev, inv_I, neg_mul,
      coeff_smul, map_sub, coeff_rescale,
      coeff_exp, factorial_succ, cast_mul, cast_add,
      cast_bit0, cast_one, one_div, map_mul, algebra.id.smul_eq_mul],
    rw [pow_add,pow_add],
    rw [pow_mul,pow_mul],
    rw neg_pow,
    rw I_pow_bit0,
    simp only [pow_one, neg_one_sq, mul_neg, mul_one, neg_mul, sub_neg_eq_add],
    rw ← two_mul,
    rw ← mul_assoc,
    simp only [inv_mul_cancel_right₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff],
    rw ← mul_assoc,
    rw ← mul_assoc,
    rw mul_comm ((-1)^k) I,
    rw ← mul_assoc,
    simp only [I_mul_I, neg_mul, one_mul, neg_neg],
    --simp only [sin, coeff_mk, factorial_succ, cast_mul, cast_add, cast_bit0, cast_one],
    /-have factorial_idea: (↑ ((2 * k).factorial))⁻¹ * (2 * ↑k + 1: ℚ)⁻¹
        = (↑((2 * k+1).factorial))⁻¹,
    {
      sorry,
    },
    have fact_idea_new :  (↑((2 * k).factorial))⁻¹ *  (2 * ↑k + 1: ℚ)⁻¹
        =  (↑((2 * k + 1).factorial))⁻¹ ,
    {
      sorry,
    },-/
    rw mul_assoc,
    have odd_fact : ¬ even (2 * k + 1),
    {
      have oddplan : odd (2*k +1),
      {
        use k,
      },
      rw odd_iff_not_even at oddplan,
      exact oddplan,
    },
    simp [sin, odd_fact],
    rw ← map_mul,
    rw ← mul_inv,
    --norm_cast,
    --rw mul_comm _ (2 * k + 1),
    --rw ← factorial_succ,
    have really : 1/2 = 0,
    {
      refl,
      --apply nat.div_def,--wow
    },
    have aux : (2 * k + 1) / 2 = k,
    {
      clear nis2kp1,
      clear odd_fact,
      induction k with r hr,
      apply nat.div_def,-- base case
      --induction step
      rw succ_eq_add_one,
      have idea : 2*(r+1)+1 = 2*r +1+2,
      {
        ring,
      },
      rw idea,
      have idea2 : (2*r +1+2)/2=(2*r+1)/2+1,
      {
        apply nat.div_def,
      },
      rw idea2,
      rw hr,
    },
    rw aux,
    rw div_eq_mul_inv,
    --
    nth_rewrite 1 mul_comm,
    rw map_mul,
    rw map_pow,
    rw map_neg,
    rw map_one,


    --rw ← smul_eq_mul,
    --rw algebra_map_smul,
    --rw fact_idea_new,
    --rw mul_comm,


    --rw fact_idea_new,





    --rw mul_inv I 2,
  },
end

theorem cos_id : (cos ℂ) =  (2: ℂ  )⁻¹ • (rescale I (exp ℂ) + rescale (-I) (exp ℂ ) ) :=
begin
  ext1 n,
  rw [map_smul, map_add, coeff_rescale, coeff_rescale,neg_pow I, mul_assoc, ← one_add_mul],
  --rcases n.even_or_odd with (⟨k, rfl⟩ | ⟨k, rfl⟩),
  cases nat.even_or_odd n with neven nodd,
  {--n even
    unfold even at neven,
    cases neven with r hr,
    rw [hr],
    sorry
  },
  {--n odd
    rcases nodd with ⟨r, rfl⟩,
    rw [two_mul,← bit0,← bit1,neg_pow_bit1, one_pow, ],

  }

end


#check sin_id

    #check has_smul ℚ ℂ


end power_series
