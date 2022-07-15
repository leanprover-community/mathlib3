import ring_theory.power_series.well_known
import ring_theory.power_series.sincos_id
import data.complex.basic
import combinatorics.catalan
import tactic.ring_exp

open complex
open ring_hom
open finset nat

namespace power_series

#check exp
#check exp ℂ



#check rescale
#check I
#check I^2
#check two_mul.


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



def sqrt_one_add_X : power_series A :=
  mk $ λ n, algebra_map ℚ A ((-1)^(n+1)*(n+1)*(catalan n)*(4^n * (2*n-1))⁻¹)

def catalan_power_series (A : Type*) [semiring A]: power_series A :=
  mk $ λ n, catalan n

#check catalan_power_series.
#check power_series.
#print power_series.

lemma one_has_no_higher_terms (A : Type*) [semiring A] (n: ℕ ) (h: n > 0): (coeff A n) 1 = 0 :=
begin
  simp,
  intro nis0,
  exfalso,
  linarith,
end
#check one_has_no_higher_terms.



theorem square_pow_series_catalan  (A : Type*) [semiring A]:
      1+ X* (catalan_power_series A)*(catalan_power_series A)=
      catalan_power_series A  :=
begin
  ext n,
  rcases nat.eq_zero_or_pos n with rfl | npos,
  {--n=0
    rw [map_add, coeff_mul],
    rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
    rw sum_range_one,
    rw coeff_mul,
    rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
    simp only,
    rw sum_range_one,
    unfold catalan_power_series,
    rw coeff_mk,
    rw [coeff_one, if_pos rfl, catalan_zero, coeff_zero_X],
    norm_num,
  },
  {--n≥ 1 case
    rw [map_add, coeff_mul],
    rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
    rw [one_has_no_higher_terms A n npos,zero_add],
    simp only,
    -- we need to take care of the first term separately
    --rw sum_range,
    rw sum_range_succ', --pulls of first term
    simp only [coeff_succ_X_mul, coeff_zero_eq_constant_coeff,
        map_mul, constant_coeff_X, zero_mul, add_zero],
    --rw coeff_succ_X_mul ,--could not get it to work on its own.  Hmm.
    unfold catalan_power_series,
    simp only [coeff_mk],
    apply symm,
    have midea : ∃ m, n = succ m,
    {
      induction n with k hk,
      exfalso,
      linarith,
      use k,
    },
    cases midea with m hm,

    rw hm,
    nth_rewrite 0 succ_eq_add_one,
    --apply catalan_succ,
    rw [catalan],
    simp only [cast_sum, cast_mul, succ_sub_succ_eq_sub],
    rw sum_range,--switiches between types of sums
  },
end
#check square_pow_series_catalan.


theorem sq_catalan_pow_series'  (A : Type*) [ring A]:
      X*(catalan_power_series A)^2=
      (catalan_power_series A)-1  :=
  begin
    nth_rewrite 1 ← square_pow_series_catalan,
    rw pow_two,
    rw mul_assoc,
    simp only [add_sub_cancel'],
  end


lemma catalan_descent_lemma (n : ℕ ) :
(((n.succ) + 1) * ((catalan n.succ) * (1 / (4 ^ n.succ * (2 * (n.succ) - 1)))):ℚ)
=
2 *(catalan n)/(4^n.succ) :=
--old--  ((n.succ + 1) * (catalan n) / (2*n -1): ℚ) = 2 * (catalan (n-1)) :=
--((n.succ) + 1) * (catalan n.succ)
begin
  have h : n.succ ≤ 2* n.succ,
  {
    rw two_mul,
    linarith,
  },
   have two_ns_minus_ns: 2*n.succ-n.succ = n.succ,
  {
      simp only [two_mul,add_tsub_cancel_left],
  },
  have h2 : (2*n.succ -1:ℚ) = 2*n +1,
  {
    simp only [cast_succ],
    rw two_mul,
    linarith,
  },
  have h3 : (2*n.succ) = (2*n).succ.succ,
  {
    rw succ_eq_add_one,
    rw succ_eq_add_one,
    rw succ_eq_add_one,
    rw two_mul,
    rw two_mul,
    linarith,
  },
  rw h2,

  rw catalan_eq_central_binom_div,
  rw nat.cast_div (succ n).succ_dvd_central_binom,
  rw nat.cast_add,
  rw nat.cast_one,
  rw central_binom,
  rw choose_eq_factorial_div_factorial h,
  rw nat.cast_div (factorial_mul_factorial_dvd_factorial h),
  rw two_ns_minus_ns,
  rw nat.cast_mul,
  rw h3,
  rw factorial,
  rw factorial,
  rw factorial,


  --push casts
  rw nat.cast_mul,
  rw nat.cast_mul,
  rw nat.cast_mul,

  --get rid of succs
  rw succ_eq_add_one,
  rw succ_eq_add_one,
  rw succ_eq_add_one,

  rw [one_div,mul_inv],
  simp only [division_def],
  --cancel the n+1+1 term
  nth_rewrite 2 mul_comm,
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc],
  rw mul_inv_cancel,
  rw one_mul,
  rw [mul_comm,←mul_assoc,← mul_assoc],
  nth_rewrite 4 mul_comm,
  rw [← mul_assoc,← mul_assoc],
  nth_rewrite 4 mul_comm,
  rw nat.cast_add,
  rw nat.cast_mul,
  rw nat.cast_two,
  rw nat.cast_one,
  rw mul_inv_cancel,
  rw one_mul,
  have h4 : 2* n +1+1 = 2*(n+1),
  {
    rw [two_mul, two_mul],
    linarith,
  },
  rw h4,
  rw nat.cast_mul,
  rw mul_inv,
  rw mul_inv,
  nth_rewrite 1 mul_comm,
  rw [← mul_assoc,← mul_assoc],
  nth_rewrite 1 mul_comm,
  rw [← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc],
  rw mul_inv_cancel,
  rw one_mul,
  nth_rewrite 2 mul_comm,
  nth_rewrite 4 mul_comm,
  nth_rewrite 1 ← mul_assoc,
  rw ← mul_assoc,
  rw ← mul_inv,
  nth_rewrite 2 ← division_def,
  have h5 : n = 2*n - n,
  {
    simp only [two_mul, add_tsub_cancel_left],
  },
  nth_rewrite 2 h5,
  have h6 : n ≤ 2*n,
  {
    simp only [two_mul, le_add_iff_nonneg_left, zero_le'],
  },
  rw ← nat.cast_mul,
  rw ← nat.cast_div (factorial_mul_factorial_dvd_factorial h6),
  rw ← choose_eq_factorial_div_factorial h6,
  nth_rewrite 1 ← division_def,
  rw ← central_binom,
  rw ← nat.cast_div,--need to use that catalan is an integer; done later
  rw ← catalan_eq_central_binom_div,
  simp only [cast_bit0, cast_one, mul_eq_mul_right_iff, inv_eq_zero, pow_eq_zero_iff, succ_pos', bit0_eq_zero, one_ne_zero,
  or_false],
  left,
  rw mul_comm,

  ---Now entering the "easy" goals spawned by the above---
  --showing n+1 divides 2n choose n; a fact about the Catalan Numbers!
  {
    rw ← succ_mul_catalan_eq_central_binom,
    simp only [dvd_mul_right],
  },
  {
    have h8 : 0≤ (n:ℚ), apply cast_nonneg,
    linarith,
  },
  {
    simp [mono_cast],
    intro silly,
    have h8 : 0< n.factorial, apply factorial_pos,
    cases silly with wrong wronger,
    linarith,
    have h9 : 0 <  (2*n -n).factorial, apply factorial_pos,
    linarith,
  },
  {
    have h8 : 0≤ (n:ℚ), apply cast_nonneg,
    linarith,
  },
  {
    have h8 : 0≤ (n:ℚ), apply cast_nonneg,
    linarith,
  },
  {
    have h8 : 0≤ (n:ℚ), apply cast_nonneg,
    linarith,
  },
  {
    simp [mono_cast],
    intro silly,
    have h8 : 0< n.factorial, apply factorial_pos,
    cases silly with wrong wronger,
    cases wrong,
    {
      have h9 : 0≤ (n:ℚ), apply cast_nonneg,
      linarith,
    },
    linarith,
    have h9 : 0 <  (2*n.succ -n.succ).factorial, apply factorial_pos,
    linarith,
  },
  {
    have h8 : 0≤ (n:ℚ),
    {
      apply cast_nonneg,
    },
    rw nat.cast_add,
    rw succ_eq_add_one,
    rw nat.cast_add,
    simp only [nat.cast_one],
    intro itsfalse,
    linarith,
  },
end
--End of Catalan Descent.

example (a b : ℚ) (h: b≠ 0): a/b = a *b⁻¹:=
begin
exact division_def a b,
end

example (a b :ℕ) (h: 0 < b): b*a/b = a :=
begin
  exact mul_div_right a h,
end

--NOTE: This one is finally proved, though it has a new hypothesis.
lemma before_squaring (A: Type*) [field A] [algebra ℚ A] [char_zero A] :
sqrt_one_add_X A = (1/(2:A))•(X*(rescale (-4⁻¹) (catalan_power_series A))) + 1 :=
begin
  ext,
  cases n,
  {--n equals zero case
    rw [sqrt_one_add_X,coeff_mk],
    rw [catalan_power_series],
    simp only [zero_add, pow_one, cast_zero, neg_mul, catalan_zero, cast_one, pow_zero, mul_zero, zero_sub, one_mul, map_neg,
  one_div, map_add, constant_coeff_one],
    rw [coeff_smul,smul_eq_mul],
    simp only [coeff_zero_eq_constant_coeff, map_mul, constant_coeff_X, zero_mul, mul_zero, coeff_one, eq_self_iff_true, if_true,
  zero_add],
    rw ring_hom.map_inv,
    simp only [map_neg, map_one],
    rw [inv_neg,neg_neg],
    simp,--simp only [inv_one, eq_self_iff_true],--squeeze failed here, oddly
  },
  {-- n.succ case
    rw succ_eq_add_one,
    simp only [one_div, map_add, coeff_smul, coeff_succ_X_mul, coeff_rescale, coeff_one, succ_ne_zero, if_false, add_zero],
    rw [sqrt_one_add_X, coeff_mk],
    rw [mul_assoc, mul_assoc],
    rw ← one_div,
    rw catalan_descent_lemma,
    rw catalan_power_series,
    simp only [map_mul, map_pow, map_neg, map_one, coeff_mk],
    rw succ_eq_add_one,
    rw division_def,
    rw map_mul,
    rw map_mul,
    simp only [map_bit0, map_one, map_nat_cast],
    rw smul_eq_mul,
    rw [ring_hom.map_inv],
    simp only [map_pow, map_bit0, map_one],
    ring_exp,
    have h2 : (2 : A) ≠ 0 := two_ne_zero',
    have h4 : (4 : A) ≠ 0,
    { convert (mul_ne_zero h2 h2), norm_num },
    have h4n : (4 ^ n : A) ≠ 0 := pow_ne_zero n h4,
    field_simp,
    ring,
    --norm_cast,
  },
end


--This is the exact version that Tyler is using; it follows from above.
lemma sqrt_one_add_X_catalan (A: Type*) [field A] [algebra ℚ A] [char_zero A] :
sqrt_one_add_X A = 1+ 2⁻¹*X*(rescale ((-4:A)⁻¹) (catalan_power_series A)) :=
begin
  --idea use before_squaring lemma
  ext n,
  have l1: (2 : power_series A) = C A 2,
    {
      rw map_bit0,
      rw map_one,
    },

  rw map_add,
  --say 2⁻¹ is a constant
  rw [l1, C_inv],
  rw mul_assoc,
  rw ← smul_eq_C_mul,
  rw coeff_smul,
  rw before_squaring,--here is the main point.
  rw division_def,
  rw one_mul,
  rw map_add,
  rw add_comm,
  rw inv_neg,
  simp only [coeff_smul],
end

example (n :ℕ ) (h: n ≥ 1): ∃ m, n = succ m :=
begin
  induction n with k hk,
  exfalso,
  linarith,
  use k,
end

example (A : Type*) [semiring A] (a b : A  ) : a=b ↔ b=a :=
begin
  apply comm,
end

--example (A : Type*) [semiring A] (k : ℕ ): ((coeff A k) (X * catalan_power_series A)) =(coeff A k) :=

example (a b: ℕ ) (h: a< b ) :( b > a) :=
begin
  exact h,
end

#check nat.eq_zero_or_pos.

example  (A: Type*) [field A] (a : A) (ha : a ≠ 0) :  a*a⁻¹ = 1 :=
begin
  refine mul_inv_cancel ha,--library_search,--found this
end

example  (A: Type*) [field A] [algebra ℚ A] (a : A) :  (1: A) ≠ 0 :=
begin
  refine one_ne_zero,
end

--lemma rescale_X (A : Type*) [semiring A] (φ : power_series A): r
lemma rescale_X_eq_C_mul_X (A:Type*) (a:A) [comm_semiring A]: rescale a X = C A a * X :=
  begin
    ext1 n,
    rw X_eq,
    rw monomial_eq_mk,
    simp only [coeff_rescale, coeff_C_mul],
    rcases lt_trichotomy n 1 with a | b | c,
    {
      have n0 : n = 0,
        {
          exact lt_one_iff.mp a,
        },
      rw n0,
      rw coeff_mk,
      rw if_neg,
      norm_num,
      apply zero_ne_one,
    },
    {
      rw b,
      rw coeff_mk,
      rw if_pos,
      norm_num,
      refl,
    },
    {
      rw coeff_mk,
      rw if_neg,
      norm_num,
      exact ne_of_gt c,
    },
  end

--MAIN RESULT!

theorem sq_power_series_sqrt_one_add_X_eq_one_add_X (A:Type*) [field A] [algebra ℚ A] [char_zero A]:
  (sqrt_one_add_X A)^2 = 1+X :=
  begin
    have h2 : (2 : A) ≠ 0 := two_ne_zero',
    have h4 : (4 : A) ≠ 0,
      { convert (mul_ne_zero h2 h2), norm_num },
    rw sqrt_one_add_X_catalan,
    have l1: (2 : power_series A) = C A 2,
    {
      rw map_bit0,
      rw map_one,
     },
    have l3: (1 : power_series A) = C A 1,
    {
      rw map_one,
    },
    rw [l1, C_inv],
    have l2: X = - C A 4 * rescale ((-4 : A)⁻¹) X,
    {
      rw rescale_X_eq_C_mul_X,
      rw ← mul_assoc,
      rw neg_mul,
      rw ← map_mul,
      rw inv_neg,
      rw mul_neg,
      rw mul_inv_cancel,
      rw map_neg,
      rw map_one,
      rw neg_neg,
      rw one_mul,
      apply h4,
    },
    nth_rewrite 0 l2,
    rw mul_assoc,
    rw mul_assoc,
    rw ← map_mul,
    rw add_sq,
    rw mul_pow,
    rw mul_pow,
    rw ← map_pow,
    rw ← map_pow,
    rw mul_pow,
    rw sq X,
    rw mul_assoc X,
    rw sq_catalan_pow_series',
    rw map_mul,
    rw map_mul,
    rw map_sub,
    rw map_one,
    rw rescale_X_eq_C_mul_X,
    rw one_pow,
    rw mul_one,
    rw ← map_neg,
    rw l1,
    rw l3,
    --rw map_add,
    --rw map_add,
    rw ← map_pow,
    simp only [← mul_assoc],
    simp only [← map_mul],
    rw mul_sub,
    --rw map_sub,
    rw inv_pow,
    rw mul_inv_cancel,
    rw one_mul,
    rw mul_inv_cancel,
    rw sq,
    rw sq,
    have l4: (((2 * 2)⁻¹ * ((-4) * -4) * (-4)⁻¹):A) = (-1:A),
    { have : (16 : A) ≠ 0,
      { convert (mul_ne_zero h4 h4),
        norm_num,
      },
      field_simp,
      norm_num,
    },
    rw l4,
    rw map_neg,
    rw add_assoc,
    rw add_sub,
    rw neg_mul,
    rw neg_mul,
    rw add_neg_self,
    rw neg_mul,
    rw sub_eq_add_neg,
    rw neg_neg,
    rw zero_add,
    rw mul_assoc,
    rw mul_comm X _,
    rw ← l3,
    rw one_mul,
    rw one_mul,
    norm_num,
    exact h2,
  end
--Hooray!

end power_series
