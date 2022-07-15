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
/-  have two_ns_pos : 0< 2*n.succ,
  {
    rw two_mul,
    rw add_succ,
    exact succ_pos (n.succ+ n),
  },
  rw ← mul_factorial_pred (two_ns_pos),
  rw nat.div_mul_cancel,-/

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

  ---Now entering the easy goals spawned by the above---
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
--End of Catalan Descent.  Holy Cow!!

example (a b : ℚ) (h: b≠ 0): a/b = a *b⁻¹:=
begin
exact division_def a b,
end

example (a b :ℕ) (h: 0 < b): b*a/b = a :=
begin
  exact mul_div_right a h,
end

--NOTE: This one is finally proved, though it has a new hypothesis.
--TODO: figure out whether we want the smul version like this, or the one below
lemma before_squaring (A: Type*) [field A] [algebra ℚ A] [char_zero A] :
maclaurin_sqrt_one_add_x A = (1/(2:A))•(X*(rescale (-4⁻¹) (catalan_power_series A))) + 1 :=
begin
  ext,
  cases n,
  {--n equals zero case
    --simp only [coeff_zero_eq_constant_coeff, one_div, map_add, constant_coeff_one],
    rw [maclaurin_sqrt_one_add_x,coeff_mk],
    rw [catalan_power_series],
    simp only [zero_add, pow_one, cast_zero, neg_mul, catalan_zero, cast_one, pow_zero, mul_zero, zero_sub, one_mul, map_neg,
  one_div, map_add, constant_coeff_one],
    rw [coeff_smul,smul_eq_mul],
    simp only [coeff_zero_eq_constant_coeff, map_mul, constant_coeff_X, zero_mul, mul_zero, coeff_one, eq_self_iff_true, if_true,
  zero_add],
    rw ring_hom.map_inv,
    simp only [map_neg, map_one],
    rw [inv_neg,neg_neg],
    simp,--simp only [inv_one, eq_self_iff_true],
  },
  {-- n.succ case
    rw succ_eq_add_one,
    simp only [one_div, map_add, coeff_smul, coeff_succ_X_mul, coeff_rescale, coeff_one, succ_ne_zero, if_false, add_zero],
    rw [maclaurin_sqrt_one_add_x, coeff_mk],
    rw [mul_assoc, mul_assoc],
    --rw mul_inv_rev,
    --rw ← inv_div_left,
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


    --maybe start here. HMMM
    /-
    cases (even_or_odd n),
    --n even case
    rw ← succ_eq_add_one,
    rw pow_succ,
    rcases h with ⟨ r, rfl ⟩,
    rw ← bit0,
    rw ← bit1,
    rw neg_pow_bit1,
    rw one_pow,
    rw neg_mul,
    rw one_mul,
    rw neg_neg,
    rw one_mul,
    rw [bit1],
    simp only [neg_pow_bit0, inv_pow],
    rw [mul_comm,← mul_assoc,← mul_assoc],
    have catalan_nzero : catalan (bit0 r) ≠ 0,
    {
      cases r,
      simp only [catalan_zero, ne.def, nat.one_ne_zero, not_false_iff],
      rw succ_eq_add_one,
      rw bit0,
      rw ← add_assoc,
      rw catalan,
      simp only [ne.def, sum_eq_zero_iff, mem_univ, nat.mul_eq_zero, forall_true_left, not_forall],
      use 1,
      push_neg,
      ---need to show that a catalan number is not usually zero.  Hmm.without
      sorry,
    },-/

    --apply mul_right_cancel₀ (catalan_nzero),




  },
end


--This is the exact version that Tyler is using.
--Can it follow from befone_squaring ??
lemma before_squaring_orig (A: Type*) [field A] [algebra ℚ A] :
maclaurin_sqrt_one_add_x A = 1+ 2⁻¹*X*(rescale (-4⁻¹) (catalan_power_series A)) :=
begin
  ext,
  cases n,
  {--n equals zero case
    sorry,
  },
  {-- n.succ case
    rw succ_eq_add_one,
    rw mul_assoc,
    rw [maclaurin_sqrt_one_add_x, coeff_mk],
    rw [mul_assoc, mul_assoc],
    --rw mul_inv_rev,
    --rw ← inv_div_left,
    rw ← one_div,
    rw catalan_descent_lemma,
    rw map_add,
    rw coeff_succ_X_mul,
    --rw ← one_div,
    --Wow--2⁻¹ is actually a _power_ series.  That is weird.
    rw coeff_mul,
    rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
    --HERE: it seem like having 2⁻¹ be a power series is messing things up.
    simp only [map_mul, map_pow, map_neg, map_one,
      coeff_rescale, coeff_one, succ_ne_zero, if_false, add_zero],
    rw catalan_power_series,
    simp,
    sorry,

    --rw constant_coeff_inv_of_unit,
    --rw is_unit_constant_coeff,



    --rw map_mul,
    --rw map_pow,
    --simp only [map_mul, map_pow, map_neg, map_one, coeff_one, succ_ne_zero, if_false, add_zero],
    --rw catalan_power_series,
    --rw ← smul_eq_mul,
    --rw ← map_smul,
    --rw coeff_rescale,
    --rw coeff_mk,
    --rw map_smul,
    --rw ← eq_X_mul_shift_add_const,
    --rw coeff_rescale,
    --rw catalan_power_series,
    --rw ← mul_assoc (↑(n.succ) + 1),--why did this not work?
    --nth_rewrite 1 ← mul_assoc,
   -- simp_rw catalan_eq_central_binom_div,
  },

  --nth_rewrite 1 ← mul_assoc,
  --rw succ_mul_central_binom_succ,

  --rw succ_mul_catalan_eq_central_binom,
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

lemma rescale_X (R : Type*) [comm_semiring R] (f : power_series R) (a : R) (n : ℕ) :
  coeff R n (rescale a X) = a^n * coeff R n X :=

--lemma rescale_X (A : Type*) [semiring A] (φ : power_series A): r


theorem square_power_series_is_one_add_X (A: Type*) [field A] [algebra ℚ A] [char_zero A]:
      (maclaurin_sqrt_one_add_x A)*(maclaurin_sqrt_one_add_x A) = 1+X :=
begin
  ext1 n,
  --rcases lt_trichotomy n 1 with niszero | rfl | c,
  cases n with nsucc,
  {-- n=0 case
    --rw lt_one_iff at niszero,
    --subst niszero,
    --rw niszero,
    rw coeff_mul,
    rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
    rw sum_range_one,
    simp only [coeff_mk, maclaurin_sqrt_one_add_x, tsub_zero,
      coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
    simp only [map_add, coeff_one, coeff_X],--compute coeff on RHS
    simp only [←map_mul, ←map_add],--pull out algebra map
    rw [if_pos rfl, if_neg nat.zero_ne_one, add_zero, ← map_one (algebra_map ℚ A)],
    --now, we can get rid of the algebra maps, since equality holds only if
    --arguments match
    rw [(algebra_map ℚ A).injective.eq_iff],
    norm_num,
  },
  {-- n.succ case
    rw before_squaring,
    rw [mul_add,add_mul,one_mul,mul_one],
    rw [map_add,map_add,map_add],
    rw [coeff_smul,smul_eq_mul],
    rw smul_eq_C_mul,
    rw [mul_assoc],
    rw [← smul_eq_C_mul,coeff_smul],
    nth_rewrite 0 mul_comm,
    rw [mul_assoc,mul_assoc,← smul_eq_C_mul,coeff_smul,smul_eq_mul,smul_eq_mul],
    rw [coeff_succ_X_mul],
    nth_rewrite 2 mul_comm,
    rw [mul_assoc,coeff_succ_X_mul],
    --try to apply the catalan lemma
    rw [coeff_rescale,← map_mul, ← mul_assoc],
    have h : 1/(2:A) *(1/(2:A))= 1/4,
    {
      field_simp,
      norm_num,
    },
    rw h,
    rw [division_def,one_mul,← smul_eq_mul,← coeff_smul,smul_eq_C_mul],




    nth_rewrite 2 mul_comm,



    --rw nis1,
    --unfold maclaurin_sqrt_one_add_x,
    /-rw coeff_mul,
    rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
    rw sum_range_succ,
    rw sum_range_one,
    --rw coeff_mk,
    --squeeze_simp [],
    simp only [coeff_mk, maclaurin_sqrt_one_add_x, tsub_zero,
      coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
    simp only [map_add, coeff_one, coeff_X],
    simp only [←map_mul, ←map_add],
    rw [if_neg, if_pos, zero_add, ←map_one (algebra_map ℚ A),
        (algebra_map ℚ A).injective.eq_iff],
    norm_num,
    refl,
    exact one_ne_zero,-/

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
        4 = 0 ↔ 4 * 4⁻¹ = 0 * 4⁻¹ : sorry--FLAW: this assumed 4≠ 0, which was the goal
          ... ↔ 1 = 0             : sorry,
    }

    sorry,
    --rw mul_inv_self,
    -/


  },
end





end power_series
