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
  mk $ λ n, algebra_map ℚ A ((-1)^(n+1)*(n+1)*(catalan n)*(4^n * (2*n-1))⁻¹)

example (A: Type*) [field A] [algebra ℚ A] :
      (maclaurin_sqrt_one_add_x A)*(maclaurin_sqrt_one_add_x A) = 1+X :=
begin
  ext1 n,
  rcases lt_trichotomy n 1 with niszero | rfl | c,
  {-- n=0 case
    rw lt_one_iff at niszero,
    subst niszero,
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
  {--n = 1
    --rw nis1,
    --unfold maclaurin_sqrt_one_add_x,
    rw coeff_mul,
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
        4 = 0 ↔ 4 * 4⁻¹ = 0 * 4⁻¹ : sorry--FLAW: this assumed 4≠ 0, which was the goal
          ... ↔ 1 = 0             : sorry,
    }

    sorry,
    --rw mul_inv_self,
    -/


  },
  { -- n > 1
    sorry
  },
end

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
    rw sum_range,--Holy cow, why did this work???
  },
end
#check square_pow_series_catalan


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

/- Kaenchin Fodder for the proof above
    rw coeff_mul,
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
    exact one_ne_zero,
-/


#check nat.eq_zero_or_pos.

example  (A: Type*) [field A] (a : A) (ha : a ≠ 0) :  a*a⁻¹ = 1 :=
begin
  refine mul_inv_cancel ha,--library_search,--found this
end

example  (A: Type*) [field A] [algebra ℚ A] (a : A) :  (1: A) ≠ 0 :=
begin
  refine one_ne_zero,
end


end power_series
