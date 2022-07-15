import ring_theory.power_series.well_known
import ring_theory.power_series.sincos_id
import data.complex.basic
import combinatorics.catalan
import tactic.ring_exp

open complex
open ring_hom
open finset nat

namespace power_series

variables (A A' : Type*) [field A]  [algebra ℚ A] [char_zero A]

def sqrt_one_add_X : power_series A :=
  mk $ λ n, algebra_map ℚ A ((-1)^(n+1)*(n+1)*(catalan n)*(4^n * (2*n-1))⁻¹)
/--/
example (A: Type*) [field A] [algebra ℚ A] :
      (sqrt_one_add_X A)*(sqrt_one_add_X A) = 1+X :=
begin
  ext1 n,
  rw coeff_mul,
  rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
  rw sum_range_succ,
  rcases lt_trichotomy n 1 with a | b | c,
  {-- n=0 case
    rw lt_one_iff at a,
    subst a,
    rw range_zero,
    rw finset.sum_empty,
    simp only [coeff_mk, sqrt_one_add_X, tsub_zero,
      coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
    simp only [map_add, coeff_one, coeff_X],
    simp only [←map_mul, ←map_add],
    norm_num,
  },
  {
    rw b,
    rw sum_range_one,
    simp only [coeff_mk, sqrt_one_add_X, tsub_zero,
      coeff_one, nat.one_ne_zero, if_false, coeff_one_X, zero_add],
    simp only [map_add, coeff_one, coeff_X],
    simp only [←map_mul, ←map_add],
    rw [if_neg, if_pos, zero_add, ←map_one (algebra_map ℚ A),
        (algebra_map ℚ A).injective.eq_iff],
    norm_num,
    refl,
    exact one_ne_zero,
  },
  {
    induction c with k hk,
    rw sum_range_succ,
    rw sum_range_one,
    simp only [coeff_mk, sqrt_one_add_X, tsub_zero,
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
-/
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



theorem sq_catalan_pow_series  (A : Type*) [semiring A]:
      1+ X* (catalan_power_series A)*(catalan_power_series A)=
      (catalan_power_series A)  :=
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

theorem sq_catalan_pow_series'  (A : Type*) [ring A]:
      X*(catalan_power_series A)^2=
      (catalan_power_series A)-1  :=
  begin
    sorry,
  end

lemma sqrt_one_add_X_catalan (A:Type*) [field A] [algebra ℚ A]:
  1+2⁻¹*X*(rescale ((-4:A)⁻¹) (catalan_power_series A)) = (sqrt_one_add_X A) :=
begin
  sorry,
end



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


theorem sq_power_series_sqrt_one_add_X_eq_one_add_X (A:Type*) [field A] [algebra ℚ A] [char_zero A]:
  (sqrt_one_add_X A)^2 = 1+X :=
  begin
    have h2 : (2 : A) ≠ 0 := two_ne_zero',
    have h4 : (4 : A) ≠ 0,
      { convert (mul_ne_zero h2 h2), norm_num },
    rw ←  sqrt_one_add_X_catalan,
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

#check mul_add




end power_series
