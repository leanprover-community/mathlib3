/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.reverse
import data.polynomial.div

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : polynomial R` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.nat_degree * f(1/X)`.

The main result is that `reverse (f * g) = reverse (f) * reverse (g)`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

namespace polynomial

open polynomial finsupp finset
open_locale classical

variables {R : Type*} [semiring R] {f : polynomial R}

namespace rev




lemma reflect_mul_induction2 :
 ∀ N O : ℕ, ∀ f g : polynomial R,
 f.nat_degree ≤ N → g.nat_degree ≤ O →
 (reflect (N + O) (f * g)) = (reflect N f) * (reflect O g) :=
begin
  intros N O f g,
  revert g,
  refine f.rec_on_horner _ _ _,
  { simp only [forall_const, reflect_zero, zero_mul, eq_self_iff_true, forall_true_iff], },
  { intros g r hg hr hor q Og Oq,
    rw [reflect_add, add_mul, add_mul, reflect_add, hor q _ Oq],
    congr,
    revert q r hg hr hor,
    refine g.rec_on_horner _ _ _,

    { simp * at *,sorry, },
--    simp only [reflect_zero, mul_zero], },
    intros p s p0 s0 hi q r hp hr hor Np de,
    rw [mul_add, reflect_add, hi, reflect_add, mul_add, reflect_C_mul, reflect_C_mul],
    rw [← mul_one (C r), ← pow_zero X, reflect_C_mul, pow_zero, mul_one, mul_assoc, mul_assoc],
    congr,

    simp only [reflect_C_mul, reflect_add],
    rw [mul_add, mul_add],
    rw [← mul_one df, cg0 ],
--    rw [← mul_one df, ← pow_zero X, ← reflect_C_mul_X_pow (N + O) 0 ],
--    rw [reflect_C_mul df dg (N + O)],

    rw reflect_mul hg ec0, },
  { intros p p0 hh pX g0,
    rw reflect_mul pX g0, },
end

end rev
end polynomial

#exit

begin
  intros N O f g,
  refine f.rec_on_horner _ _ _,
  simp only [reflect_zero, zero_mul, eq_self_iff_true, forall_true_iff],
  intros p a hp ha cp cp0 cg cg0 hg,
  simp only [*, reflect_mul] at *,
  intros p a hp ha cp cp0 cg,
  simp only [*, reflect_mul],
end


lemma nat_degree_add_le (f g : polynomial R) :
  (f + g).nat_degree ≤ max f.nat_degree g.nat_degree :=
begin
  by_cases f0 : f = 0,
  { rw [f0, zero_add, nat_degree_zero, max_eq_right], exact zero_le _, },
  by_cases g0 : g = 0,
  { rw [g0, add_zero, nat_degree_zero, max_eq_left], exact zero_le _, },
  by_cases fg0 : f + g = 0,
  { rw [fg0, nat_degree_zero], exact zero_le _, },
  rw [nat_degree_eq_support_max' f0, nat_degree_eq_support_max' g0, nat_degree_eq_support_max' fg0],
  apply max'_le,
  rintro n hn,
  rw [mem_support_iff_coeff_ne_zero, coeff_add] at hn,
  by_cases fn : f.coeff n = 0,
  { rw [fn, zero_add] at hn,
    exact le_max_iff.mpr (or.inr (g.support.le_max' n (mem_support_iff_coeff_ne_zero.mpr hn))), },
  { exact le_max_iff.mpr (or.inl (f.support.le_max' n (mem_support_iff_coeff_ne_zero.mpr fn))), },
end

lemma nat_degree_lt_add_eq_max (f g : polynomial R) (fg : f.nat_degree < g.nat_degree) :
  (f + g).nat_degree = g.nat_degree :=
begin
  sorry
end


lemma ne_nat_degree_add_eq_max (f g : polynomial R) (fg : f.nat_degree ≠ g.nat_degree) :
  (f + g).nat_degree = max f.nat_degree g.nat_degree :=
begin
  apply le_antisymm (nat_degree_add_le_max f g) _,
  rw ne_iff_lt_or_gt at fg,
  cases fg,
  { rw [max_eq_right (le_of_lt fg), nat_degree_lt_add_eq_max f g fg], },
  { rw [max_eq_left (le_of_lt fg), add_comm, nat_degree_lt_add_eq_max g f fg], },
end
