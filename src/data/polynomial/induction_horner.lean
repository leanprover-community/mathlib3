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

lemma reflect_mul_n (N O : ℕ) (f g : polynomial R) (hg : g.nat_degree ≤ O) :
  f.nat_degree ≤ N → (reflect (N + O) (f * g)) = (reflect N f) * (reflect O g) :=
begin
--  intros N O f g cf cg,
  refine f.rec_on_horner _ _ _,
  { simp only [reflect_zero, zero_mul, eq_self_iff_true, forall_true_iff], },
  { intros p r p0 hr h0 hp,
    rw [add_mul, reflect_add, reflect_add, add_mul, h0, reflect_mul _ hg],
    { rw [nat_degree_C],
      exact zero_le N, },
    { by_cases Cp : p.nat_degree = 0,
      { rw Cp, exact zero_le _, },

      sorry, }, },
--    simp only [*, reflect_mul, zero_le, nat_degree_C], },
  { intros p p0 hh pX,
    rw reflect_mul pX hg, },
end

lemma reflect_mul_induction2 (cf cg : ℕ) :
 ∀ N O : ℕ, ∀ f g : polynomial R,
 f.support.card ≤ cf.succ → g.support.card ≤ cg.succ → f.nat_degree ≤ N → g.nat_degree ≤ O →
 (reflect (N + O) (f * g)) = (reflect N f) * (reflect O g) :=
begin
  intros N O f g cf cg,
  refine f.rec_on_horner _ _ _,
  { simp only [reflect_zero, zero_mul, eq_self_iff_true, forall_true_iff], },
  { intros df dg cp0 cg cg0 hg ec0,
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
