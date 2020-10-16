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

lemma reflect_mul (N O : ℕ) (f g : polynomial R) (hg : g.nat_degree ≤ O) :
  f.nat_degree ≤ N → (reflect (N + O) (f * g)) = (reflect N f) * (reflect O g) :=
begin
--  intros N O f g cf cg,
  refine f.rec_on_horner _ _ _,
  { simp only [reflect_zero, zero_mul, eq_self_iff_true, forall_true_iff], },
  { intros p r p0 hr h0 hp,
    rw [add_mul, reflect_add, reflect_add, add_mul],
    rw [reflect_mul _ hg, reflect_mul, nat_degree_C],
    rw nat_degree_C,
    simp only [*, reflect_mul, zero_le, nat_degree_C],
    rw reflect_mul _ hg,
    sorry, },
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
