/-
Copyright (c) 2022 The Xena Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, [add your name if you want]
-/
import ring_theory.localization.fraction_ring -- field of fractions
import data.polynomial.div -- theory of division and remainder for monic polynomials
import tactic.field_simp
/-

# Partial fractions

These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.

## The main theorems

* General partial fraction decomposition theorem for polynomials over ℝ
https://en.wikipedia.org/wiki/Partial_fraction_decomposition#General_result

* General partial fraction decomposition theorem for polynomials over ℂ
(same as above but skip the quadratic case)

* General partial fraction decomposition theorem for polynomials over a general field k
https://en.wikipedia.org/wiki/Partial_fraction_decomposition#Statement

## TODO

Everything

## Strategy

Here is my proposal.

1) Build a general theory of partial fractions over an
integral domain, as a "canonical" way of representing `f/g` when `g` is *monic*.
Assuming monicity makes some divisions a lot less painful (it also guarantees nonzeroness).

2) Deduce the theory of partial fractions over a field for `f/g` with `g` non-zero,
simply by dividing by the appropriate scalars everywhere.

I think that going from (1) to (2) is perhaps a bit fiddly (this is a nice Lean puzzle,
you'll learn a lot about finite sums and units). But doing (1) properly will be some
work. Here is my proposal for how to get through it.

1a) First develop the theory corresponding to partial fractions with denominators
`d₁, d₂, …, dₙ` where the `dᵢ` are monic and pairwise coprime. Do the theory
for `n=1` and `n=2` first and then prove the general theorem by induction on `n`.
Numerators must have degree less than denominators, and the decomposition is
unique.

1b) Now develop the theory for `f/g` with g a power of a monic polynomial.
I don't see why irreducibility is even needed.

-/

-- Let `R` be an integral domain
variables (R : Type) [comm_ring R] [is_domain R]

-- Let's use the usual `R[X]` notation for polynomials
open_locale polynomial

-- I don't want to have to keep typing `polynomial.degree_mod_by_monic_lt`
-- and `polynomial.mod_by_monic_add_div`, these names are long enough already
open polynomial

/-

## Worked example: division with remainder for monic polynomials.

Lean has a really robust library for division with remainder
for *monic* polynomials. Here's an example of it in action.

-/

section worked_example

-- let p and q be polynomials over `K`, and assume `q` is monic.
variables (p q : R[X]) (hq : monic q)

-- I claim that `p /ₘ q` is the rounded-to-the-nearest-polynomial division of `p` by `q`,
-- and that `p %ₘ q` is the remainder when you divide `p` by `q`.

-- Here's the proof that you can reconstruct p from the quotient and the remainder
example : p %ₘ q + q * (p /ₘ q) = p := mod_by_monic_add_div p hq

-- and here's the proof that deg(p %ₘ q) < deg(q):
example : (p %ₘ q).degree < q.degree := degree_mod_by_monic_lt p hq

/-
-- There are lots of other theorems about  `p %ₘ q` and `p /ₘ q`; you can
-- read them on these pages

https://leanprover-community.github.io/mathlib_docs/data/polynomial/div.html
https://leanprover-community.github.io/mathlib_docs/data/polynomial/ring_division.html

-/

end worked_example

/-

## One denominator, and two coprime denominators

-/

section one_denominator

-- Let's show that we can write `f/g` as `q+r/g` with deg(q) < deg(g)

namespace polynomial

-- As always, R is an integral domain.
-- Let f and g be polynomials
variables (f : R[X]) {g : R[X]}

-- Let K be the field of fractions of R[X].
-- Examples of elements of `K` are `X^2+1`, `1/X`, `(X^2+2X+3)/(4X^3+5)` etc
variables (K : Type) [field K] [algebra R[X] K]  [is_fraction_ring R[X] K]

section nice_trick

/-

Internally, `R[X]` is not a subset of `K`, for foundational reasons.
We set it up so that if `f : R[X]` then writing `(f : K)` will enable us to
think of `f` as an element of `K`. Lean will denote this "invisible map"
from R[X] to K with an `↑`.

-/

noncomputable instance : has_coe R[X] K := ⟨algebra_map R[X] K⟩

/-

If we train the `norm_cast` tactic on the basic properties of this coercion, then
it can be used to make our lives a lot easier.

-/
@[norm_cast] lemma coe_algebra_map_add (a b : R[X]) : ((a + b : R[X]) : K) = a + b :=
map_add (algebra_map R[X] K) a b

@[norm_cast] lemma coe_algebra_map_mul (a b : R[X]) : ((a * b : R[X]) : K) = a * b :=
map_mul (algebra_map R[X] K) a b

@[norm_cast] lemma coe_algebra_map_inj_iff (a b : R[X]) : (a : K) = b ↔ a = b :=
⟨λ h, is_fraction_ring.injective R[X] K h, by rintro rfl; refl⟩

@[norm_cast] lemma coe_algebra_map_eq_zero_iff (a : R[X]) : (a : K) = 0 ↔ a = 0 :=
begin
  rw (show (0 : K) = (0 : R[X]), from (map_zero (algebra_map R[X] K)).symm),
  norm_cast,
end

@[norm_cast] lemma coe_algebra_map_zero : ((0 : R[X]) : K) = 0 :=
map_zero (algebra_map R[X] K)

@[norm_cast] lemma coe_algebra_map_pow (a : R[X]) (n : ℕ) : ((a ^ n : R[X]) : K) = a ^ n :=
map_pow (algebra_map R[X] K) _ _

/-

That's all the training I can think of right now. Here are examples
of the cast tactic.

-/

-- if `↑f = ↑g ^ 2` then `f = g ^ 2`
example (f g : R[X]) (h : (f : K) = g^2) : f = g^2 :=
begin
  exact_mod_cast h,
end

-- ↑f + ↑g = ↑(f + g)
example (f g : R[X]) : (f : K) + g = (f + g : R[X]) :=
begin
  norm_cast,
end

end nice_trick

-- If `g` is monic then `f/g` can be written as `q+r/g` with deg(r) < deg(g)
lemma div_eq_div_add_mod_div (hg : g.monic) : ∃ q r : R[X], r.degree < g.degree ∧
  (f : K) / g = q + r / g :=
begin
  refine ⟨f /ₘ g, f %ₘ g, _, _⟩, -- same as `use, use, split`
  { exact degree_mod_by_monic_lt _ hg, },
  { have hg' : (g : K) ≠ 0 := by exact_mod_cast (monic.ne_zero hg),
    field_simp [hg'], -- "clear denominators" tactic
    norm_cast, -- now a question about R[X] not K
    rw [add_comm, mul_comm, mod_by_monic_add_div _ hg], },
end

end polynomial

end one_denominator
