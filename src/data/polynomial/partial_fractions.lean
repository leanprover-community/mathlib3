/-
Copyright (c) 2022 The Xena Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, [add your name if you want]
-/
import ring_theory.localization.fraction_ring -- field of fractions
import data.polynomial.div -- theory of division and remainder for monic polynomials
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
-/

-- Let `K` be a field

variables (K : Type) [field K]

-- Let's use the usual `K[X]` notation for polynomials
open_locale polynomial

/-

## Worked example: division with remainder for monic polynomials.

Lean has a really robust library for division with remainder
for *monic* polynomials. Here's an example of it in action.

-/

-- I don't want to have to keep typing `polynomial.degree_mod_by_monic_lt`
-- and `polynomial.mod_by_monic_add_div`, these names are long enough already
open polynomial

-- let p and q be polynomials over `K`, and assume `q` is monic.
variables (p q : K[X]) (hq : monic q)

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
