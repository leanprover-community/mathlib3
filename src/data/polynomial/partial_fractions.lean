/-
Copyright (c) 2022 The Xena Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan, [add your name if you want]
-/
import ring_theory.localization.fraction_ring -- field of fractions
import data.polynomial.div -- theory of division and remainder for monic polynomials
import tactic.field_simp
import tactic
import data.zmod.basic
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

## A trick: getting `norm_cast` to work

`norm_cast` is a tactic which proves goals like `↑f + ↑g = ↑(f + g)`.
Here the up-arrow is an "invisible map", which in this case will be the
map from R[X] to its field of fractions. The point is that if we want to do division
of polynomials we need to work in the field of fractions, but the moment we've
cleared denominators we want to get back into the R[X] world.

-/

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

namespace polynomial

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

end polynomial

/-

That's all the training I can think of right now (although I'm open to the idea
that there are more lemmas we'll need). Here are examples of `cast` tactics.

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

/-

## One denominator, and two coprime denominators

-/

section one_denominator

-- Let's show that we can write `f/g` as `q+r/g` with deg(q) < deg(g)

namespace polynomial

-- As always, R is an integral domain.
-- Let f and g be polynomials
variables (f : R[X]) {g : R[X]}

-- If `g` is monic then `f/g` can be written as `q+r/g` with deg(r) < deg(g)
lemma div_eq_quo_add_rem_div (hg : g.monic) : ∃ q r : R[X], r.degree < g.degree ∧
  (f : K) / g = q + r / g :=
begin
  -- let `q` be "polynomial division `f / g`" and let `r` be the remainder
  refine ⟨f /ₘ g, f %ₘ g, _, _⟩, -- same as `use, use, split`
  -- The fact that the degree of the remainder is < degree of what we're dividing by is in the
  -- library
  { exact degree_mod_by_monic_lt _ hg, },
  -- For the other proof we first want to clear denominators.
  -- Our goal is in `K` right now so to clear denominators we need (g : K) ≠ 0
  -- Note that `monic.ne_zero hg` is a proof that (g : R[X]) ≠ 0, so a `cast` tactic can
  -- finish the job.
  { have hg' : (g : K) ≠ 0 := by exact_mod_cast (monic.ne_zero hg),
     -- Now use the "clear denominators" tactic.
    field_simp [hg'],
    -- Now use `norm_cast` to get out of `K` and back into `R[X]`
    norm_cast,
    -- now it's nearly `mod_by_monic_add_div` except that things need some rearranging.
    rw [add_comm, mul_comm, mod_by_monic_add_div _ hg], },
end

end polynomial

end one_denominator

section two_denominators

-- If `g₁` and `g₂` are coprime monics then `f/g₁g₂` can be written as `q+r₁/g₁+r₂/g₂`
-- with deg(rᵢ) < deg(gᵢ)
lemma div_eq_quo_add_rem_div_add_rem_div {f g₁ g₂ : R[X]}
  (hg₁ : g₁.monic) (hg₂ : g₂.monic) (hcoprime : is_coprime g₁ g₂ ) :
  ∃ q r₁ r₂ : R[X], r₁.degree < g₁.degree ∧ r₂.degree < g₂.degree ∧
  (f : K) / (g₁ * g₂) = q + r₁ / g₁ + r₂ / g₂ :=
begin
  rcases hcoprime with ⟨ c, d, hcd ⟩,
  refine ⟨ (f*d) /ₘ g₁ + (f*c) /ₘ g₂ , (f*d) %ₘ g₁ , (f*c) %ₘ g₂ ,
    (degree_mod_by_monic_lt _ hg₁) , (degree_mod_by_monic_lt _ hg₂) , _⟩,
  have hg₁' : (g₁ : K) ≠ 0,
  { norm_cast, exact hg₁.ne_zero_of_ne zero_ne_one, },
  have hg₂' : (g₂ : K) ≠ 0,
  { norm_cast, exact hg₂.ne_zero_of_ne zero_ne_one, },
  have hfc := mod_by_monic_add_div (f * c) hg₂,
  have hfd := mod_by_monic_add_div (f * d) hg₁,
  field_simp,
  norm_cast,
  linear_combination (-1) * f * hcd + (-1) * g₁ * hfc + (-1) * g₂ * hfd,
end

end two_denominators

section n_denominators

-- need notation for finite products
open_locale big_operators

lemma finite_product_of_monics_is_monic {ι : Type*} {g : ι → R[X]}
  (hg : ∀ i, (g i).monic) (s : finset ι) : (∏ i in s, g i).monic :=
begin
  have h0 := monic_prod_of_monic s g _,
  { exact h0 },
  { intros i hi,
    exact hg i, },
end

/-
lemma coprimality_of_products_of_coprimes {ι : Type*} {g : ι → R[X]}
  (hg : ∀ i, (g i).monic) (hcop : pairwise (λ i j, is_coprime (g i) (g j)))
  (s : finset ι) [nonempty s] :
  (∀ t : s, is_coprime (g t) (∏ i in ({a : ι // a ∈ s ∧ a ≠ t} : finset ι), g i)) :=
begin
  sorry
end
-/

lemma mul_finite_sum {ι : Type*} {s : finset ι} {g : ι → K} {h : K} :
  h * (∑ i in s, g i) = ∑ i in s, (h * g i) :=
begin
  classical,
  apply s.induction_on,
  { simp only [finset.sum_empty, mul_zero], },
  { intros a s has H,
    rw [finset.sum_insert has, finset.sum_insert has, ← H, ← mul_add], },
end


lemma div_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]}
  (hg : ∀ i, (g i).monic) (hcop : pairwise (λ i j, is_coprime (g i) (g j)))
  (s : finset ι) [nonempty s] :
  ∃ (q : R[X]) (r : ι → R[X]), (∀ i, (r i).degree < (g i).degree) ∧
  (f : K) / ∏ i in s, g i = q + ∑ i in s, (r i) / (g i) :=
begin
  classical,
  apply s.induction_on,
  { refine ⟨f, (λ (i : ι), (0 : R[X])), _⟩,
    split,
    { intro i,
      rw [degree_zero, bot_lt_iff_ne_bot],
      intro hdg,
      specialize hg i,
      rw degree_eq_bot at hdg, rw hdg at hg,
      have h0nmonic : ¬ (0:R[X]).monic := not_monic_zero,
      contradiction, },
    { simp only [finset.prod_empty, div_one, finset.sum_empty, add_zero], }, },
  { intros a b hab H,
    rcases H with ⟨q, r, Hdeg, Hind⟩,
    -- have h1 : (∏ (i : ι) in insert a b, ↑(g i)) = ↑(g a) * (∏ (j : ι) in b, ↑(g j)),
    -- { --exact finset.prod_insert hab, -- should work... right?
    --   refine unit.ext,
    --   { exact comm_ring.to_comm_monoid unit },
    --   { apply has_lift_t.mk, intro rx, exact (), },
    --   { exact distrib.to_has_mul unit },
    --   { apply has_lift_t.mk, intro rx, exact (), },
    --   { exact comm_ring.to_comm_monoid unit, },
    --   { apply has_lift_t.mk, intro rx, exact (), }, },
    have hcalc : (f : K) / ((g a) * ((∏ (j : ι) in b, ↑(g j)))) = (1 / (g a)) * ((f : K) / ((∏ (j : ι) in b, ↑(g j)))),
      { field_simp, },
    rw [finset.prod_insert hab, hcalc, Hind, mul_add, mul_finite_sum],
    field_simp,
    sorry, },
end

-- uniqueness
lemma div_eq_quo_add_sum_rem_div_unique {f : R[X]} {ι : Type*} [fintype ι] {g : ι → R[X]}
  (hg : ∀ i, (g i).monic) (q : R[X]) (r : ι → R[X]) (hr : ∀ i, (r i).degree < (g i).degree)
  (hf : (f : K) / ∏ i, g i = q + ∑ i, (r i) / (g i)) :
    q = (div_eq_quo_add_sum_rem_div R K f hg).some ∧
    r = (div_eq_quo_add_sum_rem_div R K f hg).some_spec.some :=
begin
  sorry
end

end n_denominators
