/-
Copyright (c) 2022 The Xena Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan
-/
import ring_theory.localization.fraction_ring -- field of fractions
import data.polynomial.div -- theory of division and remainder for monic polynomials
import tactic.field_simp
import tactic
import data.zmod.basic
import logic.function.basic
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
We set it up so that if `f : R[X]` then writing `(↑f : K)` will enable us to
think of `f` as an element of `K`. Think of `↑` as the "invisible map"
from R[X] to K.

-/

-- if `↑f = ↑g ^ 2` then `f = g ^ 2`
example (f g : R[X]) (h : (↑f : K) = ↑g^2) : f = g^2 :=
begin
  exact_mod_cast h,
end

-- ↑f + ↑g = ↑(f + g)
example (f g : R[X]) : (↑f : K) + ↑g = ↑(f + g : R[X]) :=
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
  (↑f : K) / ↑g = ↑q + ↑r / ↑g :=
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
  { have hg' : (↑g : K) ≠ 0 := by exact_mod_cast (monic.ne_zero hg),
     -- Now use the "clear denominators" tactic.
    field_simp [hg'],
    -- Now use `norm_cast` to get out of `K` and back into `R[X]`
    norm_cast,
    -- now it's nearly `mod_by_monic_add_div` except that things need some rearranging.
    rw [add_comm, mul_comm, mod_by_monic_add_div _ hg], },
end

end polynomial

end one_denominator

.

section two_denominators

-- If `g₁` and `g₂` are coprime monics then `f/g₁g₂` can be written as `q+r₁/g₁+r₂/g₂`
-- with deg(rᵢ) < deg(gᵢ)
lemma div_eq_quo_add_rem_div_add_rem_div {f g₁ g₂ : R[X]} --(f : R[X])
  (hg₁ : g₁.monic) (hg₂ : g₂.monic) (hcoprime : is_coprime g₁ g₂ ) :
  ∃ q r₁ r₂ : R[X], r₁.degree < g₁.degree ∧ r₂.degree < g₂.degree ∧
  (↑f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ :=
begin
  rcases hcoprime with ⟨ c, d, hcd ⟩,
  refine ⟨ (f*d) /ₘ g₁ + (f*c) /ₘ g₂ , (f*d) %ₘ g₁ , (f*c) %ₘ g₂ ,
    (degree_mod_by_monic_lt _ hg₁) , (degree_mod_by_monic_lt _ hg₂) , _⟩,
  have hg₁' : (↑g₁ : K) ≠ 0,
  { norm_cast, exact hg₁.ne_zero_of_ne zero_ne_one, },
  have hg₂' : (↑g₂ : K) ≠ 0,
  { norm_cast, exact hg₂.ne_zero_of_ne zero_ne_one, },
  have hfc := mod_by_monic_add_div (f * c) hg₂,
  have hfd := mod_by_monic_add_div (f * d) hg₁,
  field_simp,
  norm_cast,
  linear_combination (-1) * f * hcd + (-1) * g₁ * hfc + (-1) * g₂ * hfd,
end

end two_denominators

.

section n_denominators

example (ι : Type) (s : finset ι) (a : ι) : a ∈ (s : set ι) ↔ a ∈ s := finset.mem_coe
-- need notation for finite products
open_locale big_operators classical

lemma div_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} (s : finset ι)
  (hg : ∀ i ∈ s, (g i).monic)
  (hcop : set.pairwise ↑s (λ i j, is_coprime (g i) (g j))) :
  ∃ (q : R[X]) (r : ι → R[X]), (∀ i ∈ s, (r i).degree < (g i).degree) ∧
  (↑f : K) / ∏ i in s, ↑(g i) = ↑q + ∑ i in s, ↑(r i) / ↑(g i) :=
begin
  induction s using finset.induction_on with a b hab Hind f generalizing f,
  { refine ⟨f, (λ (i : ι), (0 : R[X])), λ i, _, by simp⟩,
    rintro ⟨⟩, },
  { obtain ⟨q₀, r₁, r₂, hdeg₁, hdeg₂, (hf : (↑f : K) / _ = _)⟩ :=
      div_eq_quo_add_rem_div_add_rem_div R K
      (_ : monic (g a))
      (_ : monic ∏ (i : ι) in b, (g i))
      _,
    { obtain ⟨q, r, hrdeg, IH⟩ := Hind (λ i hi, hg i (finset.mem_insert_of_mem hi))
        (set.pairwise.mono (show (b : set ι) ⊆ (insert a b : finset ι),
          from finset.coe_subset.2 $ λ i hi, finset.mem_insert_of_mem hi) hcop) r₂,
      refine ⟨q₀ + q, λ i, if i = a then r₁ else r i, _, _⟩,
      { intro i,
        split_ifs with h1,
        { cases h1,
          intro _,
          exact hdeg₁, },
        { intro hi,
          refine hrdeg i (finset.mem_of_mem_insert_of_ne hi h1), }, },
      norm_cast at ⊢ hf IH,
      rw [finset.prod_insert hab, hf, IH, finset.sum_insert hab, if_pos rfl],
      -- use `transitivity` tactic to break this into a `ring` and a `congr`
      transitivity (↑(q₀ + q : R[X]) : K) + (↑r₁ / ↑(g a) + ∑ (i : ι) in b, ↑(r i) / ↑(g i)),
      { push_cast, ring, },
      congr' 2,
      refine finset.sum_congr rfl (λ x hxb, _),
      have hxa : ¬(x = a),
      { rintro rfl,
        exact hab hxb, },
      rw if_neg hxa, },
    { exact hg a (b.mem_insert_self a), },
    { refine monic_prod_of_monic _ _ (λ i hi, hg i (finset.mem_insert_of_mem hi)), },
    { refine is_coprime.prod_right (λ i hi, hcop (finset.mem_coe.2 (b.mem_insert_self a))
       (finset.mem_coe.2 (finset.mem_insert_of_mem hi)) _),
      rintro rfl, -- this is a hidden `rw`, so I need to leave term mode
      exact hab hi, }, },
end

.

lemma div_eq_quo_add_sum_rem_div_unique' {f : R[X]} {ι : Type*} (s : finset ι) {g : ι → R[X]}
  (hg : ∀ i ∈ s, (g i).monic) (hcop : (s : set ι).pairwise (λ i j, is_coprime (g i) (g j)))
  (q : R[X]) (r : ι → R[X]) (hdeg : ∀ i, (r i).degree < (g i).degree)
  (hf : (↑f : K) / ∏ i in s, ↑(g i) = ↑q + ∑ i in s, ↑(r i) / ↑(g i)) :
    q = (div_eq_quo_add_sum_rem_div R K f s hg hcop).some ∧
    ∀ i ∈ s, r i = (div_eq_quo_add_sum_rem_div R K f s hg hcop).some_spec.some i :=
begin
  let q₀ := (div_eq_quo_add_sum_rem_div R K f s hg hcop).some,
  let r₀ := (div_eq_quo_add_sum_rem_div R K f s hg hcop).some_spec.some,
  obtain ⟨hdeg₀, hf₀⟩ : (∀ i ∈ s, (r₀ i).degree < ((λ (i : ι), g i) i).degree) ∧
    ↑f / ∏ i in s, ↑((λ (i : ι), g i) i) = ↑q₀ + ∑ i in s, ↑(r₀ i) / ↑((λ (i : ι), g i) i) :=
    (div_eq_quo_add_sum_rem_div R K f s hg hcop).some_spec.some_spec,
  change q = q₀ ∧ ∀ i ∈ s, r i = r₀ i, split,
  { rw hf at hf₀,
    have htriv : g = λ (i : ι), g i := rfl,
    rw ← htriv at hf₀,
    sorry },
  {
    sorry },
end

end n_denominators
