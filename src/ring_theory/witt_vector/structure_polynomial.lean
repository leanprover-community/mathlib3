/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import data.matrix.notation
import field_theory.mv_polynomial
import field_theory.finite.polynomial
import number_theory.basic
import ring_theory.witt_vector.witt_polynomial

/-!
# Witt structure polynomials

In this file we prove the main theorem that makes the whole theory of Witt vectors work.
Briefly, consider a polynomial `Φ : mv_polynomial idx ℤ` over the integers,
with polynomials variables indexed by an arbitrary type `idx`.

Then there exists a unique family of polynomials `φ : ℕ → mv_polynomial (idx × ℕ) Φ`
such that for all `n : ℕ` we have (`witt_structure_int_exists_unique`)
```
bind₁ φ (witt_polynomial p ℤ n) = bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

N.b.: As far as we know, these polynomials do not have a name in the literature,
so we have decided to call them the “Witt structure polynomials”. See `witt_structure_int`.

## Special cases

With the main result of this file in place, we apply it to certain special polynomials.
For example, by taking `Φ = X tt + X ff` resp. `Φ = X tt * X ff`
we obtain families of polynomials `witt_add` resp. `witt_mul`
(with type `ℕ → mv_polynomial (bool × ℕ) ℤ`) that will be used in later files to define the
addition and multiplication on the ring of Witt vectors.

## Outline of the proof

The proof of `witt_structure_int_exists_unique` is rather technical, and takes up most of this file.

We start by proving the analogous version for polynomials with rational coefficients,
instead of integer coefficients.
In this case, the solution is rather easy,
since the Witt polynomials form a faithful change of coordinates
in the polynomial ring `mv_polynomial ℕ ℚ`.
We therefore obtain a family of polynomials `witt_structure_rat Φ`
for every `Φ : mv_polynomial idx ℚ`.

If `Φ` has integer coefficients, then the polynomials `witt_structure_rat Φ n` do so as well.
Proving this claim is the essential core of this file, and culminates in
`map_witt_structure_int`, which proves that upon mapping the coefficients of `witt_structure_int Φ n`
from the integers to the rationals, one obtains `witt_structure_rat Φ n`.
Ultimately, the proof of `map_witt_structure_int` relies on
```
dvd_sub_pow_of_dvd_sub {R : Type*} [comm_ring R] {p : ℕ} {a b : R} :
    (p : R) ∣ a - b → ∀ (k : ℕ), (p : R) ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k
```

## Main results

* `witt_structure_rat Φ`: the family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
  associated with `Φ : mv_polynomial idx ℚ` and satisfying the property explained above.
* `witt_structure_rat_prop`: the proof that `witt_structure_rat` indeed satisfies the property.

-/

open mv_polynomial
open set
open finset (range)
open finsupp (single)

-- This lemma reduces a bundled morphism to a "mere" function,
-- and consequently the simplifier cannot use a lot of powerful simp-lemmas.
-- We disable this locally, and probably it should be disabled globally in mathlib.
local attribute [-simp] coe_eval₂_hom

variables {p : ℕ} {R : Type*} {idx : Type*} [comm_ring R]

open_locale witt
open_locale big_operators

section p_prime

variables (p) [hp : fact p.prime]
include hp

/-- `witt_structure_rat Φ` is a family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
`bind₁ (witt_structure_rat p Φ) (witt_polynomial p ℚ n) = bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℚ n))) Φ`.
In other words: evaluating the `n`-th Witt polynomial on the family `witt_structure_rat Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `witt_structure_rat_prop` for this property,
and `witt_structure_rat_exists_unique` for the fact that `witt_structure_rat`
gives the unique family of polynomials with this property.

These polynomials turn out to have integral coefficients,
but it requires some effort to show this.
See `witt_structure_int` for the version with integral coefficients,
and `map_witt_structure_int` for the fact that it is equal to `witt_structure_rat`
when mapped to polynomials over the rationals. -/
noncomputable def witt_structure_rat (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  mv_polynomial (idx × ℕ) ℚ :=
bind₁ (λ k, bind₁ (λ i, rename (prod.mk i) (W_ ℚ k)) Φ) (X_in_terms_of_W p ℚ n)

theorem witt_structure_rat_prop (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  bind₁ (witt_structure_rat p Φ) (W_ ℚ n) =
    bind₁ (λ i, (rename (prod.mk i) (W_ ℚ n))) Φ :=
calc bind₁ (witt_structure_rat p Φ) (W_ ℚ n)
    = bind₁ (λ k, bind₁ (λ i, (rename (prod.mk i)) (W_ ℚ k)) Φ) (bind₁ (X_in_terms_of_W p ℚ) (W_ ℚ n)) :
      by { rw bind₁_bind₁, apply eval₂_hom_congr (ring_hom.ext_rat _ _) rfl rfl }
... = bind₁ (λ i, (rename (prod.mk i) (W_ ℚ n))) Φ :
      by rw [bind₁_X_in_terms_of_W_witt_polynomial p _ n, bind₁_X_right]

theorem witt_structure_rat_exists_unique (Φ : mv_polynomial idx ℚ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℚ),
    ∀ (n : ℕ), bind₁ φ (W_ ℚ n) = bind₁ (λ i, (rename (prod.mk i) (W_ ℚ n))) Φ :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n, apply witt_structure_rat_prop },
  { intros φ H,
    funext n,
    rw show φ n = bind₁ φ (bind₁ (W_ ℚ) (X_in_terms_of_W p ℚ n)),
    { rw [bind₁_witt_polynomial_X_in_terms_of_W p, bind₁_X_right] },
    rw [bind₁_bind₁],
        exact eval₂_hom_congr (ring_hom.ext_rat _ _) (funext H) rfl },
end

/-
TODO: In a follow-up PR we define `witt_structure_int`
and prove that it satisfies the properties claimed above.
-/

end p_prime
