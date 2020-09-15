import ring_theory.witt_vector.basic
import ring_theory.witt_vector.witt_vector_preps

/-!

# The `is_poly` predicate

`witt_vector.is_poly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → mv_polynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `is_poly.ext'`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (witt_polynomial p _ n) = bind₁ ψ (witt_polynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `witt_vector.frobenius`
and `witt_vector.verschiebung` is equal to multiplication by `p`.

## On higher arity analogues

Ideally, there should be a predicate `is_polyₙ` for functions of higher arity,
together with `is_polyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary variant so far.

Once a higher arity analogue gets implemented,
it can be tested by refactoring the proof that `verschiebung` is additive,
or by redoing (and hopefully golfing) the computations in `ring_theory.witt_vector.witt_sub`.

-/

namespace witt_vector

variables {p : ℕ} {R S σ idx : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]

local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial
local attribute [-simp] coe_eval₂_hom

include hp
variables (p)

section ghost_equation
noncomputable theory

lemma poly_eq_of_witt_polynomial_bind_eq (f g : ℕ → mv_polynomial ℕ ℤ)
  (h : ∀ n, bind₁ f (witt_polynomial p _ n) = bind₁ g (witt_polynomial p _ n)) :
  f = g :=
begin
  ext1 n,
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  rw ← function.funext_iff at h,
  replace h := congr_arg
    (λ fam, bind₁ (mv_polynomial.map (int.cast_ring_hom ℚ) ∘ fam)
    (X_in_terms_of_W p ℚ n)) h,
  simpa only [function.comp, map_bind₁, map_witt_polynomial,
    ← bind₁_bind₁, bind₁_witt_polynomial_X_in_terms_of_W, bind₁_X_right] using h
end

-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib
omit hp

/--
A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x` is given by evaluating `phiₙ` at the coefficients of `x`.
-/
@[nolint has_inhabited_instance]
structure is_poly (f : Π ⦃R : Type*⦄ [comm_ring R], witt_vector p R → 𝕎 R) :=
(poly : ℕ → mv_polynomial ℕ ℤ)
(coeff : ∀ (n : ℕ) ⦃R : Type*⦄ [comm_ring R] (x : 𝕎 R),
  (f x).coeff n = aeval (λ k, x.coeff k) (poly n))

/-- The identity function is a polynomial function. -/
def id_is_poly : is_poly p (λ _ _, id) :=
{ poly := X,
  coeff := by { introsI, rw [aeval_X, id] } }

instance is_poly.inhabited : inhabited (is_poly p (λ _ _, id)) :=
⟨id_is_poly p⟩

variables {p}

/-- The composition of polynomial functions is polynomial. -/
@[simps { fully_applied := ff }]
def is_poly.comp {g f} (hg : is_poly p g) (hf : is_poly p f) :
  is_poly p (λ R _Rcr, @g R _Rcr ∘ @f R _Rcr) :=
{ poly := λ n, bind₁ (hf.poly) (hg.poly n),
  coeff := by intros; simp only [aeval_bind₁, function.comp, hg.coeff, hf.coeff] }

lemma is_poly.ext {f g} (hf : is_poly p f) (hg : is_poly p g)
  (h : hf.poly = hg.poly) :
  f = g :=
by { ext R _Rcr x n, rw [hf.coeff, hg.coeff, h] }

include hp

lemma is_poly.ext' {f g} (hf : is_poly p f) (hg : is_poly p g)
  (h : ∀ n, bind₁ hf.poly (witt_polynomial p _ n) = bind₁ hg.poly (witt_polynomial p _ n)) :
  f = g :=
is_poly.ext hf hg $ poly_eq_of_witt_polynomial_bind_eq p _ _ h

end ghost_equation

end witt_vector
