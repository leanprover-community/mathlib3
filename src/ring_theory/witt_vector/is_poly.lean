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
open function (uncurry)
local attribute [-simp] coe_eval₂_hom

include hp
variables (p)

noncomputable theory

lemma poly_eq_of_witt_polynomial_bind_eq' (f g : ℕ → mv_polynomial (idx × ℕ) ℤ)
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
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `witt_vector.is_poly₂` for the binary variant.
-/
structure is_poly (f : Π ⦃R : Type*⦄ [comm_ring R], witt_vector p R → 𝕎 R) :=
(poly : ℕ → mv_polynomial ℕ ℤ)
(coeff : ∀ ⦃R : Type*⦄ [comm_ring R] (x : 𝕎 R),
  (f x).coeff = λ n, aeval x.coeff (poly n))

/-- The identity function on Witt vectors is a polynomial function. -/
def id_is_poly : is_poly p (λ _ _, id) :=
{ poly := X,
  coeff := by { introsI, simp only [aeval_X, id] } }

section zero_one
/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/

include hp

/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
@[simps { fully_applied := ff }]
def zero_is_poly : is_poly p (λ _ _ _, by exactI 0) :=
{ poly := 0,
  coeff := by { introsI, funext n, simp only [pi.zero_apply, alg_hom.map_zero, zero_coeff] } }

@[simp] lemma bind₁_zero_witt_polynomial (n : ℕ) :
  bind₁ (0 : ℕ → mv_polynomial ℕ R) (witt_polynomial p R n) = 0 :=
by rw [← aeval_eq_bind₁, aeval_zero, constant_coeff_witt_polynomial, ring_hom.map_zero]

omit hp

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
def one_poly (n : ℕ) : mv_polynomial ℕ ℤ := if n = 0 then 1 else 0

include hp

@[simp] lemma bind₁_one_poly_witt_polynomial (n : ℕ) :
  bind₁ one_poly (witt_polynomial p ℤ n) = 1 :=
begin
  rw [witt_polynomial_eq_sum_C_mul_X_pow, alg_hom.map_sum, finset.sum_eq_single 0],
  { simp only [one_poly, one_pow, one_mul, alg_hom.map_pow, C_1, pow_zero, bind₁_X_right,
      if_true, eq_self_iff_true], },
  { intros i hi hi0,
    simp only [one_poly, if_neg hi0, zero_pow (pow_pos (nat.prime.pos hp) _), mul_zero,
      alg_hom.map_pow, bind₁_X_right, alg_hom.map_mul], },
  { rw finset.mem_range, dec_trivial }
end

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
@[simps { fully_applied := ff }]
def one_is_poly : is_poly p (λ _ _ _, by exactI 1) :=
{ poly := one_poly,
  coeff :=
  begin
    introsI, funext n, cases n,
    { simp only [one_poly, if_true, eq_self_iff_true, one_coeff_zero, alg_hom.map_one], },
    { simp only [one_poly, nat.succ_pos', one_coeff_pos, if_neg n.succ_ne_zero, alg_hom.map_zero] }
  end }

end zero_one

/--
A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `witt_vector.is_poly` for the unary variant.
-/
structure is_poly₂ (f : Π ⦃R : Type*⦄ [comm_ring R], witt_vector p R → 𝕎 R → 𝕎 R) :=
(poly : ℕ → mv_polynomial (fin 2 × ℕ) ℤ)
(coeff : ∀ ⦃R : Type*⦄ [comm_ring R] (x y : 𝕎 R),
  (f x y).coeff = λ n, peval (poly n) ![x.coeff, y.coeff])

/-- Addition of Witt vectors is a polynomial function. -/
@[simps { fully_applied := ff }]
def add_is_poly₂ [fact p.prime] : is_poly₂ p (λ _ _, by exactI (+)) :=
{ poly := witt_add p,
  coeff := by { introsI, refl } }

/-- Multiplication of Witt vectors is a polynomial function. -/
@[simps { fully_applied := ff }]
def mul_is_poly₂ [fact p.prime] : is_poly₂ p (λ _ _, by exactI (*)) :=
{ poly := witt_mul p,
  coeff := by { introsI, refl } }

namespace is_poly

instance : inhabited (is_poly p (λ _ _, id)) :=
⟨id_is_poly p⟩

variables {p}

lemma ext {f g} (hf : is_poly p f) (hg : is_poly p g)
  (h : hf.poly = hg.poly) :
  f = g :=
by { ext R _Rcr x n, rw [hf.coeff, hg.coeff, h] }

/-- The composition of polynomial functions is polynomial. -/
@[simps { fully_applied := ff }]
def comp {g f} (hg : is_poly p g) (hf : is_poly p f) :
  is_poly p (λ R _Rcr, @g R _Rcr ∘ @f R _Rcr) :=
{ poly := λ n, bind₁ (hf.poly) (hg.poly n),
  coeff := by { intros, simp only [aeval_bind₁, function.comp, hg.coeff, hf.coeff] } }

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
@[simps { fully_applied := ff }]
def comp₂ {g f} (hg : is_poly p g) (hf : is_poly₂ p f) :
  is_poly₂ p (λ R _Rcr x y, by exactI g (f x y)) :=
{ poly := λ n, bind₁ (hf.poly) (hg.poly n),
  coeff := by { intros, simp only [peval, aeval_bind₁, function.comp, hg.coeff, hf.coeff] } }

include hp

lemma ext' {f g} (hf : is_poly p f) (hg : is_poly p g)
  (h : ∀ n, bind₁ hf.poly (witt_polynomial p _ n) = bind₁ hg.poly (witt_polynomial p _ n)) :
  ∀ (R : Type*) [_Rcr : comm_ring R] x, @f R _Rcr x = @g R _Rcr x :=
begin
  rw (is_poly.ext hf hg $ poly_eq_of_witt_polynomial_bind_eq p _ _ h),
  intros, refl
end

end is_poly

namespace is_poly₂

instance [fact p.prime] : inhabited (is_poly₂ p _) :=
⟨add_is_poly₂ p⟩

variables {p}

lemma ext {f g} (hf : is_poly₂ p f) (hg : is_poly₂ p g)
  (h : hf.poly = hg.poly) :
  f = g :=
by { ext R _Rcr x n, rw [hf.coeff, hg.coeff, h] }

/-- The composition of a binary polynomial function
with two unary polynomial functions is polynomial. -/
@[simps { fully_applied := ff }]
def comp {h g f} (hh : is_poly₂ p h) (hf : is_poly p f) (hg : is_poly p g) :
  is_poly₂ p (λ R _Rcr x y, by exactI h (f x) (g y)) :=
{ poly := λ n, bind₁ (uncurry $
            ![λ k, rename (prod.mk (0 : fin 2)) (hf.poly k),
              λ k, rename (prod.mk (1 : fin 2)) (hg.poly k)]) (hh.poly n),
  coeff :=
  begin
    intros,
    funext n,
    simp only [peval, aeval_bind₁, function.comp, hh.coeff, hf.coeff, hg.coeff, uncurry],
    apply eval₂_hom_congr rfl _ rfl,
    ext ⟨i, n⟩,
    fin_cases i;
    simp only [aeval_eq_eval₂_hom, eval₂_hom_rename, function.comp, matrix.cons_val_zero,
      matrix.head_cons, matrix.cons_val_one],
  end }

/-- The composition of a binary polynomial function
 with a unary polynomial function in the first argument is polynomial. -/
def comp_left {g f} (hg : is_poly₂ p g) (hf : is_poly p f) :
  is_poly₂ p (λ R _Rcr x y, by exactI g (f x) y) :=
hg.comp hf (id_is_poly p)

/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
def comp_right {g f} (hg : is_poly₂ p g) (hf : is_poly p f) :
  is_poly₂ p (λ R _Rcr x y, by exactI g x (f y)) :=
hg.comp (id_is_poly p) hf

include hp

lemma ext' {f g} (hf : is_poly₂ p f) (hg : is_poly₂ p g)
  (h : ∀ n, bind₁ hf.poly (witt_polynomial p _ n) = bind₁ hg.poly (witt_polynomial p _ n)) :
  ∀ (R : Type*) [_Rcr : comm_ring R] x y, @f R _Rcr x y = @g R _Rcr x y :=
begin
  rw (is_poly₂.ext hf hg $ poly_eq_of_witt_polynomial_bind_eq' p _ _ h),
  intros, refl
end

end is_poly₂

end witt_vector
