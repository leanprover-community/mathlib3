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

## Main declarations

* `witt_vector.is_poly`, `witt_vector.is_poly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `witt_vector.is_poly.ext'`, `witt_vector.is_poly₂.ext'`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynmials on them.
* `witt_vector.is_poly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `witt_vector.id_is_poly`, `witt_vector.neg_is_poly`,
  `witt_vector.add_is_poly₂`, `witt_vector.mul_is_poly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `is_polyₙ` for functions of higher arity,
together with `is_polyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated as constant functions and fall under the unary case.
-/

/-
This tactic is used later in the development for certain simplifications.
We define it here so it is a shared import.
-/

mk_simp_attribute ghost_simps
"Simplification rules for ghost equations"

namespace tactic
namespace interactive
setup_tactic_parser
/-- A macro for a common simplification when rewriting with ghost component equations. -/
meta def witt_simp (lems : parse simp_arg_list) : tactic unit :=
do tactic.try tactic.intro1,
   --lems ← simp_lemmas.add_simp lems `rename_bind₁ tt,
   simp none tt
     (lems ++ [simp_arg_type.symm_expr ``(mv_polynomial.rename_bind₁),
               simp_arg_type.symm_expr ``(mv_polynomial.bind₁_bind₁)])
     [`ghost_simps] (loc.ns [none])
-- `[try {intro}, simp only [← rename_bind₁, ← bind₁_bind₁] with ghost_simps]

end interactive
end tactic

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
structure is_poly (f : Π ⦃R⦄ [comm_ring R], witt_vector p R → 𝕎 R) (φ : ℕ → mv_polynomial ℕ ℤ) :=
(coeff : ∀ ⦃R⦄ [comm_ring R] (x : 𝕎 R), (f x).coeff = λ n, aeval x.coeff (φ n))

/-- The identity function on Witt vectors is a polynomial function. -/
def id_is_poly : is_poly p (λ _ _, id) X :=
⟨by { introsI, simp only [aeval_X, id] }⟩

include hp

/-- The additive negation is a polynomial function on Witt vectors. -/
def neg_is_poly : is_poly p (λ R _, by exactI @has_neg.neg (𝕎 R) _)
  (λ n, rename prod.snd (witt_neg p n)) :=
{ coeff :=
  begin
    introsI, funext n,
    rw [neg_coeff, aeval_eq_eval₂_hom, eval₂_hom_rename],
    apply eval₂_hom_congr rfl _ rfl,
    ext ⟨i, k⟩, fin_cases i, refl,
  end }


section zero_one
/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/

/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
def zero_is_poly : is_poly p (λ _ _ _, by exactI 0) 0 :=
⟨by { introsI, funext n, simp only [pi.zero_apply, alg_hom.map_zero, zero_coeff] }⟩

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
def one_is_poly : is_poly p (λ _ _ _, by exactI 1) one_poly :=
{ coeff :=
  begin
    introsI, funext n, cases n,
    { simp only [one_poly, if_true, eq_self_iff_true, one_coeff_zero, alg_hom.map_one], },
    { simp only [one_poly, nat.succ_pos', one_coeff_pos, if_neg n.succ_ne_zero, alg_hom.map_zero] }
  end }

end zero_one

omit hp

/--
A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `witt_vector.is_poly` for the unary variant.
-/
structure is_poly₂ (f : Π ⦃R⦄ [comm_ring R], witt_vector p R → 𝕎 R → 𝕎 R)
  (φ : ℕ → mv_polynomial (fin 2 × ℕ) ℤ) :=
(coeff : ∀ ⦃R⦄ [comm_ring R] (x y : 𝕎 R), (f x y).coeff = λ n, peval (φ n) ![x.coeff, y.coeff])

/-- Addition of Witt vectors is a polynomial function. -/
def add_is_poly₂ [fact p.prime] : is_poly₂ p (λ _ _, by exactI (+)) (witt_add p) :=
⟨by { introsI, refl }⟩

/-- Multiplication of Witt vectors is a polynomial function. -/
def mul_is_poly₂ [fact p.prime] : is_poly₂ p (λ _ _, by exactI (*)) (witt_mul p) :=
⟨by { introsI, refl }⟩

namespace is_poly

instance : inhabited (is_poly p (λ _ _, id) _) :=
⟨id_is_poly p⟩

variables {p}

lemma ext {f φ g ψ} (hf : is_poly p f φ) (hg : is_poly p g ψ) (h : φ = ψ) : f = g :=
by { ext R _Rcr x n, rw [hf.coeff, hg.coeff, h] }

/-- The composition of polynomial functions is polynomial. -/
def comp {g ψ f φ} (hg : is_poly p g ψ) (hf : is_poly p f φ) :
  is_poly p (λ R _Rcr, @g R _Rcr ∘ @f R _Rcr) (λ n, bind₁ φ (ψ n)) :=
⟨by { intros, simp only [aeval_bind₁, function.comp, hg.coeff, hf.coeff] }⟩

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
def comp₂ {g ψ f φ} (hg : is_poly p g ψ) (hf : is_poly₂ p f φ) :
  is_poly₂ p (λ R _Rcr x y, by exactI g (f x y)) (λ n, bind₁ φ (ψ n)) :=
⟨by { intros, simp only [peval, aeval_bind₁, function.comp, hg.coeff, hf.coeff] }⟩

include hp

lemma ext' {f φ g ψ} (hf : is_poly p f φ) (hg : is_poly p g ψ)
  (h : ∀ n, bind₁ φ (witt_polynomial p _ n) = bind₁ ψ (witt_polynomial p _ n)) :
  ∀ (R) [_Rcr : comm_ring R] (x : 𝕎 R), by exactI f x = g x :=
by { rw (is_poly.ext hf hg $ poly_eq_of_witt_polynomial_bind_eq p _ _ h), intros, refl }

end is_poly

namespace is_poly₂

instance [fact p.prime] : inhabited (is_poly₂ p _ _) :=
⟨add_is_poly₂ p⟩

variables {p}

lemma ext {f φ g ψ} (hf : is_poly₂ p f φ) (hg : is_poly₂ p g ψ) (h : φ = ψ) : f = g :=
by { ext R _Rcr x n, rw [hf.coeff, hg.coeff, h] }

/-- The composition of a binary polynomial function
with two unary polynomial functions is polynomial. -/
def comp {h χ f φ g ψ} (hh : is_poly₂ p h χ) (hf : is_poly p f φ) (hg : is_poly p g ψ) :
  is_poly₂ p (λ R _Rcr x y, by exactI h (f x) (g y))
    (λ n, bind₁ (uncurry $
            ![λ k, rename (prod.mk (0 : fin 2)) (φ k),
              λ k, rename (prod.mk (1 : fin 2)) (ψ k)]) (χ n)) :=
{ coeff :=
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
def comp_left {g ψ f φ} (hg : is_poly₂ p g ψ) (hf : is_poly p f φ) :
  is_poly₂ p (λ R _Rcr x y, by exactI g (f x) y) _ :=
hg.comp hf (id_is_poly p)

/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
def comp_right {g ψ f φ} (hg : is_poly₂ p g ψ) (hf : is_poly p f φ) :
  is_poly₂ p (λ R _Rcr x y, by exactI g x (f y)) _ :=
hg.comp (id_is_poly p) hf

def diag {f φ} (hf : is_poly₂ p f φ) :
  is_poly p (λ R _Rcr x, by exactI f x x) (λ n, bind₁ (uncurry ![X, X]) (φ n)) :=
{ coeff :=
  begin
    intros, funext n,
    simp only [hf.coeff, peval, uncurry, aeval_bind₁],
    apply eval₂_hom_congr rfl _ rfl,
    ext ⟨i, k⟩, fin_cases i;
    simp only [matrix.head_cons, aeval_X, matrix.cons_val_zero, matrix.cons_val_one],
  end }

include hp

lemma ext' {f φ g ψ} (hf : is_poly₂ p f φ) (hg : is_poly₂ p g ψ)
  (h : ∀ n, bind₁ φ (witt_polynomial p _ n) = bind₁ ψ (witt_polynomial p _ n)) :
  ∀ (R) [_Rcr : comm_ring R] (x y : 𝕎 R), by exactI f x y = g x y :=
by { rw (is_poly₂.ext hf hg $ poly_eq_of_witt_polynomial_bind_eq' p _ _ h), intros, refl }

end is_poly₂

attribute [ghost_simps]
      witt_structure_int_prop witt_add witt_mul witt_neg
      alg_hom.map_zero alg_hom.map_one bind₁_zero_witt_polynomial bind₁_one_poly_witt_polynomial
      alg_hom.map_add alg_hom.map_mul bind₁_X_right function.uncurry bind₁_rename function.comp
      matrix.head_cons matrix.cons_val_one matrix.cons_val_zero
      if_true eq_self_iff_true if_false add_zero ring_hom.map_zero
      ring_hom.map_mul alg_hom.map_mul mul_add
      ring_hom.map_nat_cast alg_hom.map_nat_cast

end witt_vector
