/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import data.mv_polynomial.rename

/-!

# Monad operations on `mv_polynomial`

This file defines two monadic operations on `mv_polynomial`. Given `p : mv_polynomial σ R`,

* `mv_polynomial.bind₁` and `mv_polynomial.join₁` operate on the variable type `σ`.
* `mv_polynomial.bind₂` and `mv_polynomial.join₂` operate on the coefficient type `R`.

- `mv_polynomial.bind₁ f φ` with `f : σ → mv_polynomial τ R` and `φ : mv_polynomial σ R`,
  is the polynomial `φ(f 1, ..., f i, ...) : mv_polynomial τ R`.
- `mv_polynomial.join₁ φ` with `φ : mv_polynomial (mv_polynomial σ R) R` collapses `φ` to
  a `mv_polynomial σ R`, by evaluating `φ` under the map `X f ↦ f` for `f : mv_polynomial σ R`.
  In other words, if you have a polynomial `φ` in a set of variables indexed by a polynomial ring,
  you evaluate the polynomial in these indexing polynomials.
- `mv_polynomial.bind₂ f φ` with `f : R →+* mv_polynomial σ S` and `φ : mv_polynomial σ R`
  is the `mv_polynomial σ S` obtained from `φ` by mapping the coefficients of `φ` through `f`
  and considering the resulting polynomial as polynomial expression in `mv_polynomial σ R`.
- `mv_polynomial.join₂ φ` with `φ : mv_polynomial σ (mv_polynomial σ R)` collapses `φ` to
  a `mv_polynomial σ R`, by considering `φ` as polynomial expression in `mv_polynomial σ R`.

These operations themselves have algebraic structure: `mv_polynomial.bind₁`
and `mv_polynomial.join₁` are algebra homs and
`mv_polynomial.bind₂` and `mv_polynomial.join₂` are ring homs.

They interact in convenient ways with `mv_polynomial.rename`, `mv_polynomial.map`,
`mv_polynomial.vars`, and other polynomial operations.
Indeed, `mv_polynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `mv_polynomial.map` is the "map" operation for the other pair.

## Implementation notes

We add an `is_lawful_monad` instance for the (`bind₁`, `join₁`) pair.
The second pair cannot be instantiated as a `monad`,
since it is not a monad in `Type` but in `CommRing` (or rather `CommSemiRing`).

-/

open_locale big_operators
noncomputable theory
namespace mv_polynomial
open finsupp

variables {σ : Type*} {τ : Type*}
variables {R S T : Type*} [comm_semiring R] [comm_semiring S] [comm_semiring T]

/--
`bind₁` is the "left hand side" bind operation on `mv_polynomial`, operating on the variable type.
Given a polynomial `p : mv_polynomial σ R` and a map `f : σ → mv_polynomial τ R` taking variables
in `p` to polynomials in the variable type `τ`, `bind₁ f p` replaces each variable in `p` with
its value under `f`, producing a new polynomial in `τ`. The coefficient type remains the same.
This operation is an algebra hom.
-/
def bind₁ (f : σ → mv_polynomial τ R) : mv_polynomial σ R →ₐ[R] mv_polynomial τ R :=
aeval f

/--
`bind₂` is the "right hand side" bind operation on `mv_polynomial`,
operating on the coefficient type.
Given a polynomial `p : mv_polynomial σ R` and
a map `f : R → mv_polynomial σ S` taking coefficients in `p` to polynomials over a new ring `S`,
`bind₂ f p` replaces each coefficient in `p` with its value under `f`,
producing a new polynomial over `S`.
The variable type remains the same. This operation is a ring hom.
-/
def bind₂ (f : R →+* mv_polynomial σ S) : mv_polynomial σ R →+* mv_polynomial σ S :=
eval₂_hom f X

/--
`join₁` is the monadic join operation corresponding to `mv_polynomial.bind₁`. Given a polynomial `p`
with coefficients in `R` whose variables are polynomials in `σ` with coefficients in `R`,
`join₁ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is an algebra hom.
-/
def join₁ : mv_polynomial (mv_polynomial σ R) R →ₐ[R] mv_polynomial σ R :=
aeval id

/--
`join₂` is the monadic join operation corresponding to `mv_polynomial.bind₂`. Given a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficients in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is a ring hom.
-/
def join₂ : mv_polynomial σ (mv_polynomial σ R) →+* mv_polynomial σ R :=
eval₂_hom (ring_hom.id _) X

@[simp] lemma aeval_eq_bind₁ (f : σ → mv_polynomial τ R) :
  aeval f = bind₁ f := rfl

@[simp] lemma eval₂_hom_C_eq_bind₁ (f : σ → mv_polynomial τ R) :
  eval₂_hom C f = bind₁ f := rfl

@[simp] lemma eval₂_hom_eq_bind₂ (f : R →+* mv_polynomial σ S) :
  eval₂_hom f X = bind₂ f := rfl

section
variables (σ R)
@[simp] lemma aeval_id_eq_join₁ :
  aeval id = @join₁ σ R _ := rfl

lemma eval₂_hom_C_id_eq_join₁ (φ : mv_polynomial (mv_polynomial σ R) R) :
  eval₂_hom C id φ = join₁ φ := rfl

@[simp] lemma eval₂_hom_id_X_eq_join₂ :
  eval₂_hom (ring_hom.id _) X = @join₂ σ R _ := rfl

end

-- In this file, we don't want to use these simp lemmas,
-- because we first need to show how these new definitions interact
-- and the proofs fall back on unfolding the definitions and call simp afterwards

local attribute [-simp] aeval_eq_bind₁ eval₂_hom_C_eq_bind₁ eval₂_hom_eq_bind₂
                        aeval_id_eq_join₁ eval₂_hom_id_X_eq_join₂

@[simp]
lemma bind₁_X_right (f : σ → mv_polynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
aeval_X f i

@[simp]
lemma bind₂_X_right (f : R →+* mv_polynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
eval₂_hom_X' f X i

@[simp]
lemma bind₁_X_left : bind₁ (X : σ → mv_polynomial σ R) = alg_hom.id R _ :=
by { ext1 i, simp }

lemma aeval_X_left : aeval (X : σ → mv_polynomial σ R) = alg_hom.id R _ :=
by rw [aeval_eq_bind₁, bind₁_X_left]

lemma aeval_X_left_apply (φ : mv_polynomial σ R) : aeval X φ = φ :=
by rw [aeval_eq_bind₁, bind₁_X_left, alg_hom.id_apply]

variable (f : σ → mv_polynomial τ R)

@[simp]
lemma bind₁_C_right (f : σ → mv_polynomial τ R) (x) : bind₁ f (C x) = C x :=
by simp [bind₁, algebra_map_eq]

@[simp]
lemma bind₂_C_right (f : R →+* mv_polynomial σ S) (r : R) : bind₂ f (C r) = f r :=
eval₂_hom_C f X r

@[simp]
lemma bind₂_C_left : bind₂ (C : R →+* mv_polynomial σ R) = ring_hom.id _ :=
by { ext : 2; simp }

@[simp]
lemma bind₂_comp_C (f : R →+* mv_polynomial σ S) :
  (bind₂ f).comp C = f :=
ring_hom.ext $ bind₂_C_right _

@[simp]
lemma join₂_map (f : R →+* mv_polynomial σ S) (φ : mv_polynomial σ R) :
  join₂ (map f φ) = bind₂ f φ :=
by simp only [join₂, bind₂, eval₂_hom_map_hom, ring_hom.id_comp]

@[simp]
lemma join₂_comp_map (f : R →+* mv_polynomial σ S) :
  join₂.comp (map f) = bind₂ f :=
ring_hom.ext $ join₂_map _

lemma aeval_id_rename (f : σ → mv_polynomial τ R) (p : mv_polynomial σ R) :
  aeval id (rename f p) = aeval f p :=
by rw [aeval_rename, function.comp.left_id]

@[simp]
lemma join₁_rename (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  join₁ (rename f φ) = bind₁ f φ :=
aeval_id_rename _ _

@[simp]
lemma bind₁_id : bind₁ (@id (mv_polynomial σ R)) = join₁ := rfl

@[simp]
lemma bind₂_id : bind₂ (ring_hom.id (mv_polynomial σ R)) = join₂ := rfl

lemma bind₁_bind₁ {υ : Type*} (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial υ R)
  (φ : mv_polynomial σ R) :
  (bind₁ g) (bind₁ f φ) = bind₁ (λ i, bind₁ g (f i)) φ :=
by simp [bind₁, ← comp_aeval]

lemma bind₁_comp_bind₁ {υ : Type*} (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial υ R) :
  (bind₁ g).comp (bind₁ f) = bind₁ (λ i, bind₁ g (f i)) :=
by { ext1, apply bind₁_bind₁ }

lemma bind₂_comp_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* mv_polynomial σ T) :
  (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) :=
by { ext : 2; simp }

lemma bind₂_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* mv_polynomial σ T)
  (φ : mv_polynomial σ R) :
  (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
ring_hom.congr_fun (bind₂_comp_bind₂ f g) φ

lemma rename_comp_bind₁ {υ : Type*} (f : σ → mv_polynomial τ R) (g : τ → υ) :
  (rename g).comp (bind₁ f) = bind₁ (λ i, rename g $ f i) :=
by { ext1 i, simp }

lemma rename_bind₁ {υ : Type*} (f : σ → mv_polynomial τ R) (g : τ → υ) (φ : mv_polynomial σ R) :
  rename g (bind₁ f φ) = bind₁ (λ i, rename g $ f i) φ :=
alg_hom.congr_fun (rename_comp_bind₁ f g) φ

lemma map_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* T) (φ : mv_polynomial σ R) :
  map g (bind₂ f φ) = bind₂ ((map g).comp f) φ :=
begin
  simp only [bind₂, eval₂_comp_right, coe_eval₂_hom, eval₂_map],
  congr' 1 with : 1,
  simp only [function.comp_app, map_X]
end

lemma bind₁_comp_rename {υ : Type*} (f : τ → mv_polynomial υ R) (g : σ → τ) :
  (bind₁ f).comp (rename g) = bind₁ (f ∘ g) :=
by { ext1 i, simp }

lemma bind₁_rename {υ : Type*} (f : τ → mv_polynomial υ R) (g : σ → τ) (φ : mv_polynomial σ R) :
  bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
alg_hom.congr_fun (bind₁_comp_rename f g) φ

lemma bind₂_map (f : S →+* mv_polynomial σ T) (g : R →+* S) (φ : mv_polynomial σ R) :
  bind₂ f (map g φ) = bind₂ (f.comp g) φ :=
by simp [bind₂]

@[simp]
lemma map_comp_C (f : R →+* S) : (map f).comp (C : R →+* mv_polynomial σ R) = C.comp f :=
by { ext1, apply map_C }

-- mixing the two monad structures
lemma hom_bind₁ (f : mv_polynomial τ R →+* S) (g : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  f (bind₁ g φ) = eval₂_hom (f.comp C) (λ i, f (g i)) φ :=
by rw [bind₁, map_aeval, algebra_map_eq]

lemma map_bind₁ (f : R →+* S) (g : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  map f (bind₁ g φ) = bind₁ (λ (i : σ), (map f) (g i)) (map f φ) :=
by { rw [hom_bind₁, map_comp_C, ← eval₂_hom_map_hom], refl }

@[simp]
lemma eval₂_hom_comp_C (f : R →+* S) (g : σ → S) :
  (eval₂_hom f g).comp C = f :=
by { ext1 r, exact eval₂_C f g r }

lemma eval₂_hom_bind₁ (f : R →+* S) (g : τ → S) (h : σ → mv_polynomial τ R)
  (φ : mv_polynomial σ R) :
  eval₂_hom f g (bind₁ h φ) = eval₂_hom f (λ i, eval₂_hom f g (h i)) φ :=
by rw [hom_bind₁, eval₂_hom_comp_C]

lemma aeval_bind₁ [algebra R S] (f : τ → S) (g : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  aeval f (bind₁ g φ) = aeval (λ i, aeval f (g i)) φ :=
eval₂_hom_bind₁ _ _ _ _

lemma aeval_comp_bind₁ [algebra R S] (f : τ → S) (g : σ → mv_polynomial τ R) :
  (aeval f).comp (bind₁ g) = aeval (λ i, aeval f (g i)) :=
by { ext1, apply aeval_bind₁ }

lemma eval₂_hom_comp_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* mv_polynomial σ S) :
  (eval₂_hom f g).comp (bind₂ h) = eval₂_hom ((eval₂_hom f g).comp h) g :=
by { ext : 2; simp }

lemma eval₂_hom_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* mv_polynomial σ S)
  (φ : mv_polynomial σ R) :
  eval₂_hom f g (bind₂ h φ) = eval₂_hom ((eval₂_hom f g).comp h) g φ :=
ring_hom.congr_fun (eval₂_hom_comp_bind₂ f g h) φ

lemma aeval_bind₂ [algebra S T] (f : σ → T) (g : R →+* mv_polynomial σ S) (φ : mv_polynomial σ R) :
  aeval f (bind₂ g φ) = eval₂_hom ((↑(aeval f : _ →ₐ[S] _) : _ →+* _).comp g) f φ :=
eval₂_hom_bind₂ _ _ _ _

lemma eval₂_hom_C_left (f : σ → mv_polynomial τ R) : eval₂_hom C f = bind₁ f := rfl

lemma bind₁_monomial (f : σ → mv_polynomial τ R) (d : σ →₀ ℕ) (r : R) :
  bind₁ f (monomial d r) = C r * ∏ i in d.support, f i ^ d i :=
by simp only [monomial_eq, alg_hom.map_mul, bind₁_C_right, finsupp.prod,
  alg_hom.map_prod, alg_hom.map_pow, bind₁_X_right]

lemma bind₂_monomial (f : R →+* mv_polynomial σ S) (d : σ →₀ ℕ) (r : R) :
  bind₂ f (monomial d r) = f r * monomial d 1 :=
by simp only [monomial_eq, ring_hom.map_mul, bind₂_C_right, finsupp.prod,
  ring_hom.map_prod, ring_hom.map_pow, bind₂_X_right, C_1, one_mul]

@[simp]
lemma bind₂_monomial_one (f : R →+* mv_polynomial σ S) (d : σ →₀ ℕ) :
  bind₂ f (monomial d 1) = monomial d 1 :=
by rw [bind₂_monomial, f.map_one, one_mul]

instance monad : monad (λ σ, mv_polynomial σ R) :=
{ map := λ α β f p, rename f p,
  pure := λ _, X,
  bind := λ _ _ p f, bind₁ f p }

instance is_lawful_functor : is_lawful_functor (λ σ, mv_polynomial σ R) :=
{ id_map := by intros; simp [(<$>)],
  comp_map := by intros; simp [(<$>)] }

instance is_lawful_monad : is_lawful_monad (λ σ, mv_polynomial σ R) :=
{ pure_bind := by intros; simp [pure, bind],
  bind_assoc := by intros; simp [bind, ← bind₁_comp_bind₁] }

/-
Possible TODO for the future:
Enable the following definitions, and write a lot of supporting lemmas.

def bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) :
  mv_polynomial σ R →+* mv_polynomial τ S :=
eval₂_hom f g

def join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomial σ S :=
aeval (map f)

def ajoin [algebra R S] : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomial σ S :=
join (algebra_map R S)

-/

end mv_polynomial
