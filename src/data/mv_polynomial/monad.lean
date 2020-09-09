/-
Copyright (c) 2020 Johan Commelin and Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin and Robert Y. Lewis
-/

import data.mv_polynomial.rename

/-!

# Monad operations on `mv_polynomial`

This file defines two monadic operations on `mv_polynomial`. Given `p : mv_polynomial σ R`,

* `mv_polynomial.bind₁` and `mv_polynomial.join₁` operate on the variable type `σ`.
* `mv_polynomial.bind₂` and `mv_polynomial.join₂` operate on the coefficient type `R`.

These operations themselves have algebraic structure: `bind₁` and `join₁` are algebra homs and
`bind₂` and `join₂` are ring homs.

They interact in convenient ways with `mv_polynomial.rename`, `mv_polynomial.map`,
`mv_polynomial.vars`, and other polynomial operations.
Indeed, `mv_polynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `mv_polynomial.map` is the "map" operation for the other pair.

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
`bind₂` is the "right hand side" bind operation on `mv_polynomial`, operating on the coefficient type.
Given a polynomial `p : mv_polynomial σ R` and a map `f : R → mv_polynomial σ S` taking coefficients
in `p` to polynomials over a new ring `S`, `bind₂ f p` replaces each coefficient in `p` with its
value under `f`, producing a new polynomial over `S`. The variable type remains the same.
This operation is a ring hom.
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
aeval (ring_hom.id _)

/--
`join₂` is the monadic join operation corresponding to `mv_polynomial.bind₂`. Given a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficients in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is a ring hom.
-/
def join₂ : mv_polynomial σ (mv_polynomial σ R) →+* mv_polynomial σ R :=
eval₂_hom (ring_hom.id _) X

@[simp] lemma aeval_X_left (φ : mv_polynomial σ R) : aeval X φ = φ :=
begin
  apply φ.induction_on,
  { intro, rw aeval_C, refl },
  { intros p q hp hq, simp only [hp, hq, alg_hom.map_add] },
  { intros p n hp, simp only [hp, aeval_X, alg_hom.map_mul] }
end

@[simp]
lemma bind₁_X_left : bind₁ (X : σ → mv_polynomial σ R) = alg_hom.id R _ :=
by ext1; simp [bind₁]

@[simp]
lemma bind₁_X_right (f : σ → mv_polynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
aeval_X f i

@[simp]
lemma bind₂_X_right (f : R →+* mv_polynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
eval₂_hom_X' f X i

variable (f : σ → mv_polynomial τ R)

@[simp]
lemma bind₁_C_right (f : σ → mv_polynomial τ R) (x) : bind₁ f (C x) = C x :=
by simp [bind₁, C, aeval_monomial, finsupp.prod_zero_index]; refl

@[simp]
lemma bind₂_C_left : bind₂ (C : R →+* mv_polynomial σ R) = ring_hom.id _ :=
by ext1; simp [bind₂]

@[simp]
lemma bind₂_C_right (f : R →+* mv_polynomial σ S) (r : R) : bind₂ f (C r) = f r :=
eval₂_hom_C f X r

@[simp]
lemma bind₂_comp_C (f : R →+* mv_polynomial σ S) :
  (bind₂ f).comp C = f :=
by { ext1, apply bind₂_C_right }

@[simp]
lemma join₂_map (f : R →+* mv_polynomial σ S) (φ : mv_polynomial σ R) :
  join₂ (map f φ) = bind₂ f φ :=
by simp only [join₂, bind₂, eval₂_hom_map_hom, ring_hom.id_comp]

@[simp]
lemma join₂_comp_map (f : R →+* mv_polynomial σ S) :
  join₂.comp (map f) = bind₂ f :=
by ext1; simp [join₂, bind₂]

@[simp] lemma aeval_rename (f : σ → mv_polynomial τ R) (p : mv_polynomial σ R) :
  aeval (ring_hom.id (mv_polynomial τ R)) (rename f p) = aeval f p :=
begin
  apply p.induction_on,
  { simp only [aeval_C, forall_const, eq_self_iff_true, rename_C] },
  { intros p q hp hq, simp only [hp, hq, alg_hom.map_add, ring_hom.map_add] },
  { intros p n hp, simp only [hp, rename_X, ring_hom.id_apply, aeval_X, ring_hom.map_mul,
                              alg_hom.map_mul] }
end

@[simp]
lemma join₁_rename (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  join₁ (rename f φ) = bind₁ f φ :=
by simp [join₁, bind₁]

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

lemma bind₂_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* mv_polynomial σ T) (φ : mv_polynomial σ R) :
  (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
begin
  dsimp [bind₂],
  apply φ.induction_on,
  { simp },
  { intros p q hp hq, simp only [hp, hq, eval₂_add] },
  { intros p n hp, simp only [hp, eval₂_mul, eval₂_X] }
end

lemma bind₂_comp_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* mv_polynomial σ T) :
  (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) :=
by { ext1, simp only [function.comp_app, ring_hom.coe_comp, bind₂_bind₂], }

lemma rename_bind₁ {υ : Type*} (f : σ → mv_polynomial τ R) (g : τ → υ) (φ : mv_polynomial σ R) :
  rename g (bind₁ f φ) = bind₁ (λ i, rename g $ f i) φ :=
begin
  apply φ.induction_on,
  { intro a, simp },
  { intros p q hp hq, simp [hp, hq] },
  { intros p n hp, simp [hp] }
end

lemma map_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* T) (φ : mv_polynomial σ R) :
  map g (bind₂ f φ) = bind₂ ((map g).comp f) φ :=
begin
  simp only [bind₂, eval₂_comp_right, coe_eval₂_hom, eval₂_map],
  congr' 1 with : 1,
  simp only [function.comp_app, map_X]
end

lemma bind₁_rename {υ : Type*} (f : τ → mv_polynomial υ R) (g : σ → τ) (φ : mv_polynomial σ R) :
  bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
begin
  dsimp [bind₁],
  apply φ.induction_on,
  { simp },
  { intros p q hp hq, simp only [hp, hq, alg_hom.map_add, ring_hom.map_add] },
  { intros p n hp, simp only [hp, rename_X, aeval_X, ring_hom.map_mul, alg_hom.map_mul] }
end

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

end mv_polynomial
