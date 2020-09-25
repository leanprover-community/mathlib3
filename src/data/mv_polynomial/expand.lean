/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import data.mv_polynomial.monad

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `mv_polynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `mv_polynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

open_locale big_operators

namespace mv_polynomial

variables {σ τ R S : Type*} [comm_semiring R] [comm_semiring S]

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `polynomial.expand`. -/
noncomputable def expand (p : ℕ) : mv_polynomial σ R →ₐ[R] mv_polynomial σ R :=
{ commutes' := λ r, eval₂_hom_C _ _ _,
  .. (eval₂_hom C (λ i, (X i) ^ p) : mv_polynomial σ R →+* mv_polynomial σ R) }

@[simp] lemma expand_C (p : ℕ) (r : R) : expand p (C r : mv_polynomial σ R) = C r :=
eval₂_hom_C _ _ _

@[simp] lemma expand_X (p : ℕ) (i : σ) : expand p (X i : mv_polynomial σ R) = X i ^ p :=
eval₂_hom_X' _ _ _

@[simp] lemma expand_monomial (p : ℕ) (d : σ →₀ ℕ) (r : R) :
  expand p (monomial d r) = C r * ∏ i in d.support, (X i ^ p) ^ d i :=
bind₁_monomial _ _ _

lemma expand_one_apply (f : mv_polynomial σ R) : expand 1 f = f :=
by simp only [expand, bind₁_X_left, alg_hom.id_apply, ring_hom.to_fun_eq_coe,
  eval₂_hom_C_left, alg_hom.coe_to_ring_hom, pow_one, alg_hom.coe_mk]

@[simp] lemma expand_one : expand 1 = alg_hom.id R (mv_polynomial σ R) :=
by { ext1 f, rw [expand_one_apply, alg_hom.id_apply] }

lemma expand_comp_bind₁ (p : ℕ) (f : σ → mv_polynomial τ R) :
  (expand p).comp (bind₁ f) = bind₁ (λ i, expand p (f i)) :=
by { apply alg_hom_ext, intro i, simp only [alg_hom.comp_apply, bind₁_X_right], }

lemma expand_bind₁ (p : ℕ) (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  expand p (bind₁ f φ) = bind₁ (λ i, expand p (f i)) φ :=
by rw [← alg_hom.comp_apply, expand_comp_bind₁]

@[simp]
lemma map_expand (f : R →+* S) (p : ℕ) (φ : mv_polynomial σ R) :
  map f (expand p φ) = expand p (map f φ) :=
by simp [expand, map_bind₁]

@[simp]
lemma rename_expand (f : σ → τ) (p : ℕ) (φ : mv_polynomial σ R) :
  rename f (expand p φ) = expand p (rename f φ) :=
by simp [expand, bind₁_rename, rename_bind₁]

@[simp] lemma rename_comp_expand (f : σ → τ) (p : ℕ) :
  (rename f).comp (expand p) =
    (expand p).comp (rename f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) :=
by { ext1 φ, simp only [rename_expand, alg_hom.comp_apply] }

end mv_polynomial
