/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.mv_polynomial.variables

/-!
# Multivariate polynomials over a ring

Many results about polynomials hold when the coefficient ring is a commutative semiring.
Some stronger results can be derived when we assume this semiring is a ring.

This file does not define any new operations, but proves some of these stronger results.

## Notation

As in other polynomial files we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `α : Type*` `[comm_ring α]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : α`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_ring
variable [comm_ring α]
variables {p q : mv_polynomial σ α}

instance : comm_ring (mv_polynomial σ α) := add_monoid_algebra.comm_ring

instance C.is_ring_hom : is_ring_hom (C : α → mv_polynomial σ α) :=
by apply is_ring_hom.of_semiring

variables (σ a a')
@[simp] lemma C_sub : (C (a - a') : mv_polynomial σ α) = C a - C a' := is_ring_hom.map_sub _

@[simp] lemma C_neg : (C (-a) : mv_polynomial σ α) = -C a := is_ring_hom.map_neg _

@[simp] lemma coeff_neg (m : σ →₀ ℕ) (p : mv_polynomial σ α) :
  coeff m (-p) = -coeff m p := finsupp.neg_apply

@[simp] lemma coeff_sub (m : σ →₀ ℕ) (p q : mv_polynomial σ α) :
  coeff m (p - q) = coeff m p - coeff m q := finsupp.sub_apply

instance coeff.is_add_group_hom (m : σ →₀ ℕ) :
  is_add_group_hom (coeff m : mv_polynomial σ α → α) :=
{ map_add := coeff_add m }

variables {σ} (p)

section degrees

lemma degrees_neg (p : mv_polynomial σ α) : (- p).degrees = p.degrees :=
by rw [degrees, finsupp.support_neg]; refl

lemma degrees_sub (p q : mv_polynomial σ α) :
  (p - q).degrees ≤ p.degrees ⊔ q.degrees :=
le_trans (degrees_add p (-q)) $ by rw [degrees_neg]

end degrees

section vars

variables (p q)

@[simp] lemma vars_neg : (-p).vars = p.vars :=
by simp [vars, degrees_neg]

lemma vars_sub_subset : (p - q).vars ⊆ p.vars ∪ q.vars :=
by convert vars_add_subset p (-q) using 2; simp

variables {p q}

@[simp]
lemma vars_sub_of_disjoint (hpq : disjoint p.vars q.vars) : (p - q).vars = p.vars ∪ q.vars :=
begin
  rw ←vars_neg q at hpq,
  convert vars_add_of_disjoint hpq using 2,
  simp
end

end vars

section eval₂

variables [comm_ring β]
variables (f : α →+* β) (g : σ → β)

@[simp] lemma eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g := (eval₂_hom f g).map_sub _ _

@[simp] lemma eval₂_neg : (-p).eval₂ f g = -(p.eval₂ f g) := (eval₂_hom f g).map_neg _

lemma hom_C (f : mv_polynomial σ ℤ → β) [is_ring_hom f] (n : ℤ) : f (C n) = (n : β) :=
((ring_hom.of f).comp (ring_hom.of C)).eq_int_cast n

/-- A ring homomorphism f : Z[X_1, X_2, ...] → R
is determined by the evaluations f(X_1), f(X_2), ... -/
@[simp] lemma eval₂_hom_X {α : Type u} (c : ℤ →+* β)
  (f : mv_polynomial α ℤ →+* β) (x : mv_polynomial α ℤ) :
  eval₂ c (f ∘ X) x = f x :=
mv_polynomial.induction_on x
(λ n, by { rw [hom_C f, eval₂_C], exact (ring_hom.of c).eq_int_cast n })
(λ p q hp hq, by { rw [eval₂_add, hp, hq], exact (is_ring_hom.map_add f).symm })
(λ p n hp, by { rw [eval₂_mul, eval₂_X, hp], exact (is_ring_hom.map_mul f).symm })

/-- Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`, -/
def hom_equiv : (mv_polynomial σ ℤ →+* β) ≃ (σ → β) :=
{ to_fun := λ f, ⇑f ∘ X,
  inv_fun := λ f, eval₂_hom (int.cast_ring_hom β) f,
  left_inv := λ f, ring_hom.ext  $ eval₂_hom_X _ _,
  right_inv := λ f, funext $ λ x, by simp only [coe_eval₂_hom, function.comp_app, eval₂_X] }

end eval₂

section total_degree

@[simp] lemma total_degree_neg (a : mv_polynomial σ α) :
  (-a).total_degree = a.total_degree :=
by simp only [total_degree, finsupp.support_neg]

lemma total_degree_sub (a b : mv_polynomial σ α) :
  (a - b).total_degree ≤ max a.total_degree b.total_degree :=
calc (a - b).total_degree = (a + -b).total_degree                : by rw sub_eq_add_neg
                      ... ≤ max a.total_degree (-b).total_degree : total_degree_add a (-b)
                      ... = max a.total_degree b.total_degree    : by rw total_degree_neg

end total_degree

end comm_ring

end mv_polynomial
