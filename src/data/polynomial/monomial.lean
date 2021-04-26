/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.coeff

/-!
# Univariate monomials

Preparatory lemmas for degree_basic.
-/

noncomputable theory

open finsupp

namespace polynomial

universes u
variables {R : Type u} {a b : R} {m n : ℕ}
variables [semiring R] {p q r : polynomial R}

@[simp] lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp] lemma monomial_mul_C : monomial n a * C b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, add_zero]

instance [nontrivial R] : infinite (polynomial R) :=
infinite.of_injective (λ i, monomial i 1)
begin
  intros m n h,
  have := (single_eq_single_iff _ _ _ _).mp h,
  simpa only [and_true, eq_self_iff_true, or_false, one_ne_zero, and_self],
end

lemma ring_hom_ext {S} [semiring S] {f g : polynomial R →+* S}
  (h₁ : ∀ a, f (C a) = g (C a)) (h₂ : f X = g X) : f = g :=
by { ext, exacts [h₁ _, h₂] }

@[ext] lemma ring_hom_ext' {S} [semiring S] {f g : polynomial R →+* S}
  (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g :=
ring_hom_ext (ring_hom.congr_fun h₁) h₂

end polynomial
