/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/

import data.mv_polynomial.comm_ring
import ring_theory.ideal.operations

/-!
# Quotients of polynomial rings in several variables.

We set up the basic theory of quotients of polynomial rings in several variables.

## Main definition

* `ideal.quotient.mk.alg` : given an ideal `I`, the quotient map from `(mv_polynomial σ R)`
as `R`-algebra homomorphism.

## Main results

* `ideal.quotient.mk.alg_mv_poly_surjective` : `ideal.quotient.mk.alg` is surjective
* `ideal.quotient.mk.alg_mv_poly_ker` : The kernel of `ideal.quotient.mk.alg` is `I`.

-/

noncomputable theory

namespace mv_polynomial

variables {σ : Type*} {R : Type*} [comm_ring R]

instance {I : ideal (mv_polynomial σ R)} : algebra R (ideal.quotient I) :=
(ring_hom.to_algebra (ring_hom.comp (ideal.quotient.mk I) C))

def ideal.quotient.mk.alg (σ : Type*) (I : ideal (mv_polynomial σ R)) :
  (mv_polynomial σ R) →ₐ[R] I.quotient :=
⟨λ a, submodule.quotient.mk a, rfl, λ _ _, rfl, rfl, λ _ _, rfl, λ _, rfl⟩

lemma ideal.quotient.mk.alg_to_ring_hom (σ : Type*) (I : ideal (mv_polynomial σ R)) :
  (ideal.quotient.mk.alg σ I).to_ring_hom = ideal.quotient.mk I := rfl

lemma ideal.quotient.mk.alg_mv_poly_surjective (σ : Type*) (I : ideal (mv_polynomial σ R)) :
  function.surjective (ideal.quotient.mk.alg σ I) :=
λ y, quotient.induction_on' y (λ x, exists.intro x rfl)

@[simp]
lemma ideal.quotient.mk.alg_mv_poly_ker (σ : Type*) (I : ideal (mv_polynomial σ R)) :
 (ideal.quotient.mk.alg σ I).to_ring_hom.ker = I :=
by rw [ideal.quotient.mk.alg_to_ring_hom _ _, ideal.mk_ker]

end mv_polynomial
