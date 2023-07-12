/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.hom

/-!
# The R-algebra structure on products of R-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

## Main defintions

* `pi.algebra`
* `pi.eval_alg_hom`
* `pi.const_alg_hom`
-/

variables {R A B C : Type*}
variables [comm_semiring R]
variables [semiring A] [algebra R A] [semiring B] [algebra R B] [semiring C] [algebra R C]

namespace prod
variables (R A B)

open algebra

instance algebra : algebra R (A × B) :=
{ commutes' := by { rintro r ⟨a, b⟩, dsimp, rw [commutes r a, commutes r b] },
  smul_def' := by { rintro r ⟨a, b⟩, dsimp, rw [algebra.smul_def r a, algebra.smul_def r b] },
  .. prod.module,
  .. ring_hom.prod (algebra_map R A) (algebra_map R B) }

variables {R A B}

@[simp] lemma algebra_map_apply (r : R) :
  algebra_map R (A × B) r = (algebra_map R A r, algebra_map R B r) := rfl

end prod

namespace alg_hom
variables (R A B)

/-- First projection as `alg_hom`. -/
def fst : A × B →ₐ[R] A :=
{ commutes' := λ r, rfl, .. ring_hom.fst A B}

/-- Second projection as `alg_hom`. -/
def snd : A × B →ₐ[R] B :=
{ commutes' := λ r, rfl, .. ring_hom.snd A B}

variables {R A B}

/-- The `pi.prod` of two morphisms is a morphism. -/
@[simps] def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (A →ₐ[R] B × C) :=
{ commutes' := λ r, by simp only [to_ring_hom_eq_coe, ring_hom.to_fun_eq_coe, ring_hom.prod_apply,
    coe_to_ring_hom, commutes, prod.algebra_map_apply],
  .. (f.to_ring_hom.prod g.to_ring_hom) }

lemma coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.prod g) = pi.prod f g := rfl

@[simp] theorem fst_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) :
  (fst R B C).comp (prod f g) = f := by ext; refl

@[simp] theorem snd_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) :
  (snd R B C).comp (prod f g) = g := by ext; refl

@[simp] theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
fun_like.coe_injective pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps] def prod_equiv : ((A →ₐ[R] B) × (A →ₐ[R] C)) ≃ (A →ₐ[R] B × C) :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ((fst _ _ _).comp f, (snd _ _ _).comp f),
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

end alg_hom
