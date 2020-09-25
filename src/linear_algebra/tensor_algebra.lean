/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Topaz.
-/
import algebra.free_algebra
import algebra.ring_quot

/-!
# Tensor Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the tensor algebra of `M`.
This is the free `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

1. `tensor_algebra R M` is the tensor algebra itself. It is endowed with an R-algebra structure.
2. `tensor_algebra.ι R M` is the canonical R-linear map `M → tensor_algebra R M`.
3. Given a linear map `f : M → A` to an R-algebra `A`, `lift R M f` is the lift of `f` to an
  `R`-algebra morphism `tensor_algebra R M → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R M f) ∘ (ι R M)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : tensor_algebra R M → A` is
  given whose composition with `ι R M` is `f`, then one has `g = lift R M f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.

## Implementation details

As noted above, the tensor algebra of `M` is constructed as the free `R`-algebra generated by `M`,
modulo the additional relations making the inclusion of `M` into an `R`-linear map.
-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_group M] [semimodule R M]

namespace tensor_algebra

/--
An inductively defined relation on `pre R M` used to force the initial algebra structure on
the associated quotient.
-/
inductive rel : free_algebra R M → free_algebra R M → Prop
-- force `ι` to be linear
| add {a b : M} :
  rel (free_algebra.ι R M (a+b)) (free_algebra.ι R M a + free_algebra.ι R M b)
| smul {r : R} {a : M} :
  rel (free_algebra.ι R M (r • a)) (algebra_map R (free_algebra R M) r * free_algebra.ι R M a)

end tensor_algebra

/--
The tensor algebra of the module `M` over the commutative semiring `R`.
-/
@[derive [inhabited, semiring, algebra R]]
def tensor_algebra := ring_quot (tensor_algebra.rel R M)

namespace tensor_algebra

/--
The canonical linear map `M →ₗ[R] tensor_algebra R M`.
-/
def ι : M →ₗ[R] (tensor_algebra R M) :=
{ to_fun := λ m, (ring_quot.mk_alg_hom R _ (free_algebra.ι R M m)),
  map_add' := λ x y, by { rw [←alg_hom.map_add], exact ring_quot.mk_alg_hom_rel R rel.add, },
  map_smul' := λ r x, by { rw [←alg_hom.map_smul], exact ring_quot.mk_alg_hom_rel R rel.smul, } }

lemma ring_quot_mk_alg_hom_free_algebra_ι_eq_ι (m : M) :
  ring_quot.mk_alg_hom R (rel R M) (free_algebra.ι R M m) = ι R M m := rfl

/--
Given a linear map `f : M → A` where `A` is an `R`-algebra, `lift R M f` is the unique lift
of `f` to a morphism of `R`-algebras `tensor_algebra R M → A`.
-/
def lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) : tensor_algebra R M →ₐ[R] A :=
ring_quot.lift_alg_hom R (free_algebra.lift R M ⇑f) (λ x y h, by induction h; simp [algebra.smul_def])

variables {R M}

@[simp]
theorem ι_comp_lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) :
  (lift R M f).to_linear_map.comp (ι R M) = f := by { ext, simp [lift, ι], }

@[simp]
theorem lift_ι_apply {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) (x) :
  lift R M f (ι R M x) = f x := by { dsimp [lift, ι], refl, }

@[simp]
theorem lift_unique {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (g : tensor_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R M) = f ↔ g = lift R M f :=
begin
  refine ⟨λ hyp, _, λ hyp, by rw [hyp, ι_comp_lift]⟩,
  ext,
  rw ←hyp,
  simp [lift],
  refl,
end

attribute [irreducible] tensor_algebra ι lift

@[simp]
theorem lift_comp_ι {A : Type*} [semiring A] [algebra R A] (g : tensor_algebra R M →ₐ[R] A) :
  lift R M (g.to_linear_map.comp (ι R M)) = g := by {symmetry, rw ←lift_unique}

@[ext]
theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : tensor_algebra R M →ₐ[R] A}
  (w : f.to_linear_map.comp (ι R M) = g.to_linear_map.comp (ι R M)) : f = g :=
begin
  let h := g.to_linear_map.comp (ι R M),
  have : g = lift R M h, by rw ←lift_unique,
  rw [this, ←lift_unique, w],
end

end tensor_algebra
