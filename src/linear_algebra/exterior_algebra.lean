/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser.
-/

import algebra.ring_quot
import linear_algebra.tensor_algebra
import group_theory.perm.sign

/-!
# Exterior Algebras

We construct the exterior algebra of a semimodule `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-semimodule `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Implementation details

The exterior algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `exterior_algebra.rel R M` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `0`.
2. The exterior algebra is the quotient of the tensor algebra by this relation.

-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]

namespace exterior_algebra
open tensor_algebra

/-- `rel` relates each `ι m * ι m`, for `m : M`, with `0`.

The exterior algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel ((ι R m) * (ι R m)) 0

end exterior_algebra

/--
The exterior algebra of an `R`-semimodule `M`.
-/
@[derive [inhabited, semiring, algebra R]]
def exterior_algebra := ring_quot (exterior_algebra.rel R M)

namespace exterior_algebra

variables {M}

/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
def ι : M →ₗ[R] exterior_algebra R M :=
(ring_quot.mk_alg_hom R _).to_linear_map.comp (tensor_algebra.ι R)


variables {R}

/-- As well as being linear, `ι m` squares to zero -/
@[simp]
theorem ι_square_zero (m : M) : (ι R m) * (ι R m) = 0 :=
begin
  dsimp [ι],
  rw [←alg_hom.map_mul, ←alg_hom.map_zero _],
  exact ring_quot.mk_alg_hom_rel R (rel.of m),
end

variables (R) {A : Type*} [semiring A] [algebra R A]

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
def lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) : exterior_algebra R M →ₐ[R] A :=
ring_quot.lift_alg_hom R (tensor_algebra.lift R f)
  (λ x y h, by {
    induction h,
    rw [alg_hom.map_zero, alg_hom.map_mul, tensor_algebra.lift_ι_apply, cond] })

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
  (lift R f cond).to_linear_map.comp (ι R) = f :=
by { ext, simp [lift, ι] }

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) :
  lift R f cond (ι R x) = f x :=
by { dsimp [lift, ι], rw tensor_algebra.lift_ι_apply }

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0)
  (g : exterior_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R) = f ↔ g = lift R f cond :=
begin
  refine ⟨_, λ hyp, by rw [hyp, ι_comp_lift]⟩,
  rintro rfl,
  ext,
  simp [lift],
  refl,
end

attribute [irreducible] exterior_algebra ι lift

variables {R M}

@[simp]
theorem comp_ι_square_zero (g : exterior_algebra R M →ₐ[R] A)
  (m : M) : g (ι R m) * g (ι R m) = 0 :=
by rw [←alg_hom.map_mul, ι_square_zero, alg_hom.map_zero]

@[simp]
theorem lift_comp_ι (g : exterior_algebra R M →ₐ[R] A) :
  lift R (g.to_linear_map.comp (ι R)) (comp_ι_square_zero _) = g :=
by { symmetry, rw ←lift_unique, }

@[ext]
theorem hom_ext {f g : exterior_algebra R M →ₐ[R] A} :
  f.to_linear_map.comp (ι R) = g.to_linear_map.comp (ι R) → f = g :=
begin
  intro hyp,
  let h := g.to_linear_map.comp (ι R),
  have : g = lift R h (comp_ι_square_zero _), by rw ←lift_unique,
  rw [this, ←lift_unique, hyp],
end

end exterior_algebra
