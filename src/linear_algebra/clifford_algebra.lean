/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song.
-/

import algebra.ring_quot
import linear_algebra.tensor_algebra
import linear_algebra.quadratic_form

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic_form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic_form `Q` is denoted as
`clifford_algebra R M Q`.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebra_map _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism, which is denoted `clifford_algebra.lift R Q f cond`.

The canonical linear map `M → clifford_algebra R M Q` is denoted `clifford_algebra.ι R Q`.

## Theorems

The main theorems proved ensure that `clifford_algebra R M Q` satisfies the universal property
of the clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι R Q` with `lift R Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R Q f cond` with respect to 1.

## Implementation details

The clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `clifford_algebra.rel R M Q` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `linear_algebra/exterior_algebra.lean`.
Indeed, the exterior algebra can be recovered by setting `Q` to `0`.
-/

variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

variable {n : ℕ}

namespace clifford_algebra
open tensor_algebra

/-- `rel` relates each `ι m * ι m`, for `m : M`, with `Q m`.

The clifford algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel (ι R m * ι R m) (algebra_map R _ (Q m))

end clifford_algebra

/--
The Clifford algebra of an `R`-module `M` equipped with a quadratic_form `Q`.
-/
@[derive [inhabited, semiring, algebra R]]
def clifford_algebra := ring_quot (clifford_algebra.rel R M Q)

namespace clifford_algebra

variables {M}

/-
The canonical linear map `M →ₗ[R] clifford_algebra R M Q`.
-/
def ι : M →ₗ[R] clifford_algebra R M Q :=
(ring_quot.mk_alg_hom R _).to_linear_map.comp (tensor_algebra.ι R)

variables {R}

/-- As well as being linear, `ι m` squares to the quadratic form -/
@[simp]
theorem ι_square_scalar (m : M) : ι R Q m * ι R Q m = algebra_map R _ (Q m) :=
begin
  dsimp [ι],
  rw ←alg_hom.map_mul,
  rw ring_quot.mk_alg_hom_rel R (rel.of m),
  rw alg_hom.commutes,
  refl,
end

variables (R) {A : Type*} [semiring A] [algebra R A]

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `clifford_algebra R M Q` to `A`.
-/
def lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) :
  clifford_algebra R M Q →ₐ[R] A :=
ring_quot.lift_alg_hom R (tensor_algebra.lift R f)
  (λ x y h, by {
    induction h,
    rw [alg_hom.commutes, alg_hom.map_mul, tensor_algebra.lift_ι_apply, cond], })

variables {R M Q}

/-
TODO: theorems
-/
@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) :
  (lift R Q f cond).to_linear_map.comp (ι R Q) = f :=
by { ext, simp [lift, ι] }

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) (x) :
  lift R Q f cond (ι R Q x) = f x :=
by { dsimp [lift, ι], rw tensor_algebra.lift_ι_apply }

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m : M, f m * f m = algebra_map _ _ (Q m))
(g : clifford_algebra R M Q →ₐ[R] A) :
  g.to_linear_map.comp (ι R Q) = f ↔ g = lift R Q f cond :=
begin
  refine ⟨_, λ hyp, by rw [hyp, ι_comp_lift]⟩,
  rintro rfl,
  ext,
  simp [lift],
  refl,
end

attribute [irreducible] clifford_algebra ι lift

@[simp]
theorem comp_ι_square_scalar (g : clifford_algebra R M Q →ₐ[R] A) (m : M) :
  g (ι R Q m) * g (ι R Q m) = algebra_map _ _ (Q m) :=
by rw [←alg_hom.map_mul, ι_square_scalar, alg_hom.commutes]

@[simp]
theorem lift_comp_ι (g : clifford_algebra R M Q →ₐ[R] A) :
  lift R Q (g.to_linear_map.comp (ι R Q)) (comp_ι_square_scalar _) = g :=
by {symmetry, rw ←lift_unique}

theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : clifford_algebra R M Q →ₐ[R] A} :
  f.to_linear_map.comp (ι R Q) = g.to_linear_map.comp (ι R Q) → f = g :=
begin
  intro hyp,
  let h := g.to_linear_map.comp (ι R Q),
  have : g = lift R Q h (comp_ι_square_scalar _), by rw ←lift_unique,
  rw [this, ←lift_unique, hyp],
end

end clifford_algebra
