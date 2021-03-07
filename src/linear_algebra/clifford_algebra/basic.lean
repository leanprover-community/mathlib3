/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song.
-/

import algebra.ring_quot
import linear_algebra.tensor_algebra
import linear_algebra.exterior_algebra
import linear_algebra.quadratic_form

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic_form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic_form `Q` is denoted as
`clifford_algebra Q`.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebra_map _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism, which is denoted `clifford_algebra.lift Q f cond`.

The canonical linear map `M → clifford_algebra Q` is denoted `clifford_algebra.ι Q`.

## Theorems

The main theorems proved ensure that `clifford_algebra Q` satisfies the universal property
of the Clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι Q` with `lift Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift Q f cond` with respect to 1.

Additionally, when `Q = 0` an `alg_equiv` to the `exterior_algebra` is provided as `as_exterior`.

## Implementation details

The Clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `clifford_algebra.rel Q` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The Clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `linear_algebra/exterior_algebra.lean`.
-/

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

variable {n : ℕ}

namespace clifford_algebra
open tensor_algebra

/-- `rel` relates each `ι m * ι m`, for `m : M`, with `Q m`.

The Clifford algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel (ι R m * ι R m) (algebra_map R _ (Q m))

end clifford_algebra

/--
The Clifford algebra of an `R`-module `M` equipped with a quadratic_form `Q`.
-/
@[derive [inhabited, ring, algebra R]]
def clifford_algebra := ring_quot (clifford_algebra.rel Q)

namespace clifford_algebra

/--
The canonical linear map `M →ₗ[R] clifford_algebra Q`.
-/
def ι : M →ₗ[R] clifford_algebra Q :=
(ring_quot.mk_alg_hom R _).to_linear_map.comp (tensor_algebra.ι R)

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp]
theorem ι_square_scalar (m : M) : ι Q m * ι Q m = algebra_map R _ (Q m) :=
begin
  erw [←alg_hom.map_mul, ring_quot.mk_alg_hom_rel R (rel.of m), alg_hom.commutes],
  refl,
end

variables {Q} {A : Type*} [semiring A] [algebra R A]

@[simp]
theorem comp_ι_square_scalar (g : clifford_algebra Q →ₐ[R] A) (m : M) :
  g (ι Q m) * g (ι Q m) = algebra_map _ _ (Q m) :=
by rw [←alg_hom.map_mul, ι_square_scalar, alg_hom.commutes]

variables (Q)

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `clifford_algebra Q` to `A`.
-/
@[simps symm_apply]
def lift :
  {f : M →ₗ[R] A // ∀ m, f m * f m = algebra_map _ _ (Q m)} ≃ (clifford_algebra Q →ₐ[R] A) :=
{ to_fun := λ f,
  ring_quot.lift_alg_hom R ⟨tensor_algebra.lift R (f : M →ₗ[R] A),
    (λ x y (h : rel Q x y), by {
      induction h,
      rw [alg_hom.commutes, alg_hom.map_mul, tensor_algebra.lift_ι_apply, f.prop], })⟩,
  inv_fun := λ F, ⟨F.to_linear_map.comp (ι Q), λ m, by rw [
    linear_map.comp_apply, alg_hom.to_linear_map_apply, comp_ι_square_scalar]⟩,
  left_inv := λ f, by { ext, simp [ι] },
  right_inv := λ F, by { ext, simp [ι] } }

variables {Q}

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) :
  (lift Q ⟨f, cond⟩).to_linear_map.comp (ι Q) = f :=
(subtype.mk_eq_mk.mp $ (lift Q).symm_apply_apply ⟨f, cond⟩)

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) (x) :
  lift Q ⟨f, cond⟩ (ι Q x) = f x :=
(linear_map.ext_iff.mp $ ι_comp_lift f cond) x

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m : M, f m * f m = algebra_map _ _ (Q m))
  (g : clifford_algebra Q →ₐ[R] A) :
  g.to_linear_map.comp (ι Q) = f ↔ g = lift Q ⟨f, cond⟩ :=
begin
  convert (lift Q).symm_apply_eq,
  rw lift_symm_apply,
  simp only,
end

attribute [irreducible] clifford_algebra ι lift

@[simp]
theorem lift_comp_ι (g : clifford_algebra Q →ₐ[R] A) :
  lift Q ⟨g.to_linear_map.comp (ι Q), comp_ι_square_scalar _⟩ = g :=
begin
  convert (lift Q).apply_symm_apply g,
  rw lift_symm_apply,
  refl,
end

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : clifford_algebra Q →ₐ[R] A} :
  f.to_linear_map.comp (ι Q) = g.to_linear_map.comp (ι Q) → f = g :=
begin
  intro h,
  apply (lift Q).symm.injective,
  rw [lift_symm_apply, lift_symm_apply],
  simp only [h],
end

/-- If `C` holds for the `algebra_map` of `r : R` into `clifford_algebra Q`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `clifford_algebra Q`.
-/
-- This proof closely follows `tensor_algebra.induction`
@[elab_as_eliminator]
lemma induction {C : clifford_algebra Q → Prop}
  (h_grade0 : ∀ r, C (algebra_map R (clifford_algebra Q) r))
  (h_grade1 : ∀ x, C (ι Q x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b))
  (a : clifford_algebra Q) :
  C a :=
begin
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : subalgebra R (clifford_algebra Q) := {
    carrier := C,
    mul_mem' := h_mul,
    add_mem' := h_add,
    algebra_map_mem' := h_grade0, },
  let of : { f : M →ₗ[R] s // ∀ m, f m * f m = algebra_map _ _ (Q m) } :=
  ⟨(ι Q).cod_restrict s.to_submodule h_grade1,
    λ m, subtype.eq $ ι_square_scalar Q m ⟩,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (clifford_algebra Q) = s.val.comp (lift Q of),
  { ext,
    simp [of], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift Q of a),
  exact alg_hom.congr_fun of_id a,
end

/-- A Clifford algebra with a zero quadratic form is isomorphic to an `exterior_algebra` -/
def as_exterior : clifford_algebra (0 : quadratic_form R M) ≃ₐ[R] exterior_algebra R M :=
alg_equiv.of_alg_hom
  (clifford_algebra.lift 0 ⟨(exterior_algebra.ι R), by simp⟩)
  (exterior_algebra.lift R ⟨(ι (0 : quadratic_form R M)), by simp⟩)
  (by { ext, simp, })
  (by { ext, simp, })

end clifford_algebra

namespace tensor_algebra

variables {Q}

/-- The canonical image of the `tensor_algebra` in the `clifford_algebra`, which maps
`tensor_algebra.ι R x` to `clifford_algebra.ι Q x`. -/
def to_clifford : tensor_algebra R M →ₐ[R] clifford_algebra Q :=
tensor_algebra.lift R (clifford_algebra.ι Q)

@[simp] lemma to_clifford_ι (m : M) : (tensor_algebra.ι R m).to_clifford = clifford_algebra.ι Q m :=
by simp [to_clifford]

end tensor_algebra
