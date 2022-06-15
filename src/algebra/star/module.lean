/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import algebra.star.self_adjoint
import algebra.module.equiv
import linear_algebra.prod

/-!
# The star operation, bundled as a star-linear equiv

We define `star_linear_equiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

This file also provides some lemmas that need `algebra.module.basic` imported to prove.

## TODO

- Define `star_linear_equiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵐᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `is_op R S` and have an instance `is_op R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵐᵒᵖ` or `is_op R S` would require adding
  the appropriate `ring_hom_inv_pair` instances to be able to define the semilinear
  equivalence.
-/

section smul_lemmas
variables {R M : Type*}

@[simp] lemma star_int_cast_smul [ring R] [add_comm_group M] [module R M] [star_add_monoid M]
  (n : ℤ) (x : M) : star ((n : R) • x) = (n : R) • star x :=
map_int_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_nat_cast_smul [semiring R] [add_comm_monoid M] [module R M] [star_add_monoid M]
  (n : ℕ) (x : M) : star ((n : R) • x) = (n : R) • star x :=
map_nat_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_inv_int_cast_smul [division_ring R] [add_comm_group M] [module R M]
  [star_add_monoid M] (n : ℤ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
map_inv_int_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_inv_nat_cast_smul [division_ring R] [add_comm_group M] [module R M]
  [star_add_monoid M] (n : ℕ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
map_inv_nat_cast_smul (star_add_equiv : M ≃+ M) R R n x

@[simp] lemma star_rat_cast_smul [division_ring R] [add_comm_group M] [module R M]
  [star_add_monoid M] (n : ℚ) (x : M) : star ((n : R) • x) = (n : R) • star x :=
map_rat_cast_smul (star_add_equiv : M ≃+ M) _ _ _ x

@[simp] lemma star_rat_smul {R : Type*} [add_comm_group R] [star_add_monoid R] [module ℚ R]
  (x : R) (n : ℚ) : star (n • x) = n • star x :=
map_rat_smul (star_add_equiv : R ≃+ R) _ _

end smul_lemmas

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps]
def star_linear_equiv (R : Type*) {A : Type*}
  [comm_ring R] [star_ring R] [semiring A] [star_ring A] [module R A] [star_module R A]  :
    A ≃ₗ⋆[R] A :=
{ to_fun := star,
  map_smul' := star_smul,
  .. star_add_equiv }

variables (R : Type*) (A : Type*)
  [semiring R] [star_semigroup R] [has_trivial_star R]
  [add_comm_group A] [module R A] [star_add_monoid A] [star_module R A]

/-- The self-adjoint elements of a star module, as a submodule. -/
def self_adjoint.submodule : submodule R A :=
{ smul_mem' := self_adjoint.smul_mem,
  ..self_adjoint A }

/-- The skew-adjoint elements of a star module, as a submodule. -/
def skew_adjoint.submodule : submodule R A :=
{ smul_mem' := skew_adjoint.smul_mem,
  ..skew_adjoint A }

variables {A} [invertible (2 : R)]

/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps] def self_adjoint_part : A →ₗ[R] self_adjoint A :=
{ to_fun := λ x, ⟨(⅟2 : R) • (x + star x),
  by simp only [self_adjoint.mem_iff, star_smul, add_comm,
                  star_add_monoid.star_add, star_inv', star_bit0,
                  star_one, star_star, star_inv_of (2 : R), star_trivial]⟩,
  map_add' := λ x y, by { ext, simp [add_add_add_comm] },
  map_smul' := λ r x, by { ext, simp [←mul_smul,
          show ⅟ 2 * r = r * ⅟ 2, from commute.inv_of_left (commute.one_left r).bit0_left] } }

/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps] def skew_adjoint_part : A →ₗ[R] skew_adjoint A :=
{ to_fun := λ x, ⟨(⅟2 : R) • (x - star x),
    by simp only [skew_adjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ←smul_neg,
                  neg_sub]⟩,
  map_add' := λ x y, by { ext, simp only [sub_add, ←smul_add, sub_sub_eq_add_sub, star_add,
                                          add_subgroup.coe_mk, add_subgroup.coe_add] },
  map_smul' := λ r x, by { ext, simp [←mul_smul, ←smul_sub,
            show r * ⅟ 2 = ⅟ 2 * r, from commute.inv_of_right (commute.one_right r).bit0_right] } }

lemma star_module.self_adjoint_part_add_skew_adjoint_part (x : A) :
  (self_adjoint_part R x : A) + skew_adjoint_part R x = x :=
by simp only [smul_sub, self_adjoint_part_apply_coe, smul_add, skew_adjoint_part_apply_coe,
              add_add_sub_cancel, inv_of_two_smul_add_inv_of_two_smul]

variables (A)

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
@[simps] def star_module.decompose_prod_adjoint : A ≃ₗ[R] self_adjoint A × skew_adjoint A :=
linear_equiv.of_linear
  ((self_adjoint_part R).prod (skew_adjoint_part R))
  ((self_adjoint.submodule R A).subtype.coprod (skew_adjoint.submodule R A).subtype)
  (by ext; simp)
  (linear_map.ext $ star_module.self_adjoint_part_add_skew_adjoint_part R)
