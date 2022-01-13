/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import algebra.module.linear_map
import linear_algebra.bilinear_map

/-!
# Sesquilinear form

This file defines a sesquilinear form over a module. The definition requires a ring antiautomorphism
on the scalar ring. Basic ideas such as
orthogonality are also introduced.

A sesquilinear form on an `R`-module `M`, is a function from `M × M` to `R`, that is linear in the
first argument and antilinear in the second, with respect to an antiautomorphism on `R` (an
antiisomorphism from `R` to `R`).

## Notations

Given any term `S` of type `sesq_form`, due to a coercion, can use the notation `S x y` to
refer to the function field, ie. `S x y = S.sesq x y`.

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/

open_locale big_operators

namespace linear_map

section comm_ring

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variables {R : Type*} {M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]
  {I : R →+* R}

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho (B : M →ₗ[R] M →ₛₗ[I] R) (x y) : Prop := B x y = 0

lemma is_ortho_def {B : M →ₗ[R] M →ₛₗ[I] R} {x y : M} :
  B.is_ortho x y ↔ B x y = 0 := iff.rfl

lemma is_ortho_zero_left (B : M →ₗ[R] M →ₛₗ[I] R) (x) : is_ortho B (0 : M) x :=
  by { dunfold is_ortho, rw [ map_zero B, zero_apply] }

lemma is_ortho_zero_right (B : M →ₗ[R] M →ₛₗ[I] R) (x) : is_ortho B x (0 : M) :=
  map_zero (B x)


end comm_ring
section is_domain

variables {R : Type*} {M : Type*} [comm_ring R] [is_domain R] [add_comm_group M]
  [module R M]
  {I : R ≃+* R}
  {B : M →ₗ[R] M →ₛₗ[I.to_ring_hom] R}


lemma ortho_smul_left {x y} {a : R} (ha : a ≠ 0) : (is_ortho B x y) ↔ (is_ortho B (a • x) y) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [map_smul, smul_apply, H, smul_zero] },
  { rw [map_smul, smul_apply, smul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }}
end

lemma ortho_smul_right {x y} {a : R} {ha : a ≠ 0} : (is_ortho B x y) ↔ (is_ortho B x (a • y)) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [map_smulₛₗ, H, smul_zero] },
  { rw [map_smulₛₗ, smul_eq_zero] at H,
    cases H,
    { rw [ring_equiv.to_ring_hom_eq_coe, ring_equiv.coe_to_ring_hom] at H,
      exfalso,
      exact ha (I.map_eq_zero_iff.mp H) },
    { exact H }}
end

end is_domain

variables {R : Type*} {M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  {I : R →+* R}
  {B : M →ₗ[R] M →ₛₗ[I] R}

/-- The proposition that a sesquilinear form is reflexive -/
def is_refl (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ (x y), B x y = 0 → B y x = 0

namespace is_refl

variable (H : B.is_refl)

lemma eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := λ x y, H x y

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := ⟨eq_zero H, eq_zero H⟩

end is_refl

/-- The proposition that a sesquilinear form is symmetric -/
def is_symm (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ (x y), (I (B x y)) = B y x

namespace is_symm

variable (H : B.is_symm)
include H

protected lemma eq (x y) : (I (B x y)) = B y x := H x y

lemma is_refl : B.is_refl := λ x y H1, by { rw [←H], simp [H1] }

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := H.is_refl.ortho_comm

end is_symm

/-- The proposition that a sesquilinear form is alternating -/
def is_alt (B : M →ₗ[R] M →ₛₗ[I] R) : Prop := ∀ (x : M), B x x = 0

namespace is_alt

variable (H : B.is_alt)
include H

lemma self_eq_zero (x) : B x x = 0 := H x

lemma neg (x y) : - B x y = B y x :=
begin
  have H1 : B (y + x) (y + x) = 0,
  { exact self_eq_zero H (y + x) },
  simp [map_add, self_eq_zero H] at H1,
  rw [add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

lemma is_refl : B.is_refl :=
begin
  intros x y h,
  rw [← neg H, h, neg_zero],
end

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := H.is_refl.ortho_comm

end is_alt

end linear_map
