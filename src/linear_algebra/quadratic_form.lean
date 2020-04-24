/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen

Quadratic forms over modules.
-/

import algebra.invertible
import linear_algebra.bilinear_form
import linear_algebra.determinant
import linear_algebra.special_linear_group

/-!
# Quadratic forms

This file defines quadratic forms over a `R`-module `M`.
A quadratic form is a map `Q : M → R` such that
  (`to_fun_smul`) `Q (a • x) = a * a * Q x`
  (`polar_...`) The map `polar Q := λ x y, Q (x + y) - Q x - Q y` is bilinear.
They come with a scalar multiplication, `(a • Q) x = Q (a • x) = a * a * Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `quadratic_form.associated`: associated bilinear form
 * `quadratic_form.pos_def`: positive definite quadratic forms
 * `quadratic_form.discr`: discriminant of a quadratic form

## Main statements

 * `quadratic_form.associated_left_inverse`,
 * `quadratic_form.associated_right_inverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic forms and symmetric
  bilinear forms

## Notation

In this file, the variable `R` is used when a `ring` structure is sufficient and
`R₁` is used when specifically a `comm_ring` is required. This allows us to keep
`[module R M]` and `[module R₁ M]` assumptions in the variables without
confusion between `*` from `ring` and `*` from `comm_ring`.


## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic form, homogeneous polynomial, quadratic polynomial
-/

universes u v w
variables {R : Type u} {M : Type v} [add_comm_group M] [ring R]
variables {R₁ : Type u} [comm_ring R₁] [module R₁ M]

/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.d

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def quadratic_form.polar (f : M → R) (x y : M) :=
f (x + y) - f x - f y

variables [module R M]

open quadratic_form
/-- A quadratic form over a module. -/
structure quadratic_form (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] :=
(to_fun : M → R)
(to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x)
(polar_add_left : ∀ (x x' y : M), polar to_fun (x + x') y = polar to_fun x y + polar to_fun x' y)
(polar_smul_left : ∀ (a : R) (x y : M), polar to_fun (a • x) y = a • polar to_fun x y)
(polar_add_right : ∀ (x y y' : M), polar to_fun x (y + y') = polar to_fun x y + polar to_fun x y')
(polar_smul_right : ∀ (a : R) (x y : M), polar to_fun x (a • y) = a • polar to_fun x y)

namespace quadratic_form

variables {Q : quadratic_form R M}

instance : has_coe_to_fun (quadratic_form R M) :=
⟨_, λ B, B.to_fun⟩

/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp] lemma to_fun_eq_apply : Q.to_fun = ⇑ Q := rfl

lemma map_smul (a : R) (x : M) : Q (a • x) = a * a * Q x := Q.to_fun_smul a x

lemma map_add_self (x : M) : Q (x + x) = 4 * Q x :=
by { rw [←one_smul R x, ←add_smul, map_smul], norm_num }

lemma map_zero : Q 0 = 0 :=
by rw [←@zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]

lemma map_neg (x : M) : Q (-x) = Q x :=
by rw [←@neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_neg, one_mul]

lemma map_sub (x y : M) : Q (x - y) = Q (y - x) :=
by rw [←neg_sub, map_neg]

variable {Q' : quadratic_form R M}
@[ext] lemma ext (H : ∀ (x : M), Q x = Q' x) : Q = Q' :=
by { cases Q, cases Q', congr, funext, apply H }

instance : has_zero (quadratic_form R M) :=
⟨ { to_fun := λ x, 0,
    to_fun_smul := λ a x, by simp,
    polar_add_left := λ x x' y, by simp [polar],
    polar_smul_left := λ a x y, by simp [polar],
    polar_add_right := λ x y y', by simp [polar],
    polar_smul_right := λ a x y, by simp [polar] } ⟩

instance : inhabited (quadratic_form R M) := ⟨0⟩

instance : has_scalar R₁ (quadratic_form R₁ M) :=
⟨ λ a Q,
  { to_fun := λ x, Q (a • x),
    to_fun_smul := λ b x, by rw [smul_comm, map_smul],
    polar_add_left := λ x x' y,
      by convert Q.polar_add_left (a • x) (a • x') (a • y) using 1; simp [polar, smul_add],
    polar_smul_left := λ b x y,
      by convert Q.polar_smul_left b (a • x) (a • y) using 1; simp [polar, smul_add, smul_comm],
    polar_add_right := λ x y y',
      by convert Q.polar_add_right (a • x) (a • y) (a • y') using 1; simp [polar, smul_add],
    polar_smul_right := λ b x y,
      by convert Q.polar_smul_right b (a • x) (a • y) using 1; simp [polar, smul_add, smul_comm] } ⟩

@[simp] lemma smul_apply (a : R₁) (Q : quadratic_form R₁ M) (x : M) : (a • Q) x = Q (a • x) := rfl

instance : mul_action R₁ (quadratic_form R₁ M) :=
{ mul_smul := λ a b Q, ext (λ x, by simp [mul_smul, smul_comm]),
  one_smul := λ Q, ext (λ x, by simp),
  ..quadratic_form.has_scalar }

section comp

variables {N : Type v} [add_comm_group N] [module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : quadratic_form R N) (f : M →ₗ[R] N) :
  quadratic_form R M :=
{ to_fun := λ x, Q (f x),
  to_fun_smul := λ a x, by simp [map_smul],
  polar_add_left := λ x x' y,
    by convert Q.polar_add_left (f x) (f x') (f y) using 1; simp [polar],
  polar_smul_left := λ a x y,
    by convert Q.polar_smul_left a (f x) (f y) using 1; simp [polar],
  polar_add_right := λ x y y',
    by convert Q.polar_add_right (f x) (f y) (f y') using 1; simp [polar],
  polar_smul_right := λ a x y,
    by convert Q.polar_smul_right a (f x) (f y) using 1; simp [polar] }

@[simp] lemma comp_apply (Q : quadratic_form R N) (f : M →ₗ[R] N) (x : M) :
  (Q.comp f) x = Q (f x) := rfl

end comp

end quadratic_form

/-! ### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/

variables {B : bilin_form R M}

namespace bilin_form
open quadratic_form

lemma polar_to_quadratic_form (x y : M) : polar (λ x, B x x) x y = B x y + B y x :=
by simp [polar, add_left, add_right, sub_eq_add_neg _ (B y y), add_comm (B y x) _]

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def to_quadratic_form (B : bilin_form R M) : quadratic_form R M :=
⟨ λ x, B x x,
  λ a x, by simp [smul_left, smul_right, mul_assoc],
  λ x x' y, by simp [polar_to_quadratic_form, add_left, add_right, add_left_comm],
  λ a x y, by simp [polar_to_quadratic_form, smul_left, smul_right, mul_add],
  λ x y y', by simp [polar_to_quadratic_form, add_left, add_right, add_left_comm],
  λ a x y, by simp [polar_to_quadratic_form, smul_left, smul_right, mul_add] ⟩

@[simp] lemma to_quadratic_form_apply (B : bilin_form R M) (x : M) :
B.to_quadratic_form x = B x x :=
rfl

end bilin_form

namespace quadratic_form
open bilin_form sym_bilin_form

section associated
variables [invertible (2 : R₁)] {B₁ : bilin_form R₁ M} (Q : quadratic_form R₁ M)

/-- `Q.associated` is the symmetric bilinear form associated to a quadratic form `Q`. -/
def associated : bilin_form R₁ M :=
{ bilin := λ x y, ⅟2 * polar Q x y,
  bilin_add_left := λ x y z, by { erw [← mul_add, Q.polar_add_left], refl },
  bilin_smul_left := λ x y z, by { erw [← mul_left_comm, Q.polar_smul_left], refl },
  bilin_add_right := λ x y z, by { erw [← mul_add, Q.polar_add_right], refl },
  bilin_smul_right := λ x y z, by { erw [← mul_left_comm, Q.polar_smul_right], refl } }

@[simp] lemma associated_apply (x y : M) :
  Q.associated x y = ⅟2 * (Q (x + y) - Q x - Q y) := rfl

lemma associated_is_sym : is_sym Q.associated :=
λ x y, by simp [add_comm, add_left_comm, sub_eq_add_neg]

@[simp] lemma associated_smul (a : R₁) :
  (a • Q).associated = (a * a) • Q.associated :=
by { ext, simp [bilin_form.smul_apply, map_smul, mul_sub, mul_left_comm] }

@[simp] lemma associated_comp {N : Type v} [add_comm_group N] [module R₁ N] (f : N →ₗ[R₁] M) :
  (Q.comp f).associated = Q.associated.comp f f :=
by { ext, simp }

lemma associated_to_quadratic_form (B : bilin_form R₁ M) (x y : M) :
  B.to_quadratic_form.associated x y = ⅟2 * (B x y + B y x) :=
by simp [associated_apply, ←polar_to_quadratic_form, polar]

lemma associated_left_inverse (h : is_sym B₁) :
  B₁.to_quadratic_form.associated = B₁ :=
bilin_form.ext $ λ x y,
by rw [associated_to_quadratic_form, sym h x y, ←two_mul, ←mul_assoc, inv_of_mul_self, one_mul]

lemma associated_right_inverse : Q.associated.to_quadratic_form = Q :=
quadratic_form.ext $ λ x,
  calc  Q.associated.to_quadratic_form x
      = ⅟2 * (Q x + Q x) : by simp [map_add_self, bit0, add_mul]
  ... = Q x : by rw [← two_mul (Q x), ←mul_assoc, inv_of_mul_self, one_mul]
end associated

section pos_def

variables {R₂ : Type u} [ordered_ring R₂] [module R₂ M] {Q₂ : quadratic_form R₂ M}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def pos_def (Q₂ : quadratic_form R₂ M) : Prop := ∀ x ≠ 0, 0 < Q₂ x

lemma smul_pos_def_of_smul_nonzero {R} [linear_ordered_comm_ring R] [module R M]
  {Q : quadratic_form R M} (h : pos_def Q) {a : R} : (∀ x ≠ (0 : M), a • x ≠ 0) → pos_def (a • Q) :=
λ ha x hx, h (a • x) (ha x hx)

lemma smul_pos_def_of_nonzero {K : Type u} [linear_ordered_field K] [module K M]
  {Q : quadratic_form K M} (h : pos_def Q) {a : K} : a ≠ 0 → pos_def (a • Q) :=
λ ha x hx, h (a • x) (λ hax, (smul_eq_zero.mp hax).elim ha hx)

end pos_def
end quadratic_form

/-! ### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

variables {n : Type w} [fintype n]

/-- `M.to_quadratic_form` is the map `λ x, col x ⬝ M ⬝ row x` as a quadratic form. -/
def matrix.to_quadratic_form (M : matrix n n R₁) : quadratic_form R₁ (n → R₁) :=
M.to_bilin_form.to_quadratic_form

variables [decidable_eq n] [invertible (2 : R₁)]

/-- A matrix representation of the quadratic form. -/
def quadratic_form.to_matrix (Q : quadratic_form R₁ (n → R₁)) :
  matrix n n R₁ :=
Q.associated.to_matrix

open quadratic_form
lemma quadratic_form.to_matrix_smul (a : R₁) (Q : quadratic_form R₁ (n → R₁)) :
  (a • Q).to_matrix = (a * a) • Q.to_matrix :=
by simp_rw [to_matrix, associated_smul, mul_smul, bilin_form.to_matrix_smul]

namespace quadratic_form

variables {m : Type w} [fintype m] [decidable_eq m]
open_locale matrix

@[simp]
lemma to_matrix_comp (Q : quadratic_form R₁ (m → R₁)) (f : (n → R₁) →ₗ[R₁] (m → R₁)) :
  (Q.comp f).to_matrix = f.to_matrixᵀ ⬝ Q.to_matrix ⬝ f.to_matrix :=
by { ext, simp [to_matrix, bilin_form.to_matrix_comp] }

section discriminant
variables {Q : quadratic_form R₁ (n → R₁)}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : quadratic_form R₁ (n → R₁)) : R₁ := Q.to_matrix.det

lemma discr_smul (a : R₁) : (a • Q).discr = (a * a) ^ fintype.card n * Q.discr :=
by simp [discr, to_matrix_smul]

lemma discr_comp (f : (n → R₁) →ₗ[R₁] (n → R₁)) :
  (Q.comp f).discr = f.to_matrix.det * f.to_matrix.det * Q.discr :=
by simp [discr, mul_left_comm, mul_comm]

end discriminant

end quadratic_form
