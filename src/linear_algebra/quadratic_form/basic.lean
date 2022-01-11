/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/

import algebra.invertible
import linear_algebra.matrix.determinant
import linear_algebra.bilinear_form

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
 * `quadratic_form.anisotropic`: anisotropic quadratic forms
 * `quadratic_form.discr`: discriminant of a quadratic form

## Main statements

 * `quadratic_form.associated_left_inverse`,
 * `quadratic_form.associated_right_inverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic forms and symmetric
  bilinear forms
 * `bilin_form.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear form `B`.

## Notation

In this file, the variable `R` is used when a `ring` structure is sufficient and
`R₁` is used when specifically a `comm_ring` is required. This allows us to keep
`[module R M]` and `[module R₁ M]` assumptions in the variables without
confusion between `*` from `ring` and `*` from `comm_ring`.

The variable `S` is used when `R` itself has a `•` action.

## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic form, homogeneous polynomial, quadratic polynomial
-/

universes u v w
variables {S : Type*}
variables {R : Type*} {M : Type*} [add_comm_group M] [ring R]
variables {R₁ : Type*} [comm_ring R₁]

namespace quadratic_form
/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.d

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → R) (x y : M) :=
f (x + y) - f x - f y

lemma polar_add (f g : M → R) (x y : M) :
  polar (f + g) x y = polar f x y + polar g x y :=
by { simp only [polar, pi.add_apply], abel }

lemma polar_neg (f : M → R) (x y : M) :
  polar (-f) x y = - polar f x y :=
by { simp only [polar, pi.neg_apply, sub_eq_add_neg, neg_add] }

lemma polar_smul [monoid S] [distrib_mul_action S R] (f : M → R) (s : S) (x y : M) :
  polar (s • f) x y = s • polar f x y :=
by { simp only [polar, pi.smul_apply, smul_sub] }

lemma polar_comm (f : M → R) (x y : M) : polar f x y = polar f y x :=
by rw [polar, polar, add_comm, sub_sub, sub_sub, add_comm (f x) (f y)]

lemma polar_comp {F : Type*} [ring S] [add_monoid_hom_class F R S] (f : M → R) (g : F) (x y : M) :
  polar (g ∘ f) x y = g (polar f x y) :=
by simp only [polar, pi.smul_apply, function.comp_apply, map_sub]

end quadratic_form

variables [module R M] [module R₁ M]

open quadratic_form
/-- A quadratic form over a module. -/
structure quadratic_form (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] :=
(to_fun : M → R)
(to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x)
(polar_add_left' : ∀ (x x' y : M), polar to_fun (x + x') y = polar to_fun x y + polar to_fun x' y)
(polar_smul_left' : ∀ (a : R) (x y : M), polar to_fun (a • x) y = a • polar to_fun x y)
(polar_add_right' : ∀ (x y y' : M), polar to_fun x (y + y') = polar to_fun x y + polar to_fun x y')
(polar_smul_right' : ∀ (a : R) (x y : M), polar to_fun x (a • y) = a • polar to_fun x y)

namespace quadratic_form

variables {Q : quadratic_form R M}

instance : has_coe_to_fun (quadratic_form R M) (λ _, M → R) := ⟨to_fun⟩

/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp] lemma to_fun_eq_apply : Q.to_fun = ⇑ Q := rfl

lemma map_smul (a : R) (x : M) : Q (a • x) = a * a * Q x := Q.to_fun_smul a x

lemma map_add_self (x : M) : Q (x + x) = 4 * Q x :=
by { rw [←one_smul R x, ←add_smul, map_smul], norm_num }

@[simp] lemma map_zero : Q 0 = 0 :=
by rw [←@zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]

@[simp] lemma map_neg (x : M) : Q (-x) = Q x :=
by rw [←@neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_neg, one_mul]

lemma map_sub (x y : M) : Q (x - y) = Q (y - x) :=
by rw [←neg_sub, map_neg]

@[simp]
lemma polar_zero_left (y : M) : polar Q 0 y = 0 :=
by simp only [polar, zero_add, quadratic_form.map_zero, sub_zero, sub_self]

@[simp]
lemma polar_add_left (x x' y : M) :
  polar Q (x + x') y = polar Q x y + polar Q x' y :=
Q.polar_add_left' x x' y

@[simp]
lemma polar_smul_left (a : R) (x y : M) :
  polar Q (a • x) y = a * polar Q x y :=
Q.polar_smul_left' a x y

@[simp]
lemma polar_neg_left (x y : M) :
  polar Q (-x) y = -polar Q x y :=
by rw [←neg_one_smul R x, polar_smul_left, neg_one_mul]

@[simp]
lemma polar_sub_left (x x' y : M) :
  polar Q (x - x') y = polar Q x y - polar Q x' y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]

@[simp]
lemma polar_zero_right (y : M) : polar Q y 0 = 0 :=
by simp only [add_zero, polar, quadratic_form.map_zero, sub_self]

@[simp]
lemma polar_add_right (x y y' : M) :
  polar Q x (y + y') = polar Q x y + polar Q x y' :=
Q.polar_add_right' x y y'

@[simp]
lemma polar_smul_right (a : R) (x y : M) :
  polar Q x (a • y) = a * polar Q x y :=
Q.polar_smul_right' a x y

@[simp]
lemma polar_neg_right (x y : M) :
  polar Q x (-y) = -polar Q x y :=
by rw [←neg_one_smul R y, polar_smul_right, neg_one_mul]

@[simp]
lemma polar_sub_right (x y y' : M) :
  polar Q x (y - y') = polar Q x y - polar Q x y' :=
by rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]

@[simp]
lemma polar_self (x : M) : polar Q x x = 2 * Q x :=
begin
  rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ←two_mul, ←two_mul, ←mul_assoc],
  norm_num
end

section of_tower

variables [comm_semiring S] [algebra S R] [module S M] [is_scalar_tower S R M]

variables (Q)

lemma map_smul_of_tower (a : S) (x : M) : Q (a • x) = (a * a) • Q x :=
by rw [←is_scalar_tower.algebra_map_smul R a x, map_smul, ←ring_hom.map_mul, algebra.smul_def]

@[simp]
lemma polar_smul_left_of_tower (a : S) (x y : M) :
  polar Q (a • x) y = a • polar Q x y :=
by rw [←is_scalar_tower.algebra_map_smul R a x, polar_smul_left, algebra.smul_def]

@[simp]
lemma polar_smul_right_of_tower (a : S) (x y : M) :
  polar Q x (a • y) = a • polar Q x y :=
by rw [←is_scalar_tower.algebra_map_smul R a y, polar_smul_right, algebra.smul_def]

end of_tower

variable {Q' : quadratic_form R M}

@[ext] lemma ext (H : ∀ (x : M), Q x = Q' x) : Q = Q' :=
by { cases Q, cases Q', congr, funext, apply H }

lemma congr_fun (h : Q = Q') (x : M) : Q x = Q' x := h ▸ rfl

lemma ext_iff : Q = Q' ↔ (∀ x, Q x = Q' x) := ⟨congr_fun, ext⟩

instance : has_zero (quadratic_form R M) :=
⟨ { to_fun := λ x, 0,
    to_fun_smul := λ a x, by simp only [mul_zero],
    polar_add_left' := λ x x' y, by simp only [add_zero, polar, sub_self],
    polar_smul_left' := λ a x y, by simp only [polar, smul_zero, sub_self],
    polar_add_right' := λ x y y', by simp only [add_zero, polar, sub_self],
    polar_smul_right' := λ a x y, by simp only [polar, smul_zero, sub_self]} ⟩

@[simp] lemma coe_fn_zero : ⇑(0 : quadratic_form R M) = 0 := rfl

@[simp] lemma zero_apply (x : M) : (0 : quadratic_form R M) x = 0 := rfl

instance : inhabited (quadratic_form R M) := ⟨0⟩

instance : has_add (quadratic_form R M) :=
⟨ λ Q Q',
  { to_fun := Q + Q',
    to_fun_smul := λ a x,
      by simp only [pi.add_apply, map_smul, mul_add],
    polar_add_left' := λ x x' y,
      by simp only [polar_add, polar_add_left, add_assoc, add_left_comm],
    polar_smul_left' := λ a x y,
      by simp only [polar_add, smul_eq_mul, mul_add, polar_smul_left],
    polar_add_right' := λ x y y',
      by simp only [polar_add, polar_add_right, add_assoc, add_left_comm],
    polar_smul_right' := λ a x y,
      by simp only [polar_add, smul_eq_mul, mul_add, polar_smul_right] } ⟩

@[simp] lemma coe_fn_add (Q Q' : quadratic_form R M) : ⇑(Q + Q') = Q + Q' := rfl

@[simp] lemma add_apply (Q Q' : quadratic_form R M) (x : M) : (Q + Q') x = Q x + Q' x := rfl

instance : has_neg (quadratic_form R M) :=
⟨ λ Q,
  { to_fun := -Q,
  to_fun_smul := λ a x,
    by simp only [pi.neg_apply, map_smul, mul_neg_eq_neg_mul_symm],
  polar_add_left' := λ x x' y,
    by simp only [polar_neg, polar_add_left, neg_add],
  polar_smul_left' := λ a x y,
    by simp only [polar_neg, polar_smul_left, mul_neg_eq_neg_mul_symm, smul_eq_mul],
  polar_add_right' := λ x y y',
    by simp only [polar_neg, polar_add_right, neg_add],
  polar_smul_right' := λ a x y,
    by simp only [polar_neg, polar_smul_right, mul_neg_eq_neg_mul_symm, smul_eq_mul] } ⟩

@[simp] lemma coe_fn_neg (Q : quadratic_form R M) : ⇑(-Q) = -Q := rfl

@[simp] lemma neg_apply (Q : quadratic_form R M) (x : M) : (-Q) x = -Q x := rfl

instance : add_comm_group (quadratic_form R M) :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_comm := λ Q Q', by { ext, simp only [add_apply, add_comm] },
  add_assoc := λ Q Q' Q'', by { ext, simp only [add_apply, add_assoc] },
  add_left_neg := λ Q, by { ext, simp only [add_apply, neg_apply, zero_apply, add_left_neg] },
  add_zero := λ Q, by { ext, simp only [zero_apply, add_apply, add_zero] },
  zero_add := λ Q, by { ext, simp only [zero_apply, add_apply, zero_add] } }

@[simp] lemma coe_fn_sub (Q Q' : quadratic_form R M) : ⇑(Q - Q') = Q - Q' :=
by simp only [quadratic_form.coe_fn_neg, add_left_inj, quadratic_form.coe_fn_add, sub_eq_add_neg]

@[simp] lemma sub_apply (Q Q' : quadratic_form R M) (x : M) : (Q - Q') x = Q x - Q' x :=
by simp only [quadratic_form.neg_apply, add_left_inj, quadratic_form.add_apply, sub_eq_add_neg]

/-- `@coe_fn (quadratic_form R M)` as an `add_monoid_hom`.

This API mirrors `add_monoid_hom.coe_fn`. -/
@[simps apply]
def coe_fn_add_monoid_hom : quadratic_form R M →+ (M → R) :=
{ to_fun := coe_fn, map_zero' := coe_fn_zero, map_add' := coe_fn_add }

/-- Evaluation on a particular element of the module `M` is an additive map over quadratic forms. -/
@[simps apply]
def eval_add_monoid_hom (m : M) : quadratic_form R M →+ R :=
(pi.eval_add_monoid_hom _ m).comp coe_fn_add_monoid_hom

section sum

open_locale big_operators

@[simp] lemma coe_fn_sum {ι : Type*} (Q : ι → quadratic_form R M) (s : finset ι) :
  ⇑(∑ i in s, Q i) = ∑ i in s, Q i :=
(coe_fn_add_monoid_hom : _ →+ (M → R)).map_sum Q s

@[simp] lemma sum_apply {ι : Type*} (Q : ι → quadratic_form R M) (s : finset ι) (x : M) :
  (∑ i in s, Q i) x = ∑ i in s, Q i x :=
(eval_add_monoid_hom x : _ →+ R).map_sum Q s

end sum

section has_scalar

variables [monoid S] [distrib_mul_action S R] [smul_comm_class S R R]

/-- `quadratic_form R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `algebra.id`. -/
instance : has_scalar S (quadratic_form R M) :=
⟨ λ a Q,
  { to_fun := a • Q,
    to_fun_smul := λ b x, by rw [pi.smul_apply, map_smul, pi.smul_apply, mul_smul_comm],
    polar_add_left' := λ x x' y, by simp only [polar_smul, polar_add_left, smul_add],
    polar_smul_left' := λ b x y, begin
      simp only [polar_smul, polar_smul_left, ←mul_smul_comm, smul_eq_mul],
    end,
    polar_add_right' := λ x y y', by simp only [polar_smul, polar_add_right, smul_add],
    polar_smul_right' := λ b x y, begin
      simp only [polar_smul, polar_smul_right, ←mul_smul_comm, smul_eq_mul],
    end } ⟩

@[simp] lemma coe_fn_smul (a : S) (Q : quadratic_form R M) : ⇑(a • Q) = a • Q := rfl

@[simp] lemma smul_apply (a : S) (Q : quadratic_form R M) (x : M) :
  (a • Q) x = a • Q x := rfl

instance : distrib_mul_action S (quadratic_form R M) :=
{ mul_smul := λ a b Q, ext (λ x, by simp only [smul_apply, mul_smul]),
  one_smul := λ Q, ext (λ x, by simp only [quadratic_form.smul_apply, one_smul]),
  smul_add := λ a Q Q', by { ext, simp only [add_apply, smul_apply, smul_add] },
  smul_zero := λ a, by { ext, simp only [zero_apply, smul_apply, smul_zero] }, }

end has_scalar

section module

instance [semiring S] [module S R] [smul_comm_class S R R] : module S (quadratic_form R M) :=
{ zero_smul := λ Q, by { ext, simp only [zero_apply, smul_apply, zero_smul] },
  add_smul := λ a b Q, by { ext, simp only [add_apply, smul_apply, add_smul] } }

end module

section comp

variables {N : Type v} [add_comm_group N] [module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : quadratic_form R N) (f : M →ₗ[R] N) :
  quadratic_form R M :=
{ to_fun := λ x, Q (f x),
  to_fun_smul := λ a x, by simp only [map_smul, f.map_smul],
  polar_add_left' := λ x x' y,
    by convert polar_add_left (f x) (f x') (f y) using 1;
      simp only [polar, f.map_add],
  polar_smul_left' := λ a x y,
    by convert polar_smul_left a (f x) (f y) using 1;
      simp only [polar, f.map_smul, f.map_add, smul_eq_mul],
  polar_add_right' := λ x y y',
    by convert polar_add_right (f x) (f y) (f y') using 1;
      simp only [polar, f.map_add],
  polar_smul_right' := λ a x y,
    by convert polar_smul_right a (f x) (f y) using 1;
      simp only [polar, f.map_smul, f.map_add, smul_eq_mul] }

@[simp] lemma comp_apply (Q : quadratic_form R N) (f : M →ₗ[R] N) (x : M) :
  (Q.comp f) x = Q (f x) := rfl

/-- Compose a quadratic form with a linear function on the left. -/
@[simps {simp_rhs := tt}]
def _root_.linear_map.comp_quadratic_form {S : Type*}
  [comm_ring S] [algebra S R] [module S M] [is_scalar_tower S R M]
  (f : R →ₗ[S] S) (Q : quadratic_form R M) :
  quadratic_form S M :=
{ to_fun := f ∘ Q,
  to_fun_smul := λ b x, by rw [function.comp_apply, Q.map_smul_of_tower b x, f.map_smul,
                               smul_eq_mul],
  polar_add_left' := λ x x' y, by simp only [polar_comp, f.map_add, polar_add_left],
  polar_smul_left' := λ b x y, by simp only [polar_comp, f.map_smul, polar_smul_left_of_tower],
  polar_add_right' := λ x y y', by simp only [polar_comp, f.map_add, polar_add_right],
  polar_smul_right' := λ b x y, by simp only [polar_comp, f.map_smul, polar_smul_right_of_tower], }

end comp

section comm_ring

/-- Create a quadratic form in a commutative ring by proving only one side of the bilinearity. -/
def mk_left (f : M → R₁)
  (to_fun_smul : ∀ a x, f (a • x) = a * a * f x)
  (polar_add_left : ∀ x x' y, polar f (x + x') y = polar f x y + polar f x' y)
  (polar_smul_left : ∀ a x y, polar f (a • x) y = a * polar f x y) :
  quadratic_form R₁ M :=
{ to_fun := f,
  to_fun_smul := to_fun_smul,
  polar_add_left' := polar_add_left,
  polar_smul_left' := polar_smul_left,
  polar_add_right' :=
    λ x y y', by rw [polar_comm, polar_add_left, polar_comm f y x, polar_comm f y' x],
  polar_smul_right' :=
    λ a x y, by rw [polar_comm, polar_smul_left, polar_comm f y x, smul_eq_mul] }

/-- The product of linear forms is a quadratic form. -/
def lin_mul_lin (f g : M →ₗ[R₁] R₁) : quadratic_form R₁ M :=
mk_left (f * g)
  (λ a x,
    by { simp only [smul_eq_mul, ring_hom.id_apply, pi.mul_apply, linear_map.map_smulₛₗ], ring })
  (λ x x' y, by { simp only [polar, pi.mul_apply, linear_map.map_add], ring })
  (λ a x y, begin
      simp only [polar, pi.mul_apply, linear_map.map_add, linear_map.map_smul, smul_eq_mul], ring
    end)

@[simp]
lemma lin_mul_lin_apply (f g : M →ₗ[R₁] R₁) (x) : lin_mul_lin f g x = f x * g x := rfl

@[simp]
lemma add_lin_mul_lin (f g h : M →ₗ[R₁] R₁) :
  lin_mul_lin (f + g) h = lin_mul_lin f h + lin_mul_lin g h :=
ext (λ x, add_mul _ _ _)

@[simp]
lemma lin_mul_lin_add (f g h : M →ₗ[R₁] R₁) :
  lin_mul_lin f (g + h) = lin_mul_lin f g + lin_mul_lin f h :=
ext (λ x, mul_add _ _ _)

variables {N : Type v} [add_comm_group N] [module R₁ N]

@[simp]
lemma lin_mul_lin_comp (f g : M →ₗ[R₁] R₁) (h : N →ₗ[R₁] M) :
  (lin_mul_lin f g).comp h = lin_mul_lin (f.comp h) (g.comp h) :=
rfl

variables {n : Type*}

/-- `sq` is the quadratic form mapping the vector `x : R₁` to `x * x` -/
@[simps]
def sq : quadratic_form R₁ R₁ :=
lin_mul_lin linear_map.id linear_map.id

/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj (i j : n) : quadratic_form R₁ (n → R₁) :=
lin_mul_lin (@linear_map.proj _ _ _ (λ _, R₁) _ _ i) (@linear_map.proj _ _ _ (λ _, R₁) _ _ j)

@[simp]
lemma proj_apply (i j : n) (x : n → R₁) : proj i j x = x i * x j := rfl

end comm_ring

end quadratic_form

/-!
### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/

variables {B : bilin_form R M}

namespace bilin_form
open quadratic_form

lemma polar_to_quadratic_form (x y : M) : polar (λ x, B x x) x y = B x y + B y x :=
by { simp only [add_assoc, add_sub_cancel', add_right, polar, add_left_inj, add_neg_cancel_left,
  add_left, sub_eq_add_neg _ (B y y), add_comm (B y x) _] }

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def to_quadratic_form (B : bilin_form R M) : quadratic_form R M :=
⟨ λ x, B x x,
  λ a x, by simp only [mul_assoc, smul_right, smul_left],
  λ x x' y, by simp only [add_assoc, add_right, add_left_inj, polar_to_quadratic_form, add_left,
    add_left_comm],
  λ a x y, by simp only [smul_add, add_left_inj, polar_to_quadratic_form,
    smul_right, smul_eq_mul, smul_left, smul_right, mul_add],
  λ x y y', by simp only [add_assoc, add_right, add_left_inj,
    polar_to_quadratic_form, add_left, add_left_comm],
  λ a x y, by simp only [smul_add, add_left_inj, polar_to_quadratic_form,
    smul_right, smul_eq_mul, smul_left, smul_right, mul_add]⟩

@[simp] lemma to_quadratic_form_apply (B : bilin_form R M) (x : M) :
  B.to_quadratic_form x = B x x :=
rfl

section
variables (R M)
@[simp] lemma to_quadratic_form_zero : (0 : bilin_form R M).to_quadratic_form = 0 := rfl
end

end bilin_form

namespace quadratic_form
open bilin_form

section associated_hom
variables (S) [comm_semiring S] [algebra S R]
variables [invertible (2 : R)] {B₁ : bilin_form R M}

/-- `associated_hom` is the map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `associated`, which gives an `R`-linear map.  Over a general ring with
no nontrivial distinguished commutative subring, use `associated'`, which gives an additive
homomorphism (or more precisely a `ℤ`-linear map.) -/
def associated_hom : quadratic_form R M →ₗ[S] bilin_form R M :=
{ to_fun := λ Q,
  { bilin := λ x y, ⅟2 * polar Q x y,
    bilin_add_left := λ x y z, by rw [← mul_add, polar_add_left],
    bilin_smul_left := λ x y z, begin
      have htwo : x * ⅟2 = ⅟2 * x := (commute.one_right x).bit0_right.inv_of_right,
      simp only [polar_smul_left, ← mul_assoc, htwo]
    end,
    bilin_add_right := λ x y z, by rw [← mul_add, polar_add_right],
    bilin_smul_right := λ x y z, begin
      have htwo : x * ⅟2 = ⅟2 * x := (commute.one_right x).bit0_right.inv_of_right,
      simp only [polar_smul_right, ← mul_assoc, htwo]
    end },
  map_add' := λ Q Q', by { ext, simp only [bilin_form.add_apply, coe_fn_mk, polar_add, coe_fn_add,
    mul_add] },
  map_smul' := λ s Q, by { ext, simp only [ring_hom.id_apply, polar_smul, algebra.mul_smul_comm,
    coe_fn_mk, coe_fn_smul, bilin_form.smul_apply] } }

variables (Q : quadratic_form R M) (S)

@[simp] lemma associated_apply (x y : M) :
  associated_hom S Q x y = ⅟2 * (Q (x + y) - Q x - Q y) := rfl

lemma associated_is_symm : (associated_hom S Q).is_symm :=
λ x y, by simp only [associated_apply, add_comm, add_left_comm, sub_eq_add_neg]

@[simp] lemma associated_comp {N : Type v} [add_comm_group N] [module R N] (f : N →ₗ[R] M) :
  associated_hom S (Q.comp f) = (associated_hom S Q).comp f f :=
by { ext, simp only [quadratic_form.comp_apply, bilin_form.comp_apply, associated_apply,
  linear_map.map_add] }

lemma associated_to_quadratic_form (B : bilin_form R M) (x y : M) :
  associated_hom S B.to_quadratic_form x y = ⅟2 * (B x y + B y x) :=
by simp only [associated_apply, ← polar_to_quadratic_form, polar, to_quadratic_form_apply]

lemma associated_left_inverse (h : B₁.is_symm) :
  associated_hom S (B₁.to_quadratic_form) = B₁ :=
bilin_form.ext $ λ x y,
by rw [associated_to_quadratic_form, is_symm.eq h x y, ←two_mul, ←mul_assoc, inv_of_mul_self,
  one_mul]

lemma to_quadratic_form_associated : (associated_hom S Q).to_quadratic_form = Q :=
quadratic_form.ext $ λ x,
  calc (associated_hom S Q).to_quadratic_form x
      = ⅟2 * (Q x + Q x) : by simp only [add_assoc, add_sub_cancel', one_mul,
    to_quadratic_form_apply, add_mul, associated_apply, map_add_self, bit0]
  ... = Q x : by rw [← two_mul (Q x), ←mul_assoc, inv_of_mul_self, one_mul]

-- note: usually `right_inverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
lemma associated_right_inverse :
  function.right_inverse (associated_hom S)
    (bilin_form.to_quadratic_form : _ → quadratic_form R M) :=
λ Q, to_quadratic_form_associated S Q

lemma associated_eq_self_apply (x : M) : associated_hom S Q x x = Q x :=
begin
  rw [associated_apply, map_add_self],
  suffices : (⅟2) * (2 * Q x) = Q x,
  { convert this,
    simp only [bit0, add_mul, one_mul],
    abel },
  simp only [← mul_assoc, one_mul, inv_of_mul_self],
end

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbreviation associated' : quadratic_form R M →ₗ[ℤ] bilin_form R M :=
associated_hom ℤ

/-- Symmetric bilinear forms can be lifted to quadratic forms -/
instance : can_lift (bilin_form R M) (quadratic_form R M) :=
{ coe := associated_hom ℕ,
  cond := bilin_form.is_symm,
  prf := λ B hB, ⟨B.to_quadratic_form, associated_left_inverse _ hB⟩ }

/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`. -/
lemma exists_quadratic_form_ne_zero {Q : quadratic_form R M} (hB₁ : Q.associated' ≠ 0) :
  ∃ x, Q x ≠ 0 :=
begin
  rw ←not_forall,
  intro h,
  apply hB₁,
  rw [(quadratic_form.ext h : Q = 0), linear_map.map_zero],
end

end associated_hom

section associated
variables [invertible (2 : R₁)]

-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associated_hom` and place it in the previous section.

/-- `associated` is the linear map that sends a quadratic form over a commutative ring to its
associated symmetric bilinear form. -/
abbreviation associated : quadratic_form R₁ M →ₗ[R₁] bilin_form R₁ M :=
associated_hom R₁

@[simp] lemma associated_lin_mul_lin (f g : M →ₗ[R₁] R₁) :
  (lin_mul_lin f g).associated =
    ⅟(2 : R₁) • (bilin_form.lin_mul_lin f g + bilin_form.lin_mul_lin g f) :=
by { ext, simp only [smul_add, algebra.id.smul_eq_mul, bilin_form.lin_mul_lin_apply,
  quadratic_form.lin_mul_lin_apply, bilin_form.smul_apply, associated_apply, bilin_form.add_apply,
  linear_map.map_add], ring }

end associated

section anisotropic

/-- An anisotropic quadratic form is zero only on zero vectors. -/
def anisotropic (Q : quadratic_form R M) : Prop := ∀ x, Q x = 0 → x = 0

lemma not_anisotropic_iff_exists (Q : quadratic_form R M) :
  ¬anisotropic Q ↔ ∃ x ≠ 0, Q x = 0 :=
by simp only [anisotropic, not_forall, exists_prop, and_comm]

lemma anisotropic.eq_zero_iff {Q : quadratic_form R M} (h : anisotropic Q) {x : M} :
  Q x = 0 ↔ x = 0 :=
⟨h x, λ h, h.symm ▸ map_zero⟩

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
lemma nondegenerate_of_anisotropic [invertible (2 : R)] (Q : quadratic_form R M)
  (hB : Q.anisotropic) : Q.associated'.nondegenerate :=
begin
  intros x hx,
  refine hB _ _,
  rw ← hx x,
  exact (associated_eq_self_apply _ _ x).symm,
end

end anisotropic

section pos_def

variables {R₂ : Type u} [ordered_ring R₂] [module R₂ M] {Q₂ : quadratic_form R₂ M}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def pos_def (Q₂ : quadratic_form R₂ M) : Prop := ∀ x ≠ 0, 0 < Q₂ x

lemma pos_def.smul {R} [linear_ordered_comm_ring R] [module R M]
  {Q : quadratic_form R M} (h : pos_def Q) {a : R} (a_pos : 0 < a) : pos_def (a • Q) :=
λ x hx, mul_pos a_pos (h x hx)

variables {n : Type*}

lemma pos_def.nonneg {Q : quadratic_form R₂ M} (hQ : pos_def Q) (x : M) :
  0 ≤ Q x :=
(eq_or_ne x 0).elim (λ h, h.symm ▸ (map_zero).symm.le) (λ h, (hQ _ h).le)

lemma pos_def.anisotropic {Q : quadratic_form R₂ M} (hQ : Q.pos_def) : Q.anisotropic :=
λ x hQx, classical.by_contradiction $ λ hx, lt_irrefl (0 : R₂) $ begin
  have := hQ _ hx,
  rw hQx at this,
  exact this,
end

lemma pos_def_of_nonneg {Q : quadratic_form R₂ M} (h : ∀ x, 0 ≤ Q x) (h0 : Q.anisotropic) :
  pos_def Q :=
λ x hx, lt_of_le_of_ne (h x) (ne.symm $ λ hQx, hx $ h0 _ hQx)

lemma pos_def_iff_nonneg {Q : quadratic_form R₂ M} :
  pos_def Q ↔ (∀ x, 0 ≤ Q x) ∧ Q.anisotropic  :=
⟨λ h, ⟨h.nonneg, h.anisotropic⟩, λ ⟨n, a⟩, pos_def_of_nonneg n a⟩

lemma pos_def.add (Q Q' : quadratic_form R₂ M) (hQ : pos_def Q) (hQ' : pos_def Q') :
  pos_def (Q + Q') :=
λ x hx, add_pos (hQ x hx) (hQ' x hx)

lemma lin_mul_lin_self_pos_def {R} [linear_ordered_comm_ring R] [module R M]
  (f : M →ₗ[R] R) (hf : linear_map.ker f = ⊥) :
  pos_def (lin_mul_lin f f) :=
λ x hx, mul_self_pos (λ h, hx (linear_map.ker_eq_bot.mp hf (by rw [h, linear_map.map_zero])))

end pos_def
end quadratic_form

section
/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

variables {n : Type w} [fintype n] [decidable_eq n]

/-- `M.to_quadratic_form` is the map `λ x, col x ⬝ M ⬝ row x` as a quadratic form. -/
def matrix.to_quadratic_form' (M : matrix n n R₁) :
  quadratic_form R₁ (n → R₁) :=
M.to_bilin'.to_quadratic_form

variables [invertible (2 : R₁)]

/-- A matrix representation of the quadratic form. -/
def quadratic_form.to_matrix' (Q : quadratic_form R₁ (n → R₁)) : matrix n n R₁ :=
Q.associated.to_matrix'

open quadratic_form
lemma quadratic_form.to_matrix'_smul (a : R₁) (Q : quadratic_form R₁ (n → R₁)) :
  (a • Q).to_matrix' = a • Q.to_matrix' :=
by simp only [to_matrix', linear_equiv.map_smul, linear_map.map_smul]

end

namespace quadratic_form

variables {n : Type w} [fintype n]
variables [decidable_eq n] [invertible (2 : R₁)]
variables {m : Type w} [decidable_eq m] [fintype m]
open_locale matrix

@[simp]
lemma to_matrix'_comp (Q : quadratic_form R₁ (m → R₁)) (f : (n → R₁) →ₗ[R₁] (m → R₁)) :
  (Q.comp f).to_matrix' = f.to_matrix'ᵀ ⬝ Q.to_matrix' ⬝ f.to_matrix' :=
by { ext, simp only [quadratic_form.associated_comp, bilin_form.to_matrix'_comp, to_matrix'] }

section discriminant
variables {Q : quadratic_form R₁ (n → R₁)}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : quadratic_form R₁ (n → R₁)) : R₁ := Q.to_matrix'.det

lemma discr_smul (a : R₁) : (a • Q).discr = a ^ fintype.card n * Q.discr :=
by simp only [discr, to_matrix'_smul, matrix.det_smul]

lemma discr_comp (f : (n → R₁) →ₗ[R₁] (n → R₁)) :
  (Q.comp f).discr = f.to_matrix'.det * f.to_matrix'.det * Q.discr :=
by simp only [matrix.det_transpose, mul_left_comm, quadratic_form.to_matrix'_comp, mul_comm,
  matrix.det_mul, discr]

end discriminant

end quadratic_form

namespace quadratic_form

variables {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M₁] [module R M₂] [module R M₃]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
@[nolint has_inhabited_instance] structure isometry
  (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) extends M₁ ≃ₗ[R] M₂ :=
(map_app' : ∀ m, Q₂ (to_fun m) = Q₁ m)

/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometry between them:
a linear equivalence that transforms one quadratic form into the other. -/
def equivalent (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) := nonempty (Q₁.isometry Q₂)

namespace isometry

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}

instance : has_coe (Q₁.isometry Q₂) (M₁ ≃ₗ[R] M₂) := ⟨isometry.to_linear_equiv⟩

@[simp] lemma to_linear_equiv_eq_coe (f : Q₁.isometry Q₂) : f.to_linear_equiv = f := rfl

instance : has_coe_to_fun (Q₁.isometry Q₂) (λ _, M₁ → M₂) := ⟨λ f, ⇑(f : M₁ ≃ₗ[R] M₂)⟩

@[simp] lemma coe_to_linear_equiv (f : Q₁.isometry Q₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f := rfl

@[simp] lemma map_app (f : Q₁.isometry Q₂) (m : M₁) : Q₂ (f m) = Q₁ m := f.map_app' m

/-- The identity isometry from a quadratic form to itself. -/
@[refl]
def refl (Q : quadratic_form R M) : Q.isometry Q :=
{ map_app' := λ m, rfl,
  .. linear_equiv.refl R M }

/-- The inverse isometry of an isometry between two quadratic forms. -/
@[symm]
def symm (f : Q₁.isometry Q₂) : Q₂.isometry Q₁ :=
{ map_app' := by { intro m, rw ← f.map_app, congr, exact f.to_linear_equiv.apply_symm_apply m },
  .. (f : M₁ ≃ₗ[R] M₂).symm }

/-- The composition of two isometries between quadratic forms. -/
@[trans]
def trans (f : Q₁.isometry Q₂) (g : Q₂.isometry Q₃) : Q₁.isometry Q₃ :=
{ map_app' := by { intro m, rw [← f.map_app, ← g.map_app], refl },
  .. (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) }

end isometry

namespace equivalent

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}

@[refl]
lemma refl (Q : quadratic_form R M) : Q.equivalent Q := ⟨isometry.refl Q⟩

@[symm]
lemma symm (h : Q₁.equivalent Q₂) : Q₂.equivalent Q₁ := h.elim $ λ f, ⟨f.symm⟩

@[trans]
lemma trans (h : Q₁.equivalent Q₂) (h' : Q₂.equivalent Q₃) : Q₁.equivalent Q₃ :=
h'.elim $ h.elim $ λ f g, ⟨f.trans g⟩

end equivalent

end quadratic_form

namespace bilin_form

/-- A bilinear form is nondegenerate if the quadratic form it is associated with is anisotropic. -/
lemma nondegenerate_of_anisotropic
  {B : bilin_form R M} (hB : B.to_quadratic_form.anisotropic) : B.nondegenerate :=
λ x hx, hB _ (hx x)

/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
lemma exists_bilin_form_self_ne_zero [htwo : invertible (2 : R)]
  {B : bilin_form R M} (hB₁ : B ≠ 0) (hB₂ : B.is_symm) :
  ∃ x, ¬ B.is_ortho x x :=
begin
  lift B to quadratic_form R M using hB₂ with Q,
  obtain ⟨x, hx⟩ := quadratic_form.exists_quadratic_form_ne_zero hB₁,
  exact ⟨x, λ h, hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩,
end

open finite_dimensional

variables {V : Type u} {K : Type v} [field K] [add_comm_group V] [module K V]
variable [finite_dimensional K V]

/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
lemma exists_orthogonal_basis [hK : invertible (2 : K)]
  {B : bilin_form K V} (hB₂ : B.is_symm) :
  ∃ (v : basis (fin (finrank K V)) K V), B.is_Ortho v :=
begin
  tactic.unfreeze_local_instances,
  induction hd : finrank K V with d ih generalizing V,
  { exact ⟨basis_of_finrank_zero hd, λ _ _ _, zero_left _⟩ },
  haveI := finrank_pos_iff.1 (hd.symm ▸ nat.succ_pos d : 0 < finrank K V),
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0,
  { let b := finite_dimensional.fin_basis K V,
    rw hd at b,
    refine ⟨b, λ i j hij, rfl⟩, },
  obtain ⟨x, hx⟩ := exists_bilin_form_self_ne_zero hB₁ hB₂,
  rw [← submodule.finrank_add_eq_of_is_compl (is_compl_span_singleton_orthogonal hx).symm,
      finrank_span_singleton (ne_zero_of_not_is_ortho_self x hx)] at hd,
  let B' := B.restrict (B.orthogonal $ K ∙ x),
  obtain ⟨v', hv₁⟩ := ih (B.restrict_symm hB₂ _ : B'.is_symm) (nat.succ.inj hd),
  -- concatenate `x` with the basis obtained by induction
  let b := basis.mk_fin_cons x v'
    (begin
      rintros c y hy hc,
      rw add_eq_zero_iff_neg_eq at hc,
      rw [← hc, submodule.neg_mem_iff] at hy,
      have := (is_compl_span_singleton_orthogonal hx).disjoint,
      rw submodule.disjoint_def at this,
      have := this (c • x) (submodule.smul_mem _ _ $ submodule.mem_span_singleton_self _) hy,
      exact (smul_eq_zero.1 this).resolve_right (λ h, hx $ h.symm ▸ zero_left _),
    end)
    (begin
      intro y,
      refine ⟨-B x y/B x x, λ z hz, _⟩,
      obtain ⟨c, rfl⟩ := submodule.mem_span_singleton.1 hz,
      rw [is_ortho, smul_left, add_right, smul_right, div_mul_cancel _ hx, add_neg_self, mul_zero],
    end),
  refine ⟨b, _⟩,
  { rw basis.coe_mk_fin_cons,
    intros j i,
    refine fin.cases _ (λ i, _) i; refine fin.cases _ (λ j, _) j; intro hij;
      simp only [function.on_fun, fin.cons_zero, fin.cons_succ, function.comp_apply],
    { exact (hij rfl).elim },
    { rw [is_ortho, hB₂],
      exact (v' j).prop _ (submodule.mem_span_singleton_self x) },
    { exact (v' i).prop _ (submodule.mem_span_singleton_self x) },
    { exact hv₁ _ _ (ne_of_apply_ne _ hij), }, }
end

end bilin_form

namespace quadratic_form

open_locale big_operators

open finset bilin_form

variables {M₁ : Type*} [add_comm_group M₁] [module R M₁]
variables {ι : Type*} [fintype ι] {v : basis ι R M}

/-- A quadratic form composed with a `linear_equiv` is isometric to itself. -/
def isometry_of_comp_linear_equiv (Q : quadratic_form R M) (f : M₁ ≃ₗ[R] M) :
  Q.isometry (Q.comp (f : M₁ →ₗ[R] M)) :=
{ map_app' :=
  begin
    intro,
    simp only [comp_apply, linear_equiv.coe_coe, linear_equiv.to_fun_eq_coe,
               linear_equiv.apply_symm_apply, f.apply_symm_apply],
  end,
  .. f.symm }

/-- Given a quadratic form `Q` and a basis, `basis_repr` is the basis representation of `Q`. -/
noncomputable def basis_repr (Q : quadratic_form R M) (v : basis ι R M) :
  quadratic_form R (ι → R) :=
Q.comp v.equiv_fun.symm

@[simp]
lemma basis_repr_apply (Q : quadratic_form R M) (w : ι → R) :
  Q.basis_repr v w = Q (∑ i : ι, w i • v i) :=
by { rw ← v.equiv_fun_symm_apply, refl }

/-- A quadratic form is isometric to its bases representations. -/
noncomputable def isometry_basis_repr (Q : quadratic_form R M) (v : basis ι R M):
  isometry Q (Q.basis_repr v) :=
isometry_of_comp_linear_equiv Q v.equiv_fun.symm

section

variable (R₁)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R₁` or
`[algebra S R₁]`, although this is stated more generally. -/
def weighted_sum_squares [monoid S] [distrib_mul_action S R₁] [smul_comm_class S R₁ R₁]
  (w : ι → S) : quadratic_form R₁ (ι → R₁) :=
∑ i : ι, w i • proj i i

end

@[simp]
lemma weighted_sum_squares_apply [monoid S] [distrib_mul_action S R₁] [smul_comm_class S R₁ R₁]
  (w : ι → S) (v : ι → R₁) :
  weighted_sum_squares R₁ w v = ∑ i : ι, w i • (v i * v i) :=
quadratic_form.sum_apply _ _ _

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
lemma basis_repr_eq_of_is_Ortho [invertible (2 : R₁)]
  (Q : quadratic_form R₁ M) (v : basis ι R₁ M) (hv₂ : (associated Q).is_Ortho v) :
  Q.basis_repr v = weighted_sum_squares _ (λ i, Q (v i)) :=
begin
  ext w,
  rw [basis_repr_apply, ←@associated_eq_self_apply R₁, sum_left, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  rw [←@associated_eq_self_apply R₁, sum_right, sum_eq_single_of_mem j hj],
  { rw [smul_left, smul_right, smul_eq_mul], ring },
  { intros i _ hij,
    rw [smul_left, smul_right,
        show associated_hom R₁ Q (v j) (v i) = 0, from hv₂ j i hij.symm,
        mul_zero, mul_zero] },
end

variables {V : Type*} {K : Type*} [field K] [invertible (2 : K)]
variables [add_comm_group V] [module K V]

/-- Given an orthogonal basis, a quadratic form is isometric with a weighted sum of squares. -/
noncomputable def isometry_weighted_sum_squares (Q : quadratic_form K V)
  (v : basis (fin (finite_dimensional.finrank K V)) K V)
  (hv₁ : (associated Q).is_Ortho v):
  Q.isometry (weighted_sum_squares K (λ i, Q (v i))) :=
begin
  let iso := Q.isometry_basis_repr v,
  refine ⟨iso, λ m, _⟩,
  convert iso.map_app m,
  rw basis_repr_eq_of_is_Ortho _ _ hv₁,
end

variables [finite_dimensional K V]

lemma equivalent_weighted_sum_squares (Q : quadratic_form K V) :
  ∃ w : fin (finite_dimensional.finrank K V) → K, equivalent Q (weighted_sum_squares K w) :=
let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_is_symm _ Q) in
  ⟨_, ⟨Q.isometry_weighted_sum_squares v hv₁⟩⟩

lemma equivalent_weighted_sum_squares_units_of_nondegenerate'
  (Q : quadratic_form K V) (hQ : (associated Q).nondegenerate) :
  ∃ w : fin (finite_dimensional.finrank K V) → units K,
    equivalent Q (weighted_sum_squares K w) :=
begin
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_is_symm _ Q),
  have hv₂ := hv₁.not_is_ortho_basis_self_of_nondegenerate hQ,
  simp_rw [is_ortho, associated_eq_self_apply] at hv₂,
  exact ⟨λ i, units.mk0 _ (hv₂ i), ⟨Q.isometry_weighted_sum_squares v hv₁⟩⟩,
end

end quadratic_form
