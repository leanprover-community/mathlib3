/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/

import algebra.invertible
import linear_algebra.matrix.determinant
import linear_algebra.matrix.bilinear_form
import linear_algebra.matrix.symmetric

/-!
# Quadratic forms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines quadratic forms over a `R`-module `M`.
A quadratic form on a ring `R` is a map `Q : M → R` such that:
* `quadratic_form.map_smul`: `Q (a • x) = a * a * Q x`
* `quadratic_form.polar_add_left`, `quadratic_form.polar_add_right`,
  `quadratic_form.polar_smul_left`, `quadratic_form.polar_smul_right`:
  the map `quadratic_form.polar Q := λ x y, Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to semirings using the approach in [izhakian2016][] which requires that
there be a (possibly non-unique) companion bilinear form `B` such that
`∀ x y, Q (x + y) = Q x + Q y + B x y`. Over a ring, this `B` is precisely `quadratic_form.polar Q`.

To build a `quadratic_form` from the `polar` axioms, use `quadratic_form.of_polar`.

Quadratic forms come with a scalar multiplication, `(a • Q) x = Q (a • x) = a * a * Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `quadratic_form.of_polar`: a more familiar constructor that works on rings
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
variables {R R₁: Type*} {M : Type*}

open_locale big_operators

section polar
variables [ring R] [comm_ring R₁] [add_comm_group M]

namespace quadratic_form

/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.

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

/-- Auxiliary lemma to express bilinearity of `quadratic_form.polar` without subtraction. -/
lemma polar_add_left_iff {f : M → R} {x x' y : M} :
  polar f (x + x') y = polar f x y + polar f x' y ↔
    f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' + y) + f (y + x) :=
begin
  simp only [←add_assoc],
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub],
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)],
  rw [add_comm y x, add_right_comm _ _ (f (x + y)), add_comm _ (f (x + y)),
    add_right_comm (f (x + y)), add_left_inj],
end

lemma polar_comp {F : Type*} [ring S] [add_monoid_hom_class F R S] (f : M → R) (g : F) (x y : M) :
  polar (g ∘ f) x y = g (polar f x y) :=
by simp only [polar, pi.smul_apply, function.comp_apply, map_sub]

end quadratic_form

end polar

/-- A quadratic form over a module.

For a more familiar constructor when `R` is a ring, see `quadratic_form.of_polar`. -/
structure quadratic_form (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [module R M] :=
(to_fun : M → R)
(to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x)
(exists_companion' : ∃ B : bilin_form R M, ∀ x y, to_fun (x + y) = to_fun x + to_fun y + B x y)

namespace quadratic_form

section fun_like
variables [semiring R] [add_comm_monoid M] [module R M]
variables {Q Q' : quadratic_form R M}

instance fun_like : fun_like (quadratic_form R M) M (λ _, R) :=
{ coe := to_fun,
  coe_injective' := λ x y h, by cases x; cases y; congr' }

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (quadratic_form R M) (λ _, M → R) := ⟨to_fun⟩

variables (Q)

/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp] lemma to_fun_eq_coe : Q.to_fun = ⇑Q := rfl

-- this must come after the coe_to_fun definition
initialize_simps_projections quadratic_form (to_fun → apply)

variables {Q}

@[ext] lemma ext (H : ∀ (x : M), Q x = Q' x) : Q = Q' := fun_like.ext _ _ H

lemma congr_fun (h : Q = Q') (x : M) : Q x = Q' x := fun_like.congr_fun h _

lemma ext_iff : Q = Q' ↔ (∀ x, Q x = Q' x) := fun_like.ext_iff

/-- Copy of a `quadratic_form` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (Q : quadratic_form R M) (Q' : M → R) (h : Q' = ⇑Q) : quadratic_form R M :=
{ to_fun := Q',
  to_fun_smul := h.symm ▸ Q.to_fun_smul,
  exists_companion' := h.symm ▸ Q.exists_companion' }

@[simp]
lemma coe_copy (Q : quadratic_form R M) (Q' : M → R) (h : Q' = ⇑Q) : ⇑(Q.copy Q' h) = Q' := rfl

lemma copy_eq (Q : quadratic_form R M) (Q' : M → R) (h : Q' = ⇑Q) : Q.copy Q' h = Q :=
fun_like.ext' h

end fun_like

section semiring
variables [semiring R] [add_comm_monoid M] [module R M]
variables (Q : quadratic_form R M)

lemma map_smul (a : R) (x : M) : Q (a • x) = a * a * Q x := Q.to_fun_smul a x

lemma exists_companion : ∃ B : bilin_form R M, ∀ x y, Q (x + y) = Q x + Q y + B x y :=
Q.exists_companion'

lemma map_add_add_add_map (x y z : M) :
  Q (x + y + z) + (Q x + Q y + Q z) = Q (x + y) + Q (y + z) + Q (z + x) :=
begin
  obtain ⟨B, h⟩ := Q.exists_companion,
  rw [add_comm z x],
  simp [h],
  abel,
end

lemma map_add_self (x : M) : Q (x + x) = 4 * Q x :=
by { rw [←one_smul R x, ←add_smul, map_smul], norm_num }

@[simp] lemma map_zero : Q 0 = 0 :=
by rw [←@zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]

instance zero_hom_class : zero_hom_class (quadratic_form R M) M R :=
{ map_zero := map_zero,
  ..quadratic_form.fun_like }

lemma map_smul_of_tower [comm_semiring S] [algebra S R] [module S M] [is_scalar_tower S R M]
  (a : S) (x : M) :
  Q (a • x) = (a * a) • Q x :=
by rw [←is_scalar_tower.algebra_map_smul R a x, map_smul, ←ring_hom.map_mul, algebra.smul_def]

end semiring

section ring
variables [ring R] [comm_ring R₁] [add_comm_group M]
variables [module R M] (Q : quadratic_form R M)

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
polar_add_left_iff.mpr $ Q.map_add_add_add_map x x' y

@[simp]
lemma polar_smul_left (a : R) (x y : M) :
  polar Q (a • x) y = a * polar Q x y :=
begin
  obtain ⟨B, h⟩ := Q.exists_companion,
  simp_rw [polar, h, Q.map_smul, bilin_form.smul_left, sub_sub, add_sub_cancel'],
end

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
by rw [polar_comm Q x, polar_comm Q x, polar_comm Q x, polar_add_left]

@[simp]
lemma polar_smul_right (a : R) (x y : M) :
  polar Q x (a • y) = a * polar Q x y :=
by rw [polar_comm Q x, polar_comm Q x, polar_smul_left]

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

/-- `quadratic_form.polar` as a bilinear form -/
@[simps]
def polar_bilin : bilin_form R M :=
{ bilin := polar Q,
  bilin_add_left := polar_add_left Q,
  bilin_smul_left := polar_smul_left Q,
  bilin_add_right := λ x y z, by simp_rw [polar_comm _ x, polar_add_left Q],
  bilin_smul_right := λ r x y, by simp_rw [polar_comm _ x, polar_smul_left Q] }

variables [comm_semiring S] [algebra S R] [module S M] [is_scalar_tower S R M]

@[simp]
lemma polar_smul_left_of_tower (a : S) (x y : M) :
  polar Q (a • x) y = a • polar Q x y :=
by rw [←is_scalar_tower.algebra_map_smul R a x, polar_smul_left, algebra.smul_def]

@[simp]
lemma polar_smul_right_of_tower (a : S) (x y : M) :
  polar Q x (a • y) = a • polar Q x y :=
by rw [←is_scalar_tower.algebra_map_smul R a y, polar_smul_right, algebra.smul_def]

/-- An alternative constructor to `quadratic_form.mk`, for rings where `polar` can be used. -/
@[simps]
def of_polar (to_fun : M → R) (to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x)
  (polar_add_left : ∀ (x x' y : M), polar to_fun (x + x') y = polar to_fun x y + polar to_fun x' y)
  (polar_smul_left : ∀ (a : R) (x y : M), polar to_fun (a • x) y = a • polar to_fun x y) :
  quadratic_form R M :=
{ to_fun := to_fun,
  to_fun_smul := to_fun_smul,
  exists_companion' := ⟨
    { bilin := polar to_fun,
      bilin_add_left := polar_add_left,
      bilin_smul_left := polar_smul_left,
      bilin_add_right := λ x y z, by simp_rw [polar_comm _ x, polar_add_left],
      bilin_smul_right := λ r x y, by simp_rw [polar_comm _ x, polar_smul_left, smul_eq_mul] },
    λ x y, by rw [bilin_form.coe_fn_mk, polar, sub_sub, add_sub_cancel'_right]⟩ }

/-- In a ring the companion bilinear form is unique and equal to `quadratic_form.polar`. -/
lemma some_exists_companion : Q.exists_companion.some = polar_bilin Q :=
bilin_form.ext $ λ x y,
  by rw [polar_bilin_apply, polar, Q.exists_companion.some_spec, sub_sub, add_sub_cancel']

end ring

section semiring_operators
variables [semiring R] [add_comm_monoid M] [module R M]

section has_smul

variables [monoid S] [distrib_mul_action S R] [smul_comm_class S R R]

/-- `quadratic_form R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `algebra.id`. -/
instance : has_smul S (quadratic_form R M) :=
⟨ λ a Q,
  { to_fun := a • Q,
    to_fun_smul := λ b x, by rw [pi.smul_apply, map_smul, pi.smul_apply, mul_smul_comm],
    exists_companion' := let ⟨B, h⟩ := Q.exists_companion in ⟨a • B,
      by simp [h]⟩ } ⟩

@[simp] lemma coe_fn_smul (a : S) (Q : quadratic_form R M) : ⇑(a • Q) = a • Q := rfl

@[simp] lemma smul_apply (a : S) (Q : quadratic_form R M) (x : M) :
  (a • Q) x = a • Q x := rfl

end has_smul

instance : has_zero (quadratic_form R M) :=
⟨ { to_fun := λ x, 0,
    to_fun_smul := λ a x, by simp only [mul_zero],
    exists_companion' := ⟨0, λ x y, by simp only [add_zero, bilin_form.zero_apply]⟩ } ⟩

@[simp] lemma coe_fn_zero : ⇑(0 : quadratic_form R M) = 0 := rfl

@[simp] lemma zero_apply (x : M) : (0 : quadratic_form R M) x = 0 := rfl

instance : inhabited (quadratic_form R M) := ⟨0⟩

instance : has_add (quadratic_form R M) :=
⟨ λ Q Q',
  { to_fun := Q + Q',
    to_fun_smul := λ a x,
      by simp only [pi.add_apply, map_smul, mul_add],
    exists_companion' :=
      let ⟨B, h⟩ := Q.exists_companion, ⟨B', h'⟩ := Q'.exists_companion in
      ⟨B + B', λ x y, by simp_rw [pi.add_apply, h, h', bilin_form.add_apply, add_add_add_comm] ⟩ } ⟩

@[simp] lemma coe_fn_add (Q Q' : quadratic_form R M) : ⇑(Q + Q') = Q + Q' := rfl

@[simp] lemma add_apply (Q Q' : quadratic_form R M) (x : M) : (Q + Q') x = Q x + Q' x := rfl

instance : add_comm_monoid (quadratic_form R M) :=
fun_like.coe_injective.add_comm_monoid _ coe_fn_zero coe_fn_add (λ _ _, coe_fn_smul _ _)

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

@[simp] lemma coe_fn_sum {ι : Type*} (Q : ι → quadratic_form R M) (s : finset ι) :
  ⇑(∑ i in s, Q i) = ∑ i in s, Q i :=
(coe_fn_add_monoid_hom : _ →+ (M → R)).map_sum Q s

@[simp] lemma sum_apply {ι : Type*} (Q : ι → quadratic_form R M) (s : finset ι) (x : M) :
  (∑ i in s, Q i) x = ∑ i in s, Q i x :=
(eval_add_monoid_hom x : _ →+ R).map_sum Q s

end sum

instance [monoid S] [distrib_mul_action S R] [smul_comm_class S R R] :
  distrib_mul_action S (quadratic_form R M) :=
{ mul_smul := λ a b Q, ext (λ x, by simp only [smul_apply, mul_smul]),
  one_smul := λ Q, ext (λ x, by simp only [quadratic_form.smul_apply, one_smul]),
  smul_add := λ a Q Q', by { ext, simp only [add_apply, smul_apply, smul_add] },
  smul_zero := λ a, by { ext, simp only [zero_apply, smul_apply, smul_zero] }, }

instance [semiring S] [module S R] [smul_comm_class S R R] : module S (quadratic_form R M) :=
{ zero_smul := λ Q, by { ext, simp only [zero_apply, smul_apply, zero_smul] },
  add_smul := λ a b Q, by { ext, simp only [add_apply, smul_apply, add_smul] } }

end semiring_operators

section ring_operators
variables [ring R] [add_comm_group M] [module R M]

instance : has_neg (quadratic_form R M) :=
⟨ λ Q,
  { to_fun := -Q,
    to_fun_smul := λ a x,
      by simp only [pi.neg_apply, map_smul, mul_neg],
    exists_companion' :=
      let ⟨B, h⟩ := Q.exists_companion in
      ⟨-B, λ x y, by simp_rw [pi.neg_apply, h, bilin_form.neg_apply, neg_add] ⟩ } ⟩

@[simp] lemma coe_fn_neg (Q : quadratic_form R M) : ⇑(-Q) = -Q := rfl

@[simp] lemma neg_apply (Q : quadratic_form R M) (x : M) : (-Q) x = -Q x := rfl

instance : has_sub (quadratic_form R M) :=
⟨ λ Q Q', (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _) ⟩

@[simp] lemma coe_fn_sub (Q Q' : quadratic_form R M) : ⇑(Q - Q') = Q - Q' := rfl

@[simp] lemma sub_apply (Q Q' : quadratic_form R M) (x : M) : (Q - Q') x = Q x - Q' x := rfl

instance : add_comm_group (quadratic_form R M) :=
fun_like.coe_injective.add_comm_group _
  coe_fn_zero coe_fn_add coe_fn_neg coe_fn_sub (λ _ _, coe_fn_smul _ _) (λ _ _, coe_fn_smul _ _)

end ring_operators

section comp

variables [semiring R] [add_comm_monoid M] [module R M]
variables {N : Type v} [add_comm_monoid N] [module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : quadratic_form R N) (f : M →ₗ[R] N) :
  quadratic_form R M :=
{ to_fun := λ x, Q (f x),
  to_fun_smul := λ a x, by simp only [map_smul, f.map_smul],
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion in
    ⟨B.comp f f, λ x y, by simp_rw [f.map_add, h, bilin_form.comp_apply]⟩ }

@[simp] lemma comp_apply (Q : quadratic_form R N) (f : M →ₗ[R] N) (x : M) :
  (Q.comp f) x = Q (f x) := rfl

/-- Compose a quadratic form with a linear function on the left. -/
@[simps {simp_rhs := tt}]
def _root_.linear_map.comp_quadratic_form {S : Type*}
  [comm_semiring S] [algebra S R] [module S M] [is_scalar_tower S R M]
  (f : R →ₗ[S] S) (Q : quadratic_form R M) :
  quadratic_form S M :=
{ to_fun := λ x, f (Q x),
  to_fun_smul := λ b x, by rw [Q.map_smul_of_tower b x, f.map_smul, smul_eq_mul],
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion in
    ⟨f.comp_bilin_form B, λ x y, by simp_rw [h, f.map_add, linear_map.comp_bilin_form_apply]⟩ }

end comp

section comm_ring
variables [comm_semiring R] [add_comm_monoid M] [module R M]

/-- The product of linear forms is a quadratic form. -/
def lin_mul_lin (f g : M →ₗ[R] R) : quadratic_form R M :=
{ to_fun := f * g,
  to_fun_smul := λ a x,
    by { simp only [smul_eq_mul, ring_hom.id_apply, pi.mul_apply, linear_map.map_smulₛₗ], ring },
  exists_companion' := ⟨
    bilin_form.lin_mul_lin f g + bilin_form.lin_mul_lin g f, λ x y, by { simp, ring }⟩ }

@[simp]
lemma lin_mul_lin_apply (f g : M →ₗ[R] R) (x) : lin_mul_lin f g x = f x * g x := rfl

@[simp]
lemma add_lin_mul_lin (f g h : M →ₗ[R] R) :
  lin_mul_lin (f + g) h = lin_mul_lin f h + lin_mul_lin g h :=
ext (λ x, add_mul _ _ _)

@[simp]
lemma lin_mul_lin_add (f g h : M →ₗ[R] R) :
  lin_mul_lin f (g + h) = lin_mul_lin f g + lin_mul_lin f h :=
ext (λ x, mul_add _ _ _)

variables {N : Type v} [add_comm_monoid N] [module R N]

@[simp]
lemma lin_mul_lin_comp (f g : M →ₗ[R] R) (h : N →ₗ[R] M) :
  (lin_mul_lin f g).comp h = lin_mul_lin (f.comp h) (g.comp h) :=
rfl

variables {n : Type*}

/-- `sq` is the quadratic form mapping the vector `x : R₁` to `x * x` -/
@[simps]
def sq : quadratic_form R R :=
lin_mul_lin linear_map.id linear_map.id

/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj (i j : n) : quadratic_form R (n → R) :=
lin_mul_lin (@linear_map.proj _ _ _ (λ _, R) _ _ i) (@linear_map.proj _ _ _ (λ _, R) _ _ j)

@[simp]
lemma proj_apply (i j : n) (x : n → R) : proj i j x = x i * x j := rfl

end comm_ring

end quadratic_form

/-!
### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/


namespace bilin_form
open quadratic_form

section semiring

variables [semiring R] [add_comm_monoid M] [module R M]
variables {B : bilin_form R M}

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def to_quadratic_form (B : bilin_form R M) : quadratic_form R M :=
{ to_fun := λ x, B x x,
  to_fun_smul := λ a x, by simp only [mul_assoc, smul_right, smul_left],
  exists_companion' :=
    ⟨B + bilin_form.flip_hom ℕ B, λ x y, by { simp [add_add_add_comm, add_comm] }⟩ }

@[simp] lemma to_quadratic_form_apply (B : bilin_form R M) (x : M) :
  B.to_quadratic_form x = B x x :=
rfl

section
variables (R M)
@[simp] lemma to_quadratic_form_zero : (0 : bilin_form R M).to_quadratic_form = 0 := rfl
end

@[simp] lemma to_quadratic_form_add (B₁ B₂ : bilin_form R M) :
  (B₁ + B₂).to_quadratic_form = B₁.to_quadratic_form + B₂.to_quadratic_form := rfl

@[simp] lemma to_quadratic_form_smul [monoid S] [distrib_mul_action S R] [smul_comm_class S R R]
  (a : S) (B : bilin_form R M) :
  (a • B).to_quadratic_form = a • B.to_quadratic_form := rfl

section
variables (R M)
/-- `bilin_form.to_quadratic_form` as an additive homomorphism -/
@[simps] def to_quadratic_form_add_monoid_hom : bilin_form R M →+ quadratic_form R M :=
{ to_fun := to_quadratic_form,
  map_zero' := to_quadratic_form_zero _ _,
  map_add' := to_quadratic_form_add }
end

@[simp] lemma to_quadratic_form_list_sum (B : list (bilin_form R M)) :
  B.sum.to_quadratic_form = (B.map to_quadratic_form).sum :=
map_list_sum (to_quadratic_form_add_monoid_hom R M) B

@[simp] lemma to_quadratic_form_multiset_sum (B : multiset (bilin_form R M)) :
  B.sum.to_quadratic_form = (B.map to_quadratic_form).sum :=
map_multiset_sum (to_quadratic_form_add_monoid_hom R M) B

@[simp] lemma to_quadratic_form_sum {ι : Type*} (s : finset ι) (B : ι → bilin_form R M) :
  (∑ i in s, B i).to_quadratic_form = ∑ i in s, (B i).to_quadratic_form :=
map_sum (to_quadratic_form_add_monoid_hom R M) B s

@[simp] lemma to_quadratic_form_eq_zero {B : bilin_form R M} :
  B.to_quadratic_form = 0 ↔ B.is_alt :=
quadratic_form.ext_iff

end semiring

section ring
variables [ring R] [add_comm_group M] [module R M]
variables {B : bilin_form R M}

lemma polar_to_quadratic_form (x y : M) : polar (λ x, B x x) x y = B x y + B y x :=
by { simp only [add_assoc, add_sub_cancel', add_right, polar, add_left_inj, add_neg_cancel_left,
  add_left, sub_eq_add_neg _ (B y y), add_comm (B y x) _] }

@[simp] lemma to_quadratic_form_neg (B : bilin_form R M) :
  (-B).to_quadratic_form = -B.to_quadratic_form := rfl

@[simp] lemma to_quadratic_form_sub (B₁ B₂ : bilin_form R M) :
  (B₁ - B₂).to_quadratic_form = B₁.to_quadratic_form - B₂.to_quadratic_form := rfl

end ring

end bilin_form

namespace quadratic_form
open bilin_form

section associated_hom
variables [ring R] [comm_ring R₁] [add_comm_group M] [module R M] [module R₁ M]
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
  ((•) : submonoid.center R → bilin_form R M → bilin_form R M)
    (⟨⅟2, λ x, (commute.one_right x).bit0_right.inv_of_right⟩) Q.polar_bilin,
  map_add' := λ Q Q', by { ext, simp only [bilin_form.add_apply, bilin_form.smul_apply, coe_fn_mk,
    polar_bilin_apply, polar_add, coe_fn_add, smul_add] },
  map_smul' := λ s Q, by { ext, simp only [ring_hom.id_apply, polar_smul, smul_comm s,
    polar_bilin_apply, coe_fn_mk, coe_fn_smul, bilin_form.smul_apply] } }

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
instance can_lift :
  can_lift (bilin_form R M) (quadratic_form R M) (associated_hom ℕ) bilin_form.is_symm :=
{ prf := λ B hB, ⟨B.to_quadratic_form, associated_left_inverse _ hB⟩ }

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
variables [comm_ring R₁] [add_comm_group M] [module R₁ M]
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
section semiring
variables [semiring R] [add_comm_monoid M] [module R M]

/-- An anisotropic quadratic form is zero only on zero vectors. -/
def anisotropic (Q : quadratic_form R M) : Prop := ∀ x, Q x = 0 → x = 0

lemma not_anisotropic_iff_exists (Q : quadratic_form R M) :
  ¬anisotropic Q ↔ ∃ x ≠ 0, Q x = 0 :=
by simp only [anisotropic, not_forall, exists_prop, and_comm]

lemma anisotropic.eq_zero_iff {Q : quadratic_form R M} (h : anisotropic Q) {x : M} :
  Q x = 0 ↔ x = 0 :=
⟨h x, λ h, h.symm ▸ map_zero Q⟩

end semiring
section ring
variables [ring R] [add_comm_group M] [module R M]

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
lemma nondegenerate_of_anisotropic [invertible (2 : R)] (Q : quadratic_form R M)
  (hB : Q.anisotropic) : Q.associated'.nondegenerate :=
begin
  intros x hx,
  refine hB _ _,
  rw ← hx x,
  exact (associated_eq_self_apply _ _ x).symm,
end

end ring

end anisotropic

section pos_def

variables {R₂ : Type u} [ordered_ring R₂] [add_comm_monoid M] [module R₂ M]
variables {Q₂ : quadratic_form R₂ M}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def pos_def (Q₂ : quadratic_form R₂ M) : Prop := ∀ x ≠ 0, 0 < Q₂ x

lemma pos_def.smul {R} [linear_ordered_comm_ring R] [module R M]
  {Q : quadratic_form R M} (h : pos_def Q) {a : R} (a_pos : 0 < a) : pos_def (a • Q) :=
λ x hx, mul_pos a_pos (h x hx)

variables {n : Type*}

lemma pos_def.nonneg {Q : quadratic_form R₂ M} (hQ : pos_def Q) (x : M) :
  0 ≤ Q x :=
(eq_or_ne x 0).elim (λ h, h.symm ▸ (map_zero Q).symm.le) (λ h, (hQ _ h).le)

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
λ x hx, mul_self_pos.2 (λ h, hx $ linear_map.ker_eq_bot'.mp hf _ h)

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
variables [comm_ring R₁] [add_comm_monoid M] [module R₁ M]

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

lemma quadratic_form.is_symm_to_matrix' (Q : quadratic_form R₁ (n → R₁)) :
  Q.to_matrix'.is_symm :=
begin
  ext i j,
  rw [to_matrix', bilin_form.to_matrix'_apply, bilin_form.to_matrix'_apply, associated_is_symm]
end

end

namespace quadratic_form

variables {n : Type w} [fintype n]
variables [comm_ring R₁] [decidable_eq n] [invertible (2 : R₁)]
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

end quadratic_form

namespace bilin_form
section semiring
variables [semiring R] [add_comm_monoid M] [module R M]

/-- A bilinear form is nondegenerate if the quadratic form it is associated with is anisotropic. -/
lemma nondegenerate_of_anisotropic
  {B : bilin_form R M} (hB : B.to_quadratic_form.anisotropic) : B.nondegenerate :=
λ x hx, hB _ (hx x)
end semiring

variables [ring R] [add_comm_group M] [module R M]

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
  unfreezingI { induction hd : finrank K V with d ih generalizing V },
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
    { exact hv₁ (ne_of_apply_ne _ hij), }, }
end

end bilin_form

namespace quadratic_form

open finset bilin_form

variables {M₁ : Type*} [semiring R] [comm_semiring R₁] [add_comm_monoid M] [add_comm_monoid M₁]
variables [module R M] [module R M₁]
variables {ι : Type*} [fintype ι] {v : basis ι R M}

/-- Given a quadratic form `Q` and a basis, `basis_repr` is the basis representation of `Q`. -/
noncomputable def basis_repr (Q : quadratic_form R M) (v : basis ι R M) :
  quadratic_form R (ι → R) :=
Q.comp v.equiv_fun.symm

@[simp]
lemma basis_repr_apply (Q : quadratic_form R M) (w : ι → R) :
  Q.basis_repr v w = Q (∑ i : ι, w i • v i) :=
by { rw ← v.equiv_fun_symm_apply, refl }

section

variables (R₁)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R₁` or
`[algebra S R₁]`, although this is stated more generally. -/
def weighted_sum_squares [monoid S] [distrib_mul_action S R₁]
  [smul_comm_class S R₁ R₁]
  (w : ι → S) : quadratic_form R₁ (ι → R₁) :=
∑ i : ι, w i • proj i i

end

@[simp]
lemma weighted_sum_squares_apply [monoid S] [distrib_mul_action S R₁] [smul_comm_class S R₁ R₁]
  (w : ι → S) (v : ι → R₁) :
  weighted_sum_squares R₁ w v = ∑ i : ι, w i • (v i * v i) :=
quadratic_form.sum_apply _ _ _

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
lemma basis_repr_eq_of_is_Ortho
  {R₁ M} [comm_ring R₁] [add_comm_group M] [module R₁ M] [invertible (2 : R₁)]
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
        show associated_hom R₁ Q (v j) (v i) = 0, from hv₂ hij.symm,
        mul_zero, mul_zero] },
end

end quadratic_form
