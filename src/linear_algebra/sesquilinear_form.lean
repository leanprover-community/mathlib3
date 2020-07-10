/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/
import algebra.module
import ring_theory.maps

/-!
# Sesquilinear form

This file defines a sesquilinear form over a module. The definition requires a ring antiautomorphism
on the scalar ring. Basic ideas such as
orthogonality are also introduced.

A sesquilinear form on an `R`-module `M`, is a function from `M × M` to `R, that is linear in the
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

universes u v

/-- A sesquilinear form over a module  -/
structure sesq_form (R : Type u) (M : Type v) [ring R] (I : R ≃+* Rᵒᵖ)
  [add_comm_group M] [module R M] :=
(sesq : M → M → R)
(sesq_add_left : ∀ (x y z : M), sesq (x + y) z = sesq x z + sesq y z)
(sesq_smul_left : ∀ (a : R) (x y : M), sesq (a • x) y = a * (sesq x y))
(sesq_add_right : ∀ (x y z : M), sesq x (y + z) = sesq x y + sesq x z)
(sesq_smul_right : ∀ (a : R) (x y : M), sesq x (a • y) = (I a).unop * (sesq x y))

namespace sesq_form

section general_ring
variables {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M]
variables {I : R ≃+* Rᵒᵖ} {S : sesq_form R M I}

instance : has_coe_to_fun (sesq_form R M I) :=
⟨_, λ S, S.sesq⟩

lemma add_left (x y z : M) : S (x + y) z = S x z + S y z := sesq_add_left S x y z

lemma smul_left (a : R) (x y : M) : S (a • x) y = a * (S x y) := sesq_smul_left S a x y

lemma add_right (x y z : M) : S x (y + z) = S x y + S x z := sesq_add_right S x y z

lemma smul_right (a : R) (x y : M) : S x (a • y) = (I a).unop * (S x y) := sesq_smul_right S a x y

lemma zero_left (x : M) : S 0 x = 0 :=
by { rw [←zero_smul R (0 : M), smul_left, zero_mul] }

lemma zero_right (x : M) : S x 0 = 0 :=
by { rw [←zero_smul R (0 : M), smul_right], simp }

lemma neg_left (x y : M) : S (-x) y = -(S x y) :=
by { rw [←@neg_one_smul R _ _, smul_left, neg_one_mul] }

lemma neg_right (x y : M) : S x (-y) = -(S x y) :=
by { rw [←@neg_one_smul R _ _, smul_right], simp }

lemma sub_left (x y z : M) :
S (x - y) z = S x z - S y z := by rw [sub_eq_add_neg, add_left, neg_left]; refl

lemma sub_right (x y z : M) :
S x (y - z) = S x y - S x z := by rw [sub_eq_add_neg, add_right, neg_right]; refl

variable {D : sesq_form R M I}
@[ext] lemma ext (H : ∀ (x y : M), S x y = D x y) : S = D :=
by {cases S, cases D, congr, funext, exact H _ _}

instance : add_comm_group (sesq_form R M I) :=
{ add := λ S D, { sesq := λ x y, S x y + D x y,
                  sesq_add_left := λ x y z, by {rw add_left, rw add_left, ac_refl},
                  sesq_smul_left := λ a x y, by {rw [smul_left, smul_left, mul_add]},
                  sesq_add_right := λ x y z, by {rw add_right, rw add_right, ac_refl},
                  sesq_smul_right := λ a x y, by {rw [smul_right, smul_right, mul_add]} },
  add_assoc := by {intros, ext,
    unfold coe_fn has_coe_to_fun.coe sesq coe_fn has_coe_to_fun.coe sesq, rw add_assoc},
  zero := { sesq := λ x y, 0,
            sesq_add_left := λ x y z, (add_zero 0).symm,
            sesq_smul_left := λ a x y, (mul_zero a).symm,
            sesq_add_right := λ x y z, (zero_add 0).symm,
            sesq_smul_right := λ a x y, (mul_zero (I a).unop).symm },
  zero_add := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw zero_add},
  add_zero := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw add_zero},
  neg := λ S, { sesq := λ x y, - (S.1 x y),
                sesq_add_left := λ x y z, by rw [sesq_add_left, neg_add],
                sesq_smul_left := λ a x y, by rw [sesq_smul_left, mul_neg_eq_neg_mul_symm],
                sesq_add_right := λ x y z, by rw [sesq_add_right, neg_add],
                sesq_smul_right := λ a x y, by rw [sesq_smul_right, mul_neg_eq_neg_mul_symm] },
  add_left_neg := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw neg_add_self},
  add_comm := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw add_comm} }

instance : inhabited (sesq_form R M I) := ⟨0⟩

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho (S : sesq_form R M I) (x y : M) : Prop :=
S x y = 0

lemma ortho_zero (x : M) :
is_ortho S (0 : M) x := zero_left x

end general_ring

section comm_ring

variables {R : Type*} [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {J : R ≃+* Rᵒᵖ} (F : sesq_form R M J) (f : M → M)

instance to_module : module R (sesq_form R M J) :=
{ smul := λ c S,
  { sesq := λ x y, c * S x y,
    sesq_add_left := λ x y z, by {unfold coe_fn has_coe_to_fun.coe sesq,
      rw [sesq_add_left, left_distrib]},
    sesq_smul_left := λ a x y, by {unfold coe_fn has_coe_to_fun.coe sesq,
      rw [sesq_smul_left, ←mul_assoc, mul_comm c, mul_assoc]},
    sesq_add_right := λ x y z, by {unfold coe_fn has_coe_to_fun.coe sesq,
      rw [sesq_add_right, left_distrib]},
    sesq_smul_right := λ a x y, by {unfold coe_fn has_coe_to_fun.coe sesq,
      rw [sesq_smul_right, ←mul_assoc, mul_comm c, mul_assoc], refl} },
  smul_add := λ c S D, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw left_distrib},
  add_smul := λ c S D, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw right_distrib},
  mul_smul := λ a c D, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw mul_assoc},
  one_smul := λ S, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw one_mul},
  zero_smul := λ S, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw zero_mul},
  smul_zero := λ S, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw mul_zero} }

end comm_ring

section domain

variables {R : Type*} [domain R]
  {M : Type v} [add_comm_group M] [module R M]
  {K : R ≃+* Rᵒᵖ} {G : sesq_form R M K}

theorem ortho_smul_left {x y : M} {a : R} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G (a • x) y) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_left, H, mul_zero] },
  { rw [smul_left, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }}
end

theorem ortho_smul_right {x y : M} {a : R} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G x (a • y)) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_right, H, mul_zero] },
  { rw [smul_right, mul_eq_zero] at H,
    cases H,
    { exfalso,
      -- `map_eq_zero_iff` doesn't fire here even if marked as a simp lemma, probably bcecause
      -- different instance paths
      simp only [opposite.unop_eq_zero_iff] at H,
      exact ha (K.map_eq_zero_iff.mp H), },
    { exact H }}
end

end domain

end sesq_form

namespace refl_sesq_form

open refl_sesq_form sesq_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_group M] [module R M]
variables {I : R ≃+* Rᵒᵖ} {S : sesq_form R M I}

/-- The proposition that a sesquilinear form is reflexive -/
def is_refl (S : sesq_form R M I) : Prop := ∀ (x y : M), S x y = 0 → S y x = 0

variable (H : is_refl S)

lemma eq_zero : ∀ {x y : M}, S x y = 0 → S y x = 0 := λ x y, H x y

lemma ortho_sym {x y : M} :
is_ortho S x y ↔ is_ortho S y x := ⟨eq_zero H, eq_zero H⟩

end refl_sesq_form

namespace sym_sesq_form

open sym_sesq_form sesq_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_group M] [module R M]
variables {I : R ≃+* Rᵒᵖ} {S : sesq_form R M I}

/-- The proposition that a sesquilinear form is symmetric -/
def is_sym (S : sesq_form R M I) : Prop := ∀ (x y : M), (I (S x y)).unop = S y x

variable (H : is_sym S)
include H

lemma sym (x y : M) : (I (S x y)).unop = S y x := H x y

lemma is_refl : refl_sesq_form.is_refl S := λ x y H1, by { rw [←H], simp [H1], }

lemma ortho_sym {x y : M} :
is_ortho S x y ↔ is_ortho S y x := refl_sesq_form.ortho_sym (is_refl H)

end sym_sesq_form

namespace alt_sesq_form

open alt_sesq_form sesq_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_group M] [module R M]
variables {I : R ≃+* Rᵒᵖ} {S : sesq_form R M I}

/-- The proposition that a sesquilinear form is alternating -/
def is_alt (S : sesq_form R M I) : Prop := ∀ (x : M), S x x = 0

variable (H : is_alt S)
include H

lemma self_eq_zero (x : M) : S x x = 0 := H x

lemma neg (x y : M) :
- S x y = S y x :=
begin
  have H1 : S (x + y) (x + y) = 0,
  { exact self_eq_zero H (x + y) },
  rw [add_left, add_right, add_right,
    self_eq_zero H, self_eq_zero H, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

end alt_sesq_form
