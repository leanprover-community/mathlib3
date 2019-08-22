/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import linear_algebra.tensor_product

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexivive, 
symmetric and alternating bilinear forms.

A bilinear form on an R-module V, is a function from V x V to R, 
that is linear in both arguments 
 
## Notations

Given any term B of type bilin_form, due to a coercion, can use 
the notation B x y to refer to the function field, ie. B x y = B.bilin x y.  

## References

* https://en.wikipedia.org/wiki/Bilinear_form

## Tags

Bilinear form, 
-/

universes u v

/-- A bilinear form over a module  -/
structure bilin_form (α : Type u) (β : Type v) [ring α] [add_comm_group β] [module α β] :=
(bilin : β → β → α)
(bilin_add_left : ∀ (x y z : β), bilin (x + y) z = bilin x z + bilin y z)
(bilin_smul_left : ∀ (a : α) (x y : β), bilin (a • x) y = a * (bilin x y))
(bilin_add_right : ∀ (x y z : β), bilin x (y + z) = bilin x y + bilin x z)
(bilin_smul_right : ∀ (a : α) (x y : β), bilin x (a • y) = a * (bilin x y))

def linear_map.to_bilin {χ : Type u} {β : Type v} [comm_ring χ] [add_comm_group β] [module χ β] 
(f : β →ₗ[χ] β →ₗ[χ] χ) : bilin_form χ β := 
{ bilin := λ x y, f x y,
  bilin_add_left := λ x y z, (linear_map.map_add f x y).symm ▸ linear_map.add_apply (f x) (f y) z,
  bilin_smul_left := λ a x y, by {rw linear_map.map_smul, rw linear_map.smul_apply, rw smul_eq_mul},
  bilin_add_right := λ x y z, linear_map.map_add (f x) y z,
  bilin_smul_right := λ a x y, linear_map.map_smul (f x) a y }

namespace bilin_form

variables {α : Type u} {β : Type v} [ring α] [add_comm_group β] [module α β] {B : bilin_form α β}

instance : has_coe_to_fun (bilin_form α β) :=
⟨_, λ B, B.bilin⟩

lemma add_left (x y z : β) : B (x + y) z = B x z + B y z := bilin_add_left B x y z

lemma smul_left (a : α) (x y : β) : B (a • x) y = a * (B x y) := bilin_smul_left B a x y 

lemma add_right (x y z : β) : B x (y + z) = B x y + B x z := bilin_add_right B x y z

lemma smul_right (a : α) (x y : β) : B x (a • y) = a * (B x y) := bilin_smul_right B a x y

lemma zero_left (x : β) :
B 0 x = 0 := by {rw [←@zero_smul α _ _ _ _ (0 : β), smul_left, zero_mul]}

lemma zero_right (x : β) :
B x 0 = 0 := by rw [←@zero_smul _ _ _ _ _ (0 : β), smul_right, ring.zero_mul]

lemma neg_left (x y : β) :
B (-x) y = -(B x y) := by rw [←@neg_one_smul α _ _, smul_left, neg_one_mul]

lemma neg_right (x y : β) :
B x (-y) = -(B x y) := by rw [←@neg_one_smul α _ _, smul_right, neg_one_mul]

lemma sub_left (x y z : β) :
B (x - y) z = B x z - B y z := by rw [sub_eq_add_neg, add_left, neg_left]; refl

lemma sub_right (x y z : β) :
B x (y - z) = B x y - B x z := by rw [sub_eq_add_neg, add_right, neg_right]; refl 

variable {D : bilin_form α β}  
@[extensionality] lemma ext (H : ∀ (x y : β), B x y = D x y) : B = D := by {cases B, cases D, congr, funext, exact H _ _} 

instance : add_comm_group (bilin_form α β) :=
{ add := λ B D, { bilin := λ x y, B x y + D x y,
                  bilin_add_left := λ x y z, by {rw add_left, rw add_left, simp},
                  bilin_smul_left := λ a x y, by {rw [smul_left, smul_left, mul_add]}, 
                  bilin_add_right := λ x y z, by {rw add_right, rw add_right, simp},
                  bilin_smul_right := λ a x y, by {rw [smul_right, smul_right, mul_add]} }, 
  add_assoc := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin coe_fn has_coe_to_fun.coe bilin, rw add_assoc},
  zero := { bilin := λ x y, 0,
            bilin_add_left := λ x y z, (add_zero 0).symm,
            bilin_smul_left := λ a x y, (mul_zero a).symm,
            bilin_add_right := λ x y z, (zero_add 0).symm,
            bilin_smul_right := λ a x y, (mul_zero a).symm },
  zero_add := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_add},
  add_zero := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_zero},
  neg := λ B, { bilin := λ x y, - (B.1 x y), 
                bilin_add_left := λ x y z, by rw [bilin_add_left, neg_add],
                bilin_smul_left := λ a x y, by rw [bilin_smul_left, mul_neg_eq_neg_mul_symm],
                bilin_add_right := λ x y z, by rw [bilin_add_right, neg_add],
                bilin_smul_right := λ a x y, by rw [bilin_smul_right, mul_neg_eq_neg_mul_symm] },
  add_left_neg := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw neg_add_self},
  add_comm := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_comm} }

section 

variables {χ : Type*} [comm_ring χ] [module χ β] (F : bilin_form χ β) (f : β → β)

instance to_module : module χ (bilin_form χ β) := 
{ smul := λ c B, { bilin := λ x y, c * B x y,
                    bilin_add_left := λ x y z, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_add_left, left_distrib]},
                    bilin_smul_left := λ a x y, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_smul_left, ←mul_assoc, mul_comm c, mul_assoc]},
                    bilin_add_right := λ x y z, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_add_right, left_distrib]},
                    bilin_smul_right := λ a x y, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_smul_right, ←mul_assoc, mul_comm c, mul_assoc]} },
  smul_add := λ c B D, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw left_distrib},
  add_smul := λ c B D, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw right_distrib},
  mul_smul := λ a c D, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw mul_assoc},
  one_smul := λ B, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw one_mul},
  zero_smul := λ B, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_mul},
  smul_zero := λ B, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw mul_zero} }

def to_linear_map : β →ₗ[χ] β →ₗ[χ] χ := 
linear_map.mk₂ χ F.1 (bilin_add_left F) (bilin_smul_left F) (bilin_add_right F) (bilin_smul_right F)  

def bilin_linear_map_equiv : (bilin_form χ β) ≃ₗ[χ] (β →ₗ[χ] β →ₗ[χ] χ) :=  
{ to_fun := to_linear_map,
  add := λ B D, rfl, 
  smul := λ a B, rfl,
  inv_fun := linear_map.to_bilin,
  left_inv := λ B, by {ext, refl},
  right_inv := λ B, by {ext, refl} }

end 

/-- The proposition that two elements of a bilinear form space are orthogonal -/
def is_ortho (B : bilin_form α β) (x y : β) : Prop :=
B x y = 0

lemma ortho_zero (x : β) :
is_ortho B (0 : β) x := zero_left x

section

variables {γ : Type*} [domain γ] [module γ β] {G : bilin_form γ β}

theorem ortho_smul_left {x y : β} {a : γ} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G (a • x) y) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_left, H, ring.mul_zero] },
  { rw [smul_left, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }}
end

theorem ortho_smul_right {x y : β} {a : γ} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G x (a • y)) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_right, H, ring.mul_zero] },
  { rw [smul_right, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }}
end

end

end bilin_form

namespace refl_bilin_form

open refl_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {B : bilin_form α β}

/-- The proposition that a bilinear form is reflexive -/
def is_refl (B : bilin_form α β) : Prop := ∀ (x y : β), B x y = 0 → B y x = 0

variable (H : is_refl B)

lemma eq_zero : ∀ {x y : β}, B x y = 0 → B y x = 0 := λ x y, H x y

lemma ortho_sym {x y : β} :
is_ortho B x y ↔ is_ortho B y x := ⟨eq_zero H, eq_zero H⟩

end refl_bilin_form

namespace sym_bilin_form

open sym_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {B : bilin_form α β}

/-- The proposition that a bilinear form is symmetric -/
def is_sym (B : bilin_form α β) : Prop := ∀ (x y : β), B x y = B y x

variable (H : is_sym B)

lemma sym (x y : β) : B x y = B y x := H x y 

lemma is_refl : refl_bilin_form.is_refl B := λ x y H1, H x y ▸ H1

lemma ortho_sym {x y : β} :
is_ortho B x y ↔ is_ortho B y x := refl_bilin_form.ortho_sym (is_refl H) 

end sym_bilin_form

namespace alt_bilin_form

open alt_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {B : bilin_form α β}

/-- The proposition that a bilinear form is alternating -/
def is_alt (B : bilin_form α β) : Prop := ∀ (x : β), B x x = 0

variable (H : is_alt B)
include H

lemma self_eq_zero (x : β) : B x x = 0 := H x

lemma neg (x y : β) :
- B x y = B y x :=
begin
  have H1 : B (x + y) (x + y) = 0,
  { exact self_eq_zero H (x + y) },
  rw [add_left, add_right, add_right,
    self_eq_zero H, self_eq_zero H, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

end alt_bilin_form
