/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import linear_algebra.tensor_product

set_option class.instance_max_depth 100

universes u v

structure bilin_form (α : Type u) (β : Type v) [ring α] [add_comm_group β] [module α β] :=
(bilin : β → β → α)
(bilin_add_left : ∀ (x y z : β), bilin (x + y) z = bilin x z + bilin y z)
(bilin_smul_left : ∀ (a : α) (x y : β), bilin (a • x) y = a * (bilin x y))
(bilin_add_right : ∀ (x y z : β), bilin x (y + z) = bilin x y + bilin x z)
(bilin_smul_right : ∀ (a : α) (x y : β), bilin x (a • y) = a * (bilin x y))

def linear_map.to_bilin {χ : Type u} {β : Type v} [comm_ring χ] [add_comm_group β] [module χ β] 
(f : β →ₗ[χ] β →ₗ[χ] χ) : bilin_form χ β := 
{ bilin := λ x y, f x y,
  bilin_add_left := λ x y z, eq_comm.mp (linear_map.map_add f x y) ▸ linear_map.add_apply (f x) (f y) z,
  bilin_smul_left := λ a x y, by {rw linear_map.map_smul, rw linear_map.smul_apply, rw smul_eq_mul},
  bilin_add_right := λ x y z, linear_map.map_add (f x) y z,
  bilin_smul_right := λ a x y, linear_map.map_smul (f x) a y
  }

namespace bilin_form

variables {α : Type u} {β : Type v} [ring α] [add_comm_group β] [module α β] {B : bilin_form α β}

instance module : module α β := by apply_instance

lemma zero_bilin (x : β) :
B.bilin 0 x = 0 := by {rw [←@zero_smul α _ _ _ _ (0 : β), bilin_smul_left, zero_mul]}

lemma bilin_zero (x : β) :
B.bilin x 0 = 0 := by rw [←@zero_smul _ _ _ _ _ (0 : β), bilin_smul_right, ring.zero_mul]

lemma bilin_neg_left (x y : β) :
B.bilin (-x) y = -(B.bilin x y) := by rw [←@neg_one_smul α _ _, bilin_smul_left, neg_one_mul]

lemma bilin_neg_right (x y : β) :
B.bilin x (-y) = -(B.bilin x y) := by rw [←@neg_one_smul α _ _, bilin_smul_right, neg_one_mul]

lemma bilin_sub_left (x y z : β) :
B.bilin (x - y) z = B.bilin x z - B.bilin y z := by rw [sub_eq_add_neg, bilin_add_left, bilin_neg_left]; refl

lemma bilin_sub_right (x y z : β) :
B.bilin x (y - z) = B.bilin x y - B.bilin x z := by rw [sub_eq_add_neg, bilin_add_right, bilin_neg_right]; refl 

variable {D : bilin_form α β}  
@[extensionality] lemma ext (H : ∀ (x y : β), B.1 x y = D.1 x y) : B = D := begin cases B, cases D, simp, funext, exact H _ _ end 

instance : add_comm_group (bilin_form α β) :=
{ add := λ B D, { bilin := λ x y, B.1 x y + D.1 x y,
                  bilin_add_left := λ x y z, by {rw bilin_add_left, rw bilin_add_left, simp},
                  bilin_smul_left := λ a x y, by {rw [bilin_smul_left, bilin_smul_left, mul_add]}, 
                  bilin_add_right := λ x y z, by {rw bilin_add_right, rw bilin_add_right, simp},
                  bilin_smul_right := λ a x y, by {rw [bilin_smul_right, bilin_smul_right, mul_add]}
                  }, 
  add_assoc := by {intros, ext, unfold bilin, rw add_assoc},
  zero := { bilin := λ x y, 0,
            bilin_add_left := λ x y z, eq_comm.mp (add_zero 0),
            bilin_smul_left := λ a x y, eq_comm.mp (mul_zero a),
            bilin_add_right := λ x y z, eq_comm.mp (zero_add 0),
            bilin_smul_right := λ a x y, eq_comm.mp (mul_zero a),
            },
  zero_add := by {intros, ext, unfold bilin, rw zero_add},
  add_zero := by {intros, ext, unfold bilin, rw add_zero},
  neg := λ B, { bilin := λ x y, - (B.1 x y), 
                bilin_add_left := λ x y z, by rw [bilin_add_left, neg_add],
                bilin_smul_left := λ a x y, by rw [bilin_smul_left, mul_neg_eq_neg_mul_symm],
                bilin_add_right := λ x y z, by rw [bilin_add_right, neg_add],
                bilin_smul_right := λ a x y, by rw [bilin_smul_right, mul_neg_eq_neg_mul_symm],
                },
  add_left_neg := by {intros, ext, unfold bilin, rw neg_add_self},
  add_comm := by {intros, ext, unfold bilin, rw add_comm},
}

section 

variables {χ : Type*} [comm_ring χ] [module χ β] (F : bilin_form χ β) (f : β → β)

instance base_ring_module : module χ χ := ring.to_module 
instance linear_map.to_module' : module χ (β →ₗ[χ] χ) := linear_map.module
instance linear_map.to_module₂ : module χ (β →ₗ[χ] β →ₗ[χ] χ) := linear_map.module

instance to_module : module χ (bilin_form χ β) := 
{ smul := λ c B, { bilin := λ x y, c * B.bilin x y,
                    bilin_add_left := λ x y z, by rw [bilin_add_left, left_distrib],
                    bilin_smul_left := λ a x y, by rw [bilin_smul_left, ←mul_assoc, mul_comm c, mul_assoc],
                    bilin_add_right := λ x y z, by rw [bilin_add_right, left_distrib],
                    bilin_smul_right := λ a x y, by rw [bilin_smul_right, ←mul_assoc, mul_comm c, mul_assoc],
                    },
  smul_add := λ c B D, by {ext, unfold bilin, rw left_distrib},
  add_smul := λ c B D, by {ext, unfold bilin, rw right_distrib},
  mul_smul := λ a c D, by {ext, unfold bilin, rw mul_assoc},
  one_smul := λ B, by {ext, unfold bilin, rw one_mul},
  zero_smul := λ B, by {ext, unfold bilin, rw zero_mul},
  smul_zero := λ B, by {ext, unfold bilin, rw mul_zero}, 
  }

def to_linear_map : β →ₗ[χ] β →ₗ[χ] χ := 
linear_map.mk₂ χ F.1 (bilin_add_left F) (bilin_smul_left F) (bilin_add_right F) (bilin_smul_right F)  

def bilin_linear_map_equiv : (bilin_form χ β) ≃ₗ[χ] (β →ₗ[χ] β →ₗ[χ] χ) :=  
{ to_fun := to_linear_map,
  add := λ B D, by refl, 
  smul := λ a B, by refl,
  inv_fun := linear_map.to_bilin,
  left_inv := λ B, by {ext, refl},
  right_inv := λ B, by {ext, refl},
}

end 

def is_ortho (B : bilin_form α β) (x y : β) : Prop :=
B.bilin x y = 0

lemma ortho_zero (x : β) :
is_ortho B (0 : β) x := zero_bilin x

section

variables {γ : Type*} [domain γ] [module γ β] {G : bilin_form γ β}

theorem ortho_mul_left {x y : β} {a : γ} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G (a • x) y) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [bilin_smul_left, H, ring.mul_zero] },

  { intros H,
    rw [bilin_smul_left, mul_eq_zero] at H,
    cases H,
    { trivial },

    { exact H }}
end

theorem ortho_mul_right {x y : β} {a : γ} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G x (a • y)) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [bilin_smul_right, H, ring.mul_zero] },

  { intros H,
    rw [bilin_smul_right, mul_eq_zero] at H,
    cases H,
    { trivial },

    { exact H }}
end

end

end bilin_form

structure refl_bilin_form (α : Type*) (β : Type*) [ring α] [add_comm_group β] [module α β] extends bilin_form α β :=
(bilin_refl : ∀ {x y : β}, bilin x y = 0 → bilin y x = 0)

namespace refl_sesquilinear_form_space

open refl_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {B : refl_bilin_form α β}

lemma bilin_eq_zero {x y : β} : B.bilin x y = 0 → B.bilin y x = 0 := bilin_refl B

variables (x y : β)

lemma ortho_sym (B : refl_bilin_form α β) {x y : β} :
is_ortho B.1 x y ↔ is_ortho B.1 y x := ⟨λ H, bilin_eq_zero H, λ H, bilin_eq_zero H⟩

end refl_sesquilinear_form_space

structure sym_bilin_form (α : Type*) (β : Type*) [ring α] [add_comm_group β] [module α β] extends bilin_form α β :=
(bilin_sym : ∀ (x y : β), bilin x y = bilin y x)

namespace sym_sesquilinear_form_space

open sym_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {B : sym_bilin_form α β}

def to_refl_bilin_form (B : sym_bilin_form α β):
refl_bilin_form α β := { bilin_refl := λ x y H, (@bilin_sym α _ _ _ _ B x y) ▸ H,
                          .. to_bilin_form B, }

lemma ortho_sym {x y : β} :
is_ortho B.1 x y ↔ is_ortho B.1 y x := refl_sesquilinear_form_space.ortho_sym (to_refl_bilin_form B) 

end sym_sesquilinear_form_space

structure alt_bilin_form (α : Type*) (β : Type*) [ring α] [add_comm_group β] [module α β] extends bilin_form α β :=
(bilin_alt : ∀ (x : β), bilin x x = 0)

namespace alt_bilin_form

open alt_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {B: alt_bilin_form α β}

instance has_coe_to_bilin_form : has_coe (alt_bilin_form α β) (bilin_form α β) :=
⟨λ D, D.to_bilin_form⟩

lemma bilin_self (x : β) : B.bilin x x = 0 := bilin_alt B x

lemma neg_bilin (x y : β) :
- B.bilin x y = B.bilin y x :=
begin
  have H : B.bilin (x + y) (x + y) = 0,
  { exact bilin_self (x + y)},
  rw [bilin_add_left, bilin_add_right, bilin_add_right,
    bilin_self, bilin_self, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_neg_eq] at H,
  exact H,
end

end alt_bilin_form
