/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import algebra.module

universes u v

class bilin_form (α : Type u) (β : Type v) [ring α] [add_comm_group β] [module α β] :=
(bilin : β → β → α)
(bilin_add_left : ∀ (x y z : β), bilin (x + y) z = bilin x z + bilin y z)
(bilin_smul_left : ∀ (a : α) (x y : β), bilin (a • x) y = a * (bilin x y))
(bilin_add_right : ∀ (x y z : β), bilin x (y + z) = bilin x y + bilin x z)
(bilin_smul_right : ∀ (a : α) (x y : β), bilin x (a • y) = a * (bilin x y))

namespace bilin_form

open bilin_form

variables {α : Type u} {β : Type v} [ring α] [add_comm_group β] [module α β] [bilin_form α β]

instance module : module α β := by apply_instance

lemma zero_bilin (x : β) :
bilin α 0 x = 0 := by rw [←@zero_smul α _ _ _ _ (0 : β), bilin_smul_left, zero_mul]

lemma bilin_zero (x : β) :
bilin α x 0 = 0 := by rw [←@zero_smul _ _ _ _ _ (0 : β), bilin_smul_right, ring.zero_mul]

lemma bilin_neg_left (x y : β) :
bilin α (-x) y = -(bilin α x y) := by rw [←@neg_one_smul α _ _, bilin_smul_left, neg_one_mul]

lemma bilin_neg_right (x y : β) :
bilin α x (-y) = -(bilin α x y) := by rw [←@neg_one_smul α _ _, bilin_smul_right, neg_one_mul]

lemma bilin_sub_left (x y z : β) :
bilin α (x - y) z = bilin α x z - bilin α y z := by rw [sub_eq_add_neg, bilin_add_left, bilin_neg_left]; refl

lemma bilin_sub_right (x y z : β) :
bilin α x (y - z) = bilin α x y - bilin α x z := by rw [sub_eq_add_neg, bilin_add_right, bilin_neg_right]; refl

def is_ortho (α : Type u) [ring α] [module α β] [bilin_form α β] (x y : β) : Prop :=
bilin α x y = 0

lemma ortho_zero (x : β) :
is_ortho α (0 : β) x := zero_bilin x

variables {γ : Type*} [domain γ] [module γ β] [bilin_form γ β]

theorem ortho_mul_left {x y : β} {a : γ} (ha : a ≠ 0) :
(is_ortho γ x y) ↔ (is_ortho γ (a • x) y) :=
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
(is_ortho γ x y) ↔ (is_ortho γ x (a • y)) :=
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

end bilin_form

class reflx_bilin_form (α : Type*) (β : Type*) [ring α] [add_comm_group β] [module α β] extends bilin_form α β :=
(bilin_reflx : ∀ {x y : β}, bilin x y = 0 → bilin y x = 0)

namespace reflx_sesquilinear_form_space

open reflx_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] [reflx_bilin_form α β]

lemma bilin_eq_zero {x y : β} : bilin α x y = 0 → bilin α y x = 0 := bilin_reflx

variables (x y : β)

lemma ortho_sym {x y : β} :
is_ortho α x y ↔ is_ortho α y x := ⟨λ H, bilin_eq_zero H, λ H, bilin_eq_zero H⟩

end reflx_sesquilinear_form_space

class sym_bilin_form (α : Type*) (β : Type*) [ring α] [add_comm_group β] [module α β] extends bilin_form α β :=
(bilin_sym : ∀ (x y : β), bilin x y = bilin y x)

namespace sym_sesquilinear_form_space

open sym_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] [sym_bilin_form α β]

instance reflx_bilin_form :
reflx_bilin_form α β := ⟨λ x y H, ((@bilin_sym α _ _ _ _ _ x y) ▸ H)⟩

lemma ortho_sym {x y : β} :
is_ortho α x y ↔ is_ortho α y x := reflx_sesquilinear_form_space.ortho_sym

end sym_sesquilinear_form_space

class alt_bilin_form (α : Type*) (β : Type*) [ring α] [add_comm_group β] [module α β] extends bilin_form α β :=
(bilin_alt : ∀ (x : β), bilin x x = 0)

namespace alt_bilin_form

open alt_bilin_form bilin_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] [alt_bilin_form α β]

instance has_coe_to_bilin_form : has_coe (alt_bilin_form α β) (bilin_form α β) :=
⟨λ D, D.to_bilin_form⟩

lemma bilin_self (x : β) : bilin α x x = 0 := bilin_alt α x

lemma bilin_skew_sym (x y : β) :
bilin α x y = - bilin α y x :=
begin
  have H : bilin α (x + y) (x + y) = 0,
  { exact bilin_self (x + y)},
  rw [bilin_add_left, bilin_add_right, bilin_add_right,
    bilin_self, bilin_self, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_eq_neg] at H,
  exact H,
end

end alt_bilin_form
