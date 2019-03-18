/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow 
-/

import algebra.module ring_theory.ring_involution

open module ring_invo

class sesq_form (α : Type*) (β : Type*) [ring α] (Hi : ring_invo α) [add_comm_group β] [module α β] := 
(sesq : β → β → α)
(sesq_add_left : ∀ (x y z : β), sesq (x + y) z = sesq x z + sesq y z)
(sesq_smul_left : ∀ (a : α) (x y : β), sesq (a • x) y = a * (sesq x y))
(sesq_add_right : ∀ (x y z : β), sesq x (y + z) = sesq x y + sesq x z)
(sesq_smul_right : ∀ (a : α) (x y : β), sesq x (a • y) = (Hi a) * (sesq x y))  

namespace sesq_form

open sesq_form

variables {α : Type*} {β : Type*} [ring α] {Hi : ring_invo α} [add_comm_group β] [module α β] [sesq_form α β Hi]

lemma zero_sesq (x : β) :
sesq Hi 0 x = 0 := by rw [←@zero_smul α _ _, sesq_smul_left, ring.zero_mul]; exact 0

lemma sesq_zero (x : β) :
sesq Hi x 0 = 0 := by rw [←@zero_smul α _ _, sesq_smul_right, map_zero, ring.zero_mul]; exact 0

lemma sesq_neg_left (x y : β) : 
sesq Hi (-x) y = -(sesq Hi x y : α) := by rw [←@neg_one_smul α _ _, sesq_smul_left, neg_one_mul]

lemma sesq_neg_right (x y : β) : 
sesq Hi x (-y) = -(sesq Hi x y) := by rw [←@neg_one_smul α _ _, sesq_smul_right, map_neg, ring_invo.map_one, neg_one_mul]

lemma sesq_sub_left (x y z : β) :
sesq Hi (x - y) z = sesq Hi x z - sesq Hi y z := by rw [sub_eq_add_neg, sesq_add_left, sesq_neg_left]; refl

lemma sesq_sub_right (x y z : β) :
sesq Hi x (y - z) = sesq Hi x y - sesq Hi x z := by rw [sub_eq_add_neg, sesq_add_right, sesq_neg_right]; refl

def is_ortho (Hi : ring_invo α) [sesq_form α β Hi] (x y : β) : Prop := sesq Hi x y = 0

lemma ortho_zero (x : β) : is_ortho Hi 0 x := zero_sesq x 

variables {γ : Type*} [domain γ] {He : ring_invo γ} [module γ β] [sesq_form γ β He]

theorem ortho_smul_left {x y : β} {a : γ} (ha : a ≠ 0) : 
(is_ortho He x y) ↔ (is_ortho He (a • x) y) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [sesq_smul_left, H, ring.mul_zero] },

  { intros H,
    rw [sesq_smul_left, mul_eq_zero] at H,
    cases H, 
    { trivial }, 

    { exact H }} 
end

theorem ortho_smul_right {x y : β} {a : γ} (ha : a ≠ 0) : 
(is_ortho He x y) ↔ (is_ortho He x (a • y)) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [sesq_smul_right, H, ring.mul_zero] },

  { intros H,
    rw [sesq_smul_right, mul_eq_zero] at H,
    cases H, 
    { rw map_zero_iff at H,
        trivial }, 

    { exact H }}
end

end sesq_form

class reflx_sesq_form (α : Type*) (β : Type*) [ring α] (Hi : ring_invo α) [add_comm_group β] [module α β] extends sesq_form α β Hi := 
(is_reflx : ∀ {x y : β}, sesq x y = 0 → sesq y x = 0)

namespace reflx_sesq_form

open reflx_sesq_form sesq_form

variables {α : Type*} {β : Type*} [ring α] {Hi : ring_invo α} [add_comm_group β] [module α β] [reflx_sesq_form α β Hi]

lemma ortho_sym {x y : β} : 
is_ortho Hi x y ↔ is_ortho Hi y x := ⟨λ H, is_reflx H, λ H, is_reflx H⟩

end reflx_sesq_form

class sym_sesq_form (α : Type*) (β : Type*) [ring α] (Hi : ring_invo α) [add_comm_group β] [module α β] extends to_sesq_form : sesq_form α β Hi := 
(map_sesq : ∀ (x y : β), Hi (sesq y x) = sesq x y)

namespace sym_sesq_form

open sym_sesq_form sesq_form

variables {α : Type*} {β : Type*} [ring α] {Hi : ring_invo α} [add_comm_group β] [module α β] [sym_sesq_form α β Hi]

instance reflx_sesq_form : 
reflx_sesq_form α β Hi :=
⟨λ x y H, (map_zero_iff Hi).mp (( eq_comm.mp (map_sesq Hi x y)) ▸ (H))⟩ 

def ortho_sym {x y : β} : 
is_ortho Hi x y ↔ is_ortho Hi y x := reflx_sesq_form.ortho_sym

end sym_sesq_form
