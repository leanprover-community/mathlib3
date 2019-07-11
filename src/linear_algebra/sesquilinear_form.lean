/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import algebra.module ring_theory.involution linear_algebra.tensor_product

open module ring_invo

universes u v

structure sesq_form (α : Type u) (β : Type v) [ring α] (I : ring_invo α) [add_comm_group β] [module α β] := 
(sesq : β → β → α)
(sesq_add_left : ∀ (x y z : β), sesq (x + y) z = sesq x z + sesq y z)
(sesq_smul_left : ∀ (a : α) (x y : β), sesq (a • x) y = a * (sesq x y))
(sesq_add_right : ∀ (x y z : β), sesq x (y + z) = sesq x y + sesq x z)
(sesq_smul_right : ∀ (a : α) (x y : β), sesq x (a • y) = (I a) * (sesq x y))  

namespace sesq_form

variables {α : Type u} {β : Type v} [ring α] [add_comm_group β] [module α β] {I : ring_invo α} {S : sesq_form α β I}

instance : has_coe_to_fun (sesq_form α β I) :=
⟨_, λ S, S.sesq⟩

lemma add_left (x y z : β) : S (x + y) z = S x z + S y z := sesq_add_left S x y z

lemma smul_left (a : α) (x y : β) : S (a • x) y = a * (S x y) := sesq_smul_left S a x y 

lemma add_right (x y z : β) : S x (y + z) = S x y + S x z := sesq_add_right S x y z

lemma smul_right (a : α) (x y : β) : S x (a • y) = (I a) * (S x y) := sesq_smul_right S a x y

lemma zero_left (x : β) :
S 0 x = 0 := by {rw [←@zero_smul α _ _ _ _ (0 : β), smul_left, zero_mul]}

lemma zero_right (x : β) :
S x 0 = 0 := by rw [←@zero_smul _ _ _ _ _ (0 : β), smul_right, map_zero, ring.zero_mul]

lemma neg_left (x y : β) :
S (-x) y = -(S x y) := by rw [←@neg_one_smul α _ _, smul_left, neg_one_mul]

lemma neg_right (x y : β) :
S x (-y) = -(S x y) := by rw [←@neg_one_smul α _ _, smul_right, map_neg_one, neg_one_mul]

lemma sub_left (x y z : β) :
S (x - y) z = S x z - S y z := by rw [sub_eq_add_neg, add_left, neg_left]; refl

lemma sub_right (x y z : β) :
S x (y - z) = S x y - S x z := by rw [sub_eq_add_neg, add_right, neg_right]; refl 

variable {D : sesq_form α β I}  
@[extensionality] lemma ext (H : ∀ (x y : β), S x y = D x y) : S = D := begin cases S, cases D, simp, funext, exact H _ _ end 

instance : add_comm_group (sesq_form α β I) :=
{ add := λ S D, { sesq := λ x y, S x y + D x y,
                  sesq_add_left := λ x y z, by {rw add_left, rw add_left, simp},
                  sesq_smul_left := λ a x y, by {rw [smul_left, smul_left, mul_add]}, 
                  sesq_add_right := λ x y z, by {rw add_right, rw add_right, simp},
                  sesq_smul_right := λ a x y, by {rw [smul_right, smul_right, mul_add]}
                  }, 
  add_assoc := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq coe_fn has_coe_to_fun.coe sesq, rw add_assoc},
  zero := { sesq := λ x y, 0,
            sesq_add_left := λ x y z, eq_comm.mp (add_zero 0),
            sesq_smul_left := λ a x y, eq_comm.mp (mul_zero a),
            sesq_add_right := λ x y z, eq_comm.mp (zero_add 0),
            sesq_smul_right := λ a x y, eq_comm.mp (mul_zero (I a)),
            },
  zero_add := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw zero_add},
  add_zero := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw add_zero},
  neg := λ S, { sesq := λ x y, - (S.1 x y), 
                sesq_add_left := λ x y z, by rw [sesq_add_left, neg_add],
                sesq_smul_left := λ a x y, by rw [sesq_smul_left, mul_neg_eq_neg_mul_symm],
                sesq_add_right := λ x y z, by rw [sesq_add_right, neg_add],
                sesq_smul_right := λ a x y, by rw [sesq_smul_right, mul_neg_eq_neg_mul_symm],
                },
  add_left_neg := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw neg_add_self},
  add_comm := by {intros, ext, unfold coe_fn has_coe_to_fun.coe sesq, rw add_comm},
}

section 

variables {χ : Type*} [comm_ring χ] [module χ β] {J : ring_invo χ} (F : sesq_form χ β J) (f : β → β)

instance to_module : module χ (sesq_form χ β J) := 
{ smul := λ c S, { sesq := λ x y, c * S x y,
                    sesq_add_left := λ x y z, by {unfold coe_fn has_coe_to_fun.coe sesq, rw [sesq_add_left, left_distrib]},
                    sesq_smul_left := λ a x y, by {unfold coe_fn has_coe_to_fun.coe sesq, rw [sesq_smul_left, ←mul_assoc, mul_comm c, mul_assoc]},
                    sesq_add_right := λ x y z, by {unfold coe_fn has_coe_to_fun.coe sesq, rw [sesq_add_right, left_distrib]},
                    sesq_smul_right := λ a x y, by {unfold coe_fn has_coe_to_fun.coe sesq, rw [sesq_smul_right, ←mul_assoc, mul_comm c, mul_assoc], refl},
                    },
  smul_add := λ c S D, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw left_distrib},
  add_smul := λ c S D, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw right_distrib},
  mul_smul := λ a c D, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw mul_assoc},
  one_smul := λ S, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw one_mul},
  zero_smul := λ S, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw zero_mul},
  smul_zero := λ S, by {ext, unfold coe_fn has_coe_to_fun.coe sesq, rw mul_zero}, 
  }

end 

def is_ortho (S : sesq_form α β I) (x y : β) : Prop :=
S x y = 0

lemma ortho_zero (x : β) :
is_ortho S (0 : β) x := zero_left x

section

variables {γ : Type*} [domain γ] [module γ β] {K : ring_invo γ} {G : sesq_form γ β K}

theorem ortho_smul_left {x y : β} {a : γ} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G (a • x) y) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [smul_left, H, ring.mul_zero] },

  { intros H,
    rw [smul_left, mul_eq_zero] at H,
    cases H,
    { trivial },

    { exact H }}
end

theorem ortho_smul_right {x y : β} {a : γ} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G x (a • y)) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [smul_right, H, ring.mul_zero] },

  { intros H,
    rw [smul_right, mul_eq_zero] at H,
    cases H,
    { rw map_zero_iff at H, trivial },

    { exact H }}
end

end

end sesq_form

namespace refl_sesq_form

open refl_sesq_form sesq_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {I : ring_invo α} {S : sesq_form α β I}

def is_refl (S : sesq_form α β I) : Prop := ∀ (x y : β), S x y = 0 → S y x = 0

variable (H : is_refl S)

lemma eq_zero : ∀ {x y : β}, S x y = 0 → S y x = 0 := λ x y, H x y

lemma ortho_sym {x y : β} :
is_ortho S x y ↔ is_ortho S y x := ⟨eq_zero H, eq_zero H⟩

end refl_sesq_form

namespace sym_sesq_form

open sym_sesq_form sesq_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {I : ring_invo α} {S : sesq_form α β I}

def is_sym (S : sesq_form α β I) : Prop := ∀ (x y : β), I (S x y) = S y x

variable (H : is_sym S)
include H

lemma sym (x y : β) : I (S x y) = S y x := H x y 

lemma is_refl : refl_sesq_form.is_refl S := λ x y H1, by rw [←H, map_zero_iff, H1] 

lemma ortho_sym {x y : β} :
is_ortho S x y ↔ is_ortho S y x := refl_sesq_form.ortho_sym (is_refl H) 

end sym_sesq_form

namespace alt_sesq_form

open alt_sesq_form sesq_form

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {I : ring_invo α} {S : sesq_form α β I}

def is_alt (S : sesq_form α β I) : Prop := ∀ (x : β), S x x = 0

variable (H : is_alt S)
include H

lemma self_eq_zero (x : β) : S x x = 0 := H x

lemma neg (x y : β) :
- S x y = S y x :=
begin
  have H1 : S (x + y) (x + y) = 0,
  { exact self_eq_zero H (x + y)},
  rw [add_left, add_right, add_right,
    self_eq_zero H, self_eq_zero H, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

end alt_sesq_form
