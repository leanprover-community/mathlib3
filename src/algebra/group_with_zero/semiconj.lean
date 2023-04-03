/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group_with_zero.units.basic
import algebra.group.semiconj

/-!
# Lemmas about semiconjugate elements in a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α M₀ G₀ M₀' G₀' F F' : Type*}

namespace semiconj_by

@[simp] lemma zero_right [mul_zero_class G₀] (a : G₀) : semiconj_by a 0 0 :=
by simp only [semiconj_by, mul_zero, zero_mul]

@[simp] lemma zero_left [mul_zero_class G₀] (x y : G₀) : semiconj_by 0 x y :=
by simp only [semiconj_by, mul_zero, zero_mul]

variables [group_with_zero G₀] {a x y x' y' : G₀}

@[simp] lemma inv_symm_left_iff₀ : semiconj_by a⁻¹ x y ↔ semiconj_by a y x :=
classical.by_cases
  (λ ha : a = 0, by simp only [ha, inv_zero, semiconj_by.zero_left])
  (λ ha, @units_inv_symm_left_iff _ _ (units.mk0 a ha) _ _)

lemma inv_symm_left₀ (h : semiconj_by a x y) : semiconj_by a⁻¹ y x :=
semiconj_by.inv_symm_left_iff₀.2 h

lemma inv_right₀ (h : semiconj_by a x y) : semiconj_by a x⁻¹ y⁻¹ :=
begin
  by_cases ha : a = 0,
  { simp only [ha, zero_left] },
  by_cases hx : x = 0,
  { subst x,
    simp only [semiconj_by, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h,
    simp [h.resolve_right ha] },
  { have := mul_ne_zero ha hx,
    rw [h.eq, mul_ne_zero_iff] at this,
    exact @units_inv_right _ _ _ (units.mk0 x hx) (units.mk0 y this.1) h },
end

@[simp] lemma inv_right_iff₀ : semiconj_by a x⁻¹ y⁻¹ ↔ semiconj_by a x y :=
⟨λ h, inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩

lemma div_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x / x') (y / y') :=
by { rw [div_eq_mul_inv, div_eq_mul_inv], exact h.mul_right h'.inv_right₀ }

end semiconj_by
