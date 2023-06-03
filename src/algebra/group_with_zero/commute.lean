/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group_with_zero.semiconj
import algebra.group.commute
import tactic.nontriviality

/-!
# Lemmas about commuting elements in a `monoid_with_zero` or a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α M₀ G₀ M₀' G₀' F F' : Type*}

variables [monoid_with_zero M₀]

namespace ring
open_locale classical

lemma mul_inverse_rev' {a b : M₀} (h : commute a b) : inverse (a * b) = inverse b * inverse a :=
begin
  by_cases hab : is_unit (a * b),
  { obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab,
    rw [←units.coe_mul, inverse_unit, inverse_unit, inverse_unit, ←units.coe_mul,
      mul_inv_rev], },
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab),
  { rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]},
  { rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]},
end

lemma mul_inverse_rev {M₀} [comm_monoid_with_zero M₀] (a b : M₀) :
  ring.inverse (a * b) = inverse b * inverse a :=
mul_inverse_rev' (commute.all _ _)

end ring

lemma commute.ring_inverse_ring_inverse {a b : M₀} (h : commute a b) :
  commute (ring.inverse a) (ring.inverse b) :=
(ring.mul_inverse_rev' h.symm).symm.trans $ (congr_arg _ h.symm.eq).trans $ ring.mul_inverse_rev' h

namespace commute

@[simp] theorem zero_right [mul_zero_class G₀] (a : G₀) : commute a 0 := semiconj_by.zero_right a
@[simp] theorem zero_left [mul_zero_class G₀] (a : G₀) : commute 0 a := semiconj_by.zero_left a a

variables [group_with_zero G₀] {a b c : G₀}

@[simp] theorem inv_left_iff₀ : commute a⁻¹ b ↔ commute a b :=
semiconj_by.inv_symm_left_iff₀

theorem inv_left₀ (h : commute a b) : commute a⁻¹ b := inv_left_iff₀.2 h

@[simp] theorem inv_right_iff₀ : commute a b⁻¹ ↔ commute a b :=
semiconj_by.inv_right_iff₀

theorem inv_right₀ (h : commute a b) : commute a b⁻¹ := inv_right_iff₀.2 h

@[simp] theorem div_right (hab : commute a b) (hac : commute a c) :
  commute a (b / c) :=
hab.div_right hac

@[simp] theorem div_left (hac : commute a c) (hbc : commute b c) :
  commute (a / b) c :=
by { rw div_eq_mul_inv, exact hac.mul_left hbc.inv_left₀ }

end commute
