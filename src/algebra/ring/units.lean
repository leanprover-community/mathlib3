/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.ring.inj_surj
import algebra.group.units

/-!
# Units in semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open function

namespace units

section has_distrib_neg
variables [monoid α] [has_distrib_neg α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : has_neg αˣ := ⟨λu, ⟨-↑u, -↑u⁻¹, by simp, by simp⟩ ⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast] protected theorem coe_neg (u : αˣ) : (↑-u : α) = -u := rfl

@[simp, norm_cast] protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 := rfl

instance : has_distrib_neg αˣ := units.ext.has_distrib_neg _ units.coe_neg units.coe_mul

@[field_simps] lemma neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = (-a) /ₚ u :=
by simp only [divp, neg_mul]

end has_distrib_neg

section ring

variables [ring α] {a b : α}

@[field_simps] lemma divp_add_divp_same (a b : α) (u : αˣ) :
  a /ₚ u + b /ₚ u = (a + b) /ₚ u :=
by simp only [divp, add_mul]

@[field_simps] lemma divp_sub_divp_same (a b : α) (u : αˣ) :
  a /ₚ u - b /ₚ u = (a - b) /ₚ u :=
by rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]

@[field_simps] lemma add_divp (a b : α) (u : αˣ)  : a + b /ₚ u = (a * u + b) /ₚ u :=
by simp only [divp, add_mul, units.mul_inv_cancel_right]

@[field_simps] lemma sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u :=
by simp only [divp, sub_mul, units.mul_inv_cancel_right]

@[field_simps] lemma divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u :=
by simp only [divp, add_mul, units.mul_inv_cancel_right]

@[field_simps] lemma divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u :=
begin
  simp only [divp, sub_mul, sub_right_inj],
  assoc_rw [units.mul_inv, mul_one],
end

end ring

end units

lemma is_unit.neg [monoid α] [has_distrib_neg α] {a : α} : is_unit a → is_unit (-a)
| ⟨x, hx⟩ := hx ▸ (-x).is_unit

@[simp]
lemma is_unit.neg_iff [monoid α] [has_distrib_neg α] (a : α) : is_unit (-a) ↔ is_unit a :=
⟨λ h, neg_neg a ▸ h.neg, is_unit.neg⟩

lemma is_unit.sub_iff [ring α] {x y : α} :
  is_unit (x - y) ↔ is_unit (y - x) :=
(is_unit.neg_iff _).symm.trans $ neg_sub x y ▸ iff.rfl

namespace units

@[field_simps] lemma divp_add_divp [comm_ring α] (a b : α) (u₁ u₂ : αˣ) :
a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) :=
begin
  simp only [divp, add_mul, mul_inv_rev, coe_mul],
  rw [mul_comm (↑u₁ * b), mul_comm b],
  assoc_rw [mul_inv, mul_inv, mul_one, mul_one],
end

@[field_simps] lemma divp_sub_divp [comm_ring α] (a b : α) (u₁ u₂ : αˣ) :
  (a /ₚ u₁) - (b /ₚ u₂) = ((a * u₂) - (u₁ * b)) /ₚ (u₁ * u₂) :=
by simp_rw [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

lemma add_eq_mul_one_add_div [semiring R] {a : Rˣ} {b : R} : ↑a + b = a * (1 + ↑a⁻¹ * b) :=
by rwa [mul_add, mul_one, ← mul_assoc, units.mul_inv, one_mul]

end units
