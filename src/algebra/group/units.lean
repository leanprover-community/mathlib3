/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes, Hölzl, Chris Hughes

Units (i.e., invertible elements) of a multiplicative monoid.
-/

import tactic.basic

universe u
variable {α : Type u}

structure units (α : Type u) [monoid α] :=
(val : α)
(inv : α)
(val_inv : val * inv = 1)
(inv_val : inv * val = 1)

namespace units
variables [monoid α] {a b c : units α}

instance : has_coe (units α) α := ⟨val⟩

@[extensionality] theorem ext : ∀ {a b : units α}, (a : α) = b → a = b
| ⟨v, i₁, vi₁, iv₁⟩ ⟨v', i₂, vi₂, iv₂⟩ e :=
  by change v = v' at e; subst v'; congr;
      simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

theorem ext_iff {a b : units α} : a = b ↔ (a : α) = b :=
⟨congr_arg _, ext⟩

instance [decidable_eq α] : decidable_eq (units α)
| a b := decidable_of_iff' _ ext_iff

protected def mul (u₁ u₂ : units α) : units α :=
⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
  have u₁.val * (u₂.val * u₂.inv) * u₁.inv = 1,
    by rw [u₂.val_inv]; rw [mul_one, u₁.val_inv],
  by simpa only [mul_assoc],
  have u₂.inv * (u₁.inv * u₁.val) * u₂.val = 1,
    by rw [u₁.inv_val]; rw [mul_one, u₂.inv_val],
  by simpa only [mul_assoc]⟩

protected def inv' (u : units α) : units α :=
⟨u.inv, u.val, u.inv_val, u.val_inv⟩

instance : has_mul (units α) := ⟨units.mul⟩
instance : has_one (units α) := ⟨⟨1, 1, mul_one 1, one_mul 1⟩⟩
instance : has_inv (units α) := ⟨units.inv'⟩

variables (a b)
@[simp] lemma coe_mul : (↑(a * b) : α) = a * b := rfl
@[simp] lemma coe_one : ((1 : units α) : α) = 1 := rfl
lemma val_coe : (↑a : α) = a.val := rfl
lemma coe_inv : ((a⁻¹ : units α) : α) = a.inv := rfl
@[simp] lemma inv_mul : (↑a⁻¹ * a : α) = 1 := inv_val _
@[simp] lemma mul_inv : (a * ↑a⁻¹ : α) = 1 := val_inv _

@[simp] lemma mul_inv_cancel_left (a : units α) (b : α) : (a:α) * (↑a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_inv, one_mul]

@[simp] lemma inv_mul_cancel_left (a : units α) (b : α) : (↑a⁻¹:α) * (a * b) = b :=
by rw [← mul_assoc, inv_mul, one_mul]

@[simp] lemma mul_inv_cancel_right (a : α) (b : units α) : a * b * ↑b⁻¹ = a :=
by rw [mul_assoc, mul_inv, mul_one]

@[simp] lemma inv_mul_cancel_right (a : α) (b : units α) : a * ↑b⁻¹ * b = a :=
by rw [mul_assoc, inv_mul, mul_one]

instance : group (units α) :=
by refine {mul := (*), one := 1, inv := has_inv.inv, ..};
  { intros, apply ext, simp only [coe_mul, coe_one,
      mul_assoc, one_mul, mul_one, inv_mul] }

instance {α} [comm_monoid α] : comm_group (units α) :=
{ mul_comm := λ u₁ u₂, ext $ mul_comm _ _, ..units.group }

instance [has_repr α] : has_repr (units α) := ⟨repr ∘ val⟩

@[simp] theorem mul_left_inj (a : units α) {b c : α} : (a:α) * b = a * c ↔ b = c :=
⟨λ h, by simpa only [inv_mul_cancel_left] using congr_arg ((*) ↑(a⁻¹ : units α)) h, congr_arg _⟩

@[simp] theorem mul_right_inj (a : units α) {b c : α} : b * a = c * a ↔ b = c :=
⟨λ h, by simpa only [mul_inv_cancel_right] using congr_arg (* ↑(a⁻¹ : units α)) h, congr_arg _⟩

end units

theorem nat.units_eq_one (u : units ℕ) : u = 1 :=
units.ext $ nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

def units.mk_of_mul_eq_one [comm_monoid α] (a b : α) (hab : a * b = 1) : units α :=
⟨a, b, hab, (mul_comm b a).trans hab⟩


section monoid
  variables [monoid α] {a b c : α}

  /-- Partial division. It is defined when the
    second argument is invertible, and unlike the division operator
    in `division_ring` it is not totalized at zero. -/
  def divp (a : α) (u) : α := a * (u⁻¹ : units α)

  infix ` /ₚ `:70 := divp

  @[simp] theorem divp_self (u : units α) : (u : α) /ₚ u = 1 := units.mul_inv _

  @[simp] theorem divp_one (a : α) : a /ₚ 1 = a := mul_one _

  theorem divp_assoc (a b : α) (u : units α) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _

  @[simp] theorem divp_mul_cancel (a : α) (u : units α) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans $ by rw [units.inv_mul, mul_one]

  @[simp] theorem mul_divp_cancel (a : α) (u : units α) : (a * u) /ₚ u = a :=
  (mul_assoc _ _ _).trans $ by rw [units.mul_inv, mul_one]

  @[simp] theorem divp_right_inj (u : units α) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  units.mul_right_inj _

  theorem divp_eq_one (a : α) (u : units α) : a /ₚ u = 1 ↔ a = u :=
  (units.mul_right_inj u).symm.trans $ by rw [divp_mul_cancel, one_mul]

  @[simp] theorem one_divp (u : units α) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _

end monoid

section group
  variables [group α]

  instance : has_lift α (units α) :=
  ⟨λ a, ⟨a, a⁻¹, mul_inv_self _, inv_mul_self _⟩⟩
end group
