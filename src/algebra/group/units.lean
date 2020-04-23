/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes, Hölzl, Chris Hughes
-/
import logic.function
import algebra.group.to_additive

/-!
# Units (i.e., invertible elements) of a multiplicative monoid
-/

universe u
variable {α : Type u}

/-- Units of a monoid, bundled version. An element of a `monoid` is a unit if it has a two-sided
inverse. This version bundles the inverse element so that it can be computed. For a predicate
see `is_unit`. -/
structure units (α : Type u) [monoid α] :=
(val : α)
(inv : α)
(val_inv : val * inv = 1)
(inv_val : inv * val = 1)

/-- Units of an add_monoid, bundled version. An element of an add_monoid is a unit if it has a
    two-sided additive inverse. This version bundles the inverse element so that it can be
    computed. For a predicate see `is_add_unit`. -/
structure add_units (α : Type u) [add_monoid α] :=
(val : α)
(neg : α)
(val_neg : val + neg = 0)
(neg_val : neg + val = 0)

attribute [to_additive add_units] units

namespace units

variables [monoid α]

@[to_additive] instance : has_coe (units α) α := ⟨val⟩

@[simp, to_additive] lemma coe_mk (a : α) (b h₁ h₂) : ↑(units.mk a b h₁ h₂) = a := rfl

@[ext, to_additive] theorem ext :
  function.injective (coe : units α → α)
| ⟨v, i₁, vi₁, iv₁⟩ ⟨v', i₂, vi₂, iv₂⟩ e :=
  by change v = v' at e; subst v'; congr;
      simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

@[to_additive] theorem ext_iff {a b : units α} :
  a = b ↔ (a : α) = b :=
ext.eq_iff.symm

@[to_additive] instance [decidable_eq α] : decidable_eq (units α) := λ a b, decidable_of_iff' _ ext_iff

/-- Units of a monoid form a group. -/
@[to_additive] instance : group (units α) :=
{ mul := λ u₁ u₂, ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
    by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
    by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩,
  one := ⟨1, 1, one_mul 1, one_mul 1⟩,
  mul_one := λ u, ext $ mul_one u,
  one_mul := λ u, ext $ one_mul u,
  mul_assoc := λ u₁ u₂ u₃, ext $ mul_assoc u₁ u₂ u₃,
  inv := λ u, ⟨u.2, u.1, u.4, u.3⟩,
  mul_left_inv := λ u, ext u.inv_val }

variables (a b : units α) {c : units α}
@[simp, to_additive] lemma coe_mul : (↑(a * b) : α) = a * b := rfl
@[simp, to_additive] lemma coe_one : ((1 : units α) : α) = 1 := rfl
@[to_additive] lemma val_coe : (↑a : α) = a.val := rfl
@[to_additive] lemma coe_inv : ((a⁻¹ : units α) : α) = a.inv := rfl
@[simp, to_additive] lemma inv_mul : (↑a⁻¹ * a : α) = 1 := inv_val _
@[simp, to_additive] lemma mul_inv : (a * ↑a⁻¹ : α) = 1 := val_inv _

@[simp, to_additive] lemma mul_inv_cancel_left (a : units α) (b : α) : (a:α) * (↑a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_inv, one_mul]

@[simp, to_additive] lemma inv_mul_cancel_left (a : units α) (b : α) : (↑a⁻¹:α) * (a * b) = b :=
by rw [← mul_assoc, inv_mul, one_mul]

@[simp, to_additive] lemma mul_inv_cancel_right (a : α) (b : units α) : a * b * ↑b⁻¹ = a :=
by rw [mul_assoc, mul_inv, mul_one]

@[simp, to_additive] lemma inv_mul_cancel_right (a : α) (b : units α) : a * ↑b⁻¹ * b = a :=
by rw [mul_assoc, inv_mul, mul_one]

@[to_additive] instance : inhabited (units α) := ⟨1⟩

@[to_additive] instance {α} [comm_monoid α] : comm_group (units α) :=
{ mul_comm := λ u₁ u₂, ext $ mul_comm _ _, ..units.group }

@[to_additive] instance [has_repr α] : has_repr (units α) := ⟨repr ∘ val⟩

@[simp, to_additive] theorem mul_left_inj (a : units α) {b c : α} : (a:α) * b = a * c ↔ b = c :=
⟨λ h, by simpa only [inv_mul_cancel_left] using congr_arg ((*) ↑(a⁻¹ : units α)) h, congr_arg _⟩

@[simp, to_additive] theorem mul_right_inj (a : units α) {b c : α} : b * a = c * a ↔ b = c :=
⟨λ h, by simpa only [mul_inv_cancel_right] using congr_arg (* ↑(a⁻¹ : units α)) h, congr_arg _⟩

@[to_additive] theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
⟨λ h, by rw [h, inv_mul_cancel_right], λ h, by rw [← h, mul_inv_cancel_right]⟩

@[to_additive] theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
⟨λ h, by rw [h, mul_inv_cancel_left], λ h, by rw [← h, inv_mul_cancel_left]⟩

@[to_additive] theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
⟨λ h, by rw [← h, mul_inv_cancel_left], λ h, by rw [h, inv_mul_cancel_left]⟩

@[to_additive] theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
⟨λ h, by rw [← h, inv_mul_cancel_right], λ h, by rw [h, mul_inv_cancel_right]⟩

end units

theorem nat.units_eq_one (u : units ℕ) : u = 1 :=
units.ext $ nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

theorem nat.add_units_eq_zero (u : add_units ℕ) : u = 0 :=
add_units.ext $ (nat.eq_zero_of_add_eq_zero u.val_neg).1

/-- For `a, b` in a `comm_monoid` such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive "For `a, b` in an `add_comm_monoid` such that `a + b = 0`, makes an add_unit out of `a`."]
def units.mk_of_mul_eq_one [comm_monoid α] (a b : α) (hab : a * b = 1) :
  units α :=
⟨a, b, hab, (mul_comm b a).trans hab⟩

@[simp, to_additive] lemma units.coe_mk_of_mul_eq_one [comm_monoid α] {a b : α} (h : a * b = 1) :
  (units.mk_of_mul_eq_one a b h : α) = a := rfl

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

  @[simp] theorem divp_inv (u : units α) : a /ₚ u⁻¹ = a * u := rfl

  @[simp] theorem divp_mul_cancel (a : α) (u : units α) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans $ by rw [units.inv_mul, mul_one]

  @[simp] theorem mul_divp_cancel (a : α) (u : units α) : (a * u) /ₚ u = a :=
  (mul_assoc _ _ _).trans $ by rw [units.mul_inv, mul_one]

  @[simp] theorem divp_right_inj (u : units α) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  units.mul_right_inj _

  theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : units α) : (x /ₚ u₁) /ₚ u₂ = x /ₚ (u₂ * u₁) :=
  by simp only [divp, mul_inv_rev, units.coe_mul, mul_assoc]

  theorem divp_eq_iff_mul_eq {x : α} {u : units α} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_right_inj.symm.trans $ by rw [divp_mul_cancel]; exact ⟨eq.symm, eq.symm⟩

  theorem divp_eq_one_iff_eq {a : α} {u : units α} : a /ₚ u = 1 ↔ a = u :=
  (units.mul_right_inj u).symm.trans $ by rw [divp_mul_cancel, one_mul]

  @[simp] theorem one_divp (u : units α) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _

end monoid

section comm_monoid

variables [comm_monoid α]

theorem divp_eq_divp_iff {x y : α} {ux uy : units α} :
  x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux :=
by rw [divp_eq_iff_mul_eq, mul_comm, ← divp_assoc, divp_eq_iff_mul_eq, mul_comm y ux]

theorem divp_mul_divp (x y : α) (ux uy : units α) :
  (x /ₚ ux) * (y /ₚ uy) = (x * y) /ₚ (ux * uy) :=
by rw [← divp_divp_eq_divp_mul, divp_assoc, mul_comm x, divp_assoc, mul_comm]

end comm_monoid
