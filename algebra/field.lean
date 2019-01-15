/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import algebra.ring logic.basic
open set

universe u
variables {α : Type u}

instance division_ring.to_domain [s : division_ring α] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h,
    classical.by_contradiction $ λ hn,
      division_ring.mul_ne_zero (mt or.inl hn) (mt or.inr hn) h
  ..s }

namespace units
variables [division_ring α] {a b : α}

/-- Embed an element of a division ring into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : α) (ha : a ≠ 0) : units α :=
⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

@[simp] theorem inv_eq_inv (u : units α) : (↑u⁻¹ : α) = u⁻¹ :=
(mul_left_inj u).1 $ by rw [units.mul_inv, mul_inv_cancel]; apply units.ne_zero

@[simp] theorem mk0_val (ha : a ≠ 0) : (mk0 a ha : α) = a := rfl

@[simp] theorem mk0_inv (ha : a ≠ 0) : ((mk0 a ha)⁻¹ : α) = a⁻¹ := rfl

@[simp] lemma units.mk0_inj [field α] {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
  units.mk0 a ha = units.mk0 b hb ↔ a = b :=
⟨λ h, by injection h, λ h, units.ext h⟩

end units

section division_ring
variables [s : division_ring α] {a b c : α}
include s

lemma div_eq_mul_inv : a / b = a * b⁻¹ := rfl

attribute [simp] div_one zero_div div_self

theorem divp_eq_div (a : α) (u : units α) : a /ₚ u = a / u :=
congr_arg _ $ units.inv_eq_inv _

@[simp] theorem divp_mk0 (a : α) {b : α} (hb : b ≠ 0) :
  a /ₚ units.mk0 b hb = a / b :=
divp_eq_div _ _

lemma inv_div (ha : a ≠ 0) (hb : b ≠ 0) : (a / b)⁻¹ = b / a :=
(mul_inv_eq (inv_ne_zero hb) ha).trans $ by rw division_ring.inv_inv hb; refl

lemma inv_div_left (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ / b = (b * a)⁻¹ :=
(mul_inv_eq ha hb).symm

lemma neg_inv (h : a ≠ 0) : - a⁻¹ = (- a)⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div _ h]

lemma division_ring.inv_comm_of_comm (h : a ≠ 0) (H : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
begin
  have : a⁻¹ * (b * a) * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ :=
    congr_arg (λ x:α, a⁻¹ * x * a⁻¹) H.symm,
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one,
       ← mul_assoc, inv_mul_cancel, one_mul] at this; exact h
end

lemma div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 :=
division_ring.mul_ne_zero ha (inv_ne_zero hb)

lemma div_ne_zero_iff (hb : b ≠ 0) : a / b ≠ 0 ↔ a ≠ 0 :=
⟨mt (λ h, by rw [h, zero_div]), λ ha, div_ne_zero ha hb⟩

lemma div_eq_zero_iff (hb : b ≠ 0) : a / b = 0 ↔ a = 0 :=
by haveI := classical.prop_decidable; exact
not_iff_not.1 (div_ne_zero_iff hb)

lemma add_div (a b c : α) : (a + b) / c = a / c + b / c :=
(div_add_div_same _ _ _).symm

lemma div_right_inj (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
by rw [← divp_mk0 _ hc, ← divp_mk0 _ hc, divp_right_inj]

lemma sub_div (a b c : α) : (a - b) / c = a / c - b / c :=
(div_sub_div_same _ _ _).symm

lemma division_ring.inv_inj (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ = b⁻¹ ↔ a = b :=
⟨λ h, by rw [← division_ring.inv_inv ha, ← division_ring.inv_inv hb, h], congr_arg (λx,x⁻¹)⟩

lemma division_ring.inv_eq_iff (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ = b ↔ b⁻¹ = a :=
by rw [← division_ring.inv_inj (inv_ne_zero ha) hb,
       eq_comm, division_ring.inv_inv ha]

lemma div_neg (a : α) (hb : b ≠ 0) : a / -b = -(a / b) :=
by rw [← division_ring.neg_div_neg_eq _ (neg_ne_zero.2 hb), neg_neg, neg_div]

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
⟨λ h, by rw [← h, div_mul_cancel _ hb],
 λ h, by rw [← h, mul_div_cancel _ hb]⟩

end division_ring

instance field.to_integral_domain [F : field α] : integral_domain α :=
{ ..F, ..division_ring.to_domain }

section
variables [field α] {a b c d : α}

lemma div_eq_inv_mul : a / b = b⁻¹ * a := mul_comm _ _

lemma inv_add_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

lemma inv_sub_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]

lemma mul_div_right_comm (a b c : α) : (a * b) / c = (a / c) * b :=
(div_mul_eq_mul_div _ _ _).symm

lemma mul_comm_div (a b c : α) : (a / b) * c = a * (c / b) :=
by rw [← mul_div_assoc, mul_div_right_comm]

lemma div_mul_comm (a b c : α) : (a / b) * c = (c / b) * a :=
by rw [div_mul_eq_mul_div, mul_comm, mul_div_right_comm]

lemma mul_div_comm (a b c : α) : a * (b / c) = b * (a / c) :=
by rw [← mul_div_assoc, mul_comm, mul_div_assoc]

lemma field.div_right_comm (a : α) (hb : b ≠ 0) (hc : c ≠ 0) : (a / b) / c = (a / c) / b :=
by rw [field.div_div_eq_div_mul _ hb hc, field.div_div_eq_div_mul _ hc hb, mul_comm]

lemma field.div_div_div_cancel_right (a : α) (hb : b ≠ 0) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
by rw [field.div_div_eq_mul_div _ hb hc, div_mul_cancel _ hc]

lemma field.div_mul_div_cancel (a : α) (hb : b ≠ 0) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
by rw [← mul_div_assoc, div_mul_cancel _ hc]

lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
(domain.mul_right_inj (mul_ne_zero' hb hd)).symm.trans $
by rw [← mul_assoc, div_mul_cancel _ hb,
       ← mul_assoc, mul_right_comm, div_mul_cancel _ hd]

lemma field.div_div_cancel (ha : a ≠ 0) (hb : b ≠ 0) : a / (a / b) = b :=
by rw [div_eq_mul_inv, inv_div ha hb, mul_div_cancel' _ ha]

end

section
variables [discrete_field α] {a b c : α}

attribute [simp] inv_zero div_zero

lemma div_right_comm (a b c : α) : (a / b) / c = (a / c) / b :=
if b0 : b = 0 then by simp only [b0, div_zero, zero_div] else
if c0 : c = 0 then by simp only [c0, div_zero, zero_div] else
field.div_right_comm _ b0 c0

lemma div_div_div_cancel_right (a b : α) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
if b0 : b = 0 then by simp only [b0, div_zero, zero_div] else
field.div_div_div_cancel_right _ b0 hc

lemma div_mul_div_cancel (a : α) (hb : b ≠ 0) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
if b0 : b = 0 then by simp only [b0, div_zero, mul_zero] else
field.div_mul_div_cancel _ b0 hc

lemma div_div_cancel (ha : a ≠ 0) : a / (a / b) = b :=
if b0 : b = 0 then by simp only [b0, div_zero] else
field.div_div_cancel ha b0

end

@[reducible] def is_field_hom {α β} [division_ring α] [division_ring β] (f : α → β) := is_ring_hom f

namespace is_field_hom
open is_ring_hom

section
variables {β : Type*} [division_ring α] [division_ring β]
variables (f : α → β) [is_field_hom f] {x y : α}

lemma map_ne_zero : f x ≠ 0 ↔ x ≠ 0 :=
⟨mt $ λ h, h.symm ▸ map_zero f,
 λ x0 h, one_ne_zero $ calc
    1 = f (x * x⁻¹) : by rw [mul_inv_cancel x0, map_one f]
  ... = 0 : by rw [map_mul f, h, zero_mul]⟩

lemma map_eq_zero : f x = 0 ↔ x = 0 :=
by haveI := classical.dec; exact not_iff_not.1 (map_ne_zero f)

lemma map_inv' (h : x ≠ 0) : f x⁻¹ = (f x)⁻¹ :=
(domain.mul_left_inj ((map_ne_zero f).2 h)).1 $
by rw [mul_inv_cancel ((map_ne_zero f).2 h), ← map_mul f, mul_inv_cancel h, map_one f]

lemma map_div' (h : y ≠ 0) : f (x / y) = f x / f y :=
(map_mul f).trans $ congr_arg _ $ map_inv' f h

lemma injective : function.injective f :=
(is_add_group_hom.injective_iff _).2
  (λ a ha, classical.by_contradiction $ λ ha0,
    by simpa [ha, is_ring_hom.map_mul f, is_ring_hom.map_one f, zero_ne_one]
        using congr_arg f (mul_inv_cancel ha0))

end

section
variables {β : Type*} [discrete_field α] [discrete_field β]
variables (f : α → β) [is_field_hom f] {x y : α}

lemma map_inv : f x⁻¹ = (f x)⁻¹ :=
classical.by_cases (by rintro rfl; simp only [map_zero f, inv_zero]) (map_inv' f)

lemma map_div : f (x / y) = f x / f y :=
(map_mul f).trans $ congr_arg _ $ map_inv f

end

end is_field_hom
