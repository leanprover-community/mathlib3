/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import algebra.ring logic.basic
open set

universe u
variables {α : Type u}

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_domain [s : division_ring α] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h,
    classical.by_contradiction $ λ hn,
      division_ring.mul_ne_zero (mt or.inl hn) (mt or.inr hn) h
  ..s }

@[simp] theorem inv_one [division_ring α] : (1⁻¹ : α) = 1 := by rw [inv_eq_one_div, one_div_one]

attribute [simp] inv_inv'

lemma inv_inv'' [division_ring α] (x : α) : x⁻¹⁻¹ = x :=
inv_inv'

lemma inv_involutive' [division_ring α] : function.involutive (has_inv.inv : α → α) :=
@inv_inv' _ _

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

@[simp] lemma mk0_coe (u : units α) (h : (u : α) ≠ 0) : mk0 (u : α) h = u :=
units.ext rfl

@[simp] lemma mk0_inj {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
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

lemma inv_div : (a / b)⁻¹ = b / a :=
(mul_inv' _ _).trans (by rw inv_inv'; refl)

lemma inv_div_left : a⁻¹ / b = (b * a)⁻¹ :=
(mul_inv' _ _).symm

lemma neg_inv : - a⁻¹ = (- a)⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

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

lemma division_ring.inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
⟨λ h, by rw [← inv_inv'' a, h, inv_inv''], congr_arg (λx,x⁻¹)⟩

lemma division_ring.inv_eq_iff  : a⁻¹ = b ↔ b⁻¹ = a :=
by rw [← division_ring.inv_inj, eq_comm, inv_inv'']

lemma div_neg (a : α) : a / -b = -(a / b) :=
by rw [← div_neg_eq_neg_div]

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
⟨λ h, by rw [← h, div_mul_cancel _ hb],
 λ h, by rw [← h, mul_div_cancel _ hb]⟩

end division_ring

@[priority 100] -- see Note [lower instance priority]
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

lemma field.div_right_comm (a : α) : (a / b) / c = (a / c) / b :=
by rw [div_div_eq_div_mul, div_div_eq_div_mul, mul_comm]

lemma field.div_div_div_cancel_right (a : α) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
by rw [div_div_eq_mul_div, div_mul_cancel _ hc]

lemma div_mul_div_cancel (a : α) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
by rw [← mul_div_assoc, div_mul_cancel _ hc]

lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
(domain.mul_right_inj (mul_ne_zero' hb hd)).symm.trans $
by rw [← mul_assoc, div_mul_cancel _ hb,
       ← mul_assoc, mul_right_comm, div_mul_cancel _ hd]

lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
by simpa using @div_eq_div_iff _ _ a b c 1 hb one_ne_zero

lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
by simpa using @div_eq_div_iff _ _ c 1 a b one_ne_zero hb

lemma field.div_div_cancel (ha : a ≠ 0) : a / (a / b) = b :=
by rw [div_eq_mul_inv, inv_div, mul_div_cancel' _ ha]

lemma add_div' (a b c : α) (hc : c ≠ 0) :
  b + a / c = (b * c + a) / c :=
by simpa using div_add_div b a one_ne_zero hc

lemma sub_div' (a b c : α) (hc : c ≠ 0) :
  b - a / c = (b * c - a) / c :=
by simpa using div_sub_div b a one_ne_zero hc

lemma div_add' (a b c : α) (hc : c ≠ 0) :
  a / c + b = (a + b * c) / c :=
by rwa [add_comm, add_div', add_comm]

lemma div_sub' (a b c : α) (hc : c ≠ 0) :
  a / c - b = (a - c * b) / c :=
by simpa using div_sub_div a b hc one_ne_zero

end

section
variables [field α] {a b c : α}

attribute [simp] inv_zero div_zero

@[simp] lemma inv_eq_zero {a : α} : a⁻¹ = 0 ↔ a = 0 :=
classical.by_cases (assume : a = 0, by simp [*])(assume : a ≠ 0, by simp [*, inv_ne_zero])

end

namespace ring_hom

section

variables {β : Type*} [division_ring α] [division_ring β] (f : α →+* β) {x y : α}

lemma map_ne_zero : f x ≠ 0 ↔ x ≠ 0 :=
⟨mt $ λ h, h.symm ▸ f.map_zero,
 λ x0 h, one_ne_zero $ by rw [← f.map_one, ← mul_inv_cancel x0, f.map_mul, h, zero_mul]⟩

lemma map_eq_zero : f x = 0 ↔ x = 0 :=
by haveI := classical.dec; exact not_iff_not.1 f.map_ne_zero

lemma map_inv : f x⁻¹ = (f x)⁻¹ :=
begin
  classical, by_cases h : x = 0, by simp [h],
  apply (domain.mul_left_inj (f.map_ne_zero.2 h)).1,
  rw [mul_inv_cancel (f.map_ne_zero.2 h), ← f.map_mul, mul_inv_cancel h, f.map_one]
end

lemma map_div : f (x / y) = f x / f y :=
(f.map_mul _ _).trans $ congr_arg _ $ f.map_inv

lemma injective : function.injective f :=
f.injective_iff.2
  (λ a ha, classical.by_contradiction $ λ ha0,
    by simpa [ha, f.map_mul, f.map_one, zero_ne_one]
        using congr_arg f (mul_inv_cancel ha0))

end

end ring_hom

namespace is_ring_hom
open ring_hom (of)

section
variables {β : Type*} [division_ring α] [division_ring β]
variables (f : α → β) [is_ring_hom f] {x y : α}

lemma map_ne_zero : f x ≠ 0 ↔ x ≠ 0 := (of f).map_ne_zero

lemma map_eq_zero : f x = 0 ↔ x = 0 := (of f).map_eq_zero

lemma map_inv : f x⁻¹ = (f x)⁻¹ := (of f).map_inv

lemma map_div : f (x / y) = f x / f y := (of f).map_div

lemma injective : function.injective f := (of f).injective

end

end is_ring_hom

section field_simp

mk_simp_attribute field_simps "The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free."

lemma mul_div_assoc' {α : Type*} [division_ring α] (a b c : α) : a * (b / c) = (a * b) / c :=
by simp [mul_div_assoc]

lemma neg_div' {α : Type*} [division_ring α] (a b : α) : - (b / a) = (-b) / a :=
by simp [neg_div]

attribute [field_simps] div_add_div_same inv_eq_one_div div_mul_eq_mul_div div_add' add_div'
div_div_eq_div_mul mul_div_assoc' div_eq_div_iff div_eq_iff eq_div_iff mul_ne_zero'
div_div_eq_mul_div neg_div' two_ne_zero div_sub_div div_sub' sub_div'

end field_simp
