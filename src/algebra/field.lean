/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import logic.basic algebra.ring algebra.group_with_zero
open set

universe u
variables {α : Type u}

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_domain [s : division_ring α] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h,
    classical.by_contradiction $ λ hn,
      division_ring.mul_ne_zero (mt or.inl hn) (mt or.inr hn) h
  ..s, ..(by apply_instance : semiring α) }

/-- Every division ring is a `group_with_zero`. -/
@[priority 10] -- see Note [lower instance priority]
instance division_ring.to_group_with_zero {K : Type*} [division_ring K] :
  group_with_zero K :=
{ mul_inv_cancel := λ _, mul_inv_cancel,
  .. ‹division_ring K›,
  .. (by apply_instance : semiring K) }

/-- Every field is a `comm_group_with_zero`. -/
@[priority 100] -- see Note [lower instance priority]
instance field.to_comm_group_with_zero {K : Type*} [field K] :
  comm_group_with_zero K :=
{ .. (_ : group_with_zero K), .. ‹field K› }

@[simp] theorem inv_one [division_ring α] : (1⁻¹ : α) = 1 := by rw [inv_eq_one_div, one_div_one]

attribute [simp] inv_inv'

section division_ring
variables [s : division_ring α] {a b c : α}
include s

attribute [simp] div_one zero_div div_self

lemma neg_inv : - a⁻¹ = (- a)⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma add_div (a b c : α) : (a + b) / c = a / c + b / c :=
(div_add_div_same _ _ _).symm

lemma sub_div (a b c : α) : (a - b) / c = a / c - b / c :=
(div_sub_div_same _ _ _).symm

lemma division_ring.inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
inv_inj'' _ _

lemma division_ring.inv_eq_iff  : a⁻¹ = b ↔ b⁻¹ = a :=
inv_eq_iff

lemma div_neg (a : α) : a / -b = -(a / b) :=
by rw [← div_neg_eq_neg_div]

end division_ring

@[priority 100] -- see Note [lower instance priority]
instance field.to_integral_domain [F : field α] : integral_domain α :=
{ ..F, ..division_ring.to_domain }

section
variables [field α] {a b c d : α}

lemma inv_add_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

lemma inv_sub_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]

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
