/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.ring
import algebra.group_with_zero
open set

set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true

universe u
variables {α : Type u}

@[protect_proj, ancestor ring has_inv]
class division_ring (α : Type u) extends ring α, has_inv α :=
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_mul_cancel : ∀ {a : α}, a ≠ 0 → a⁻¹ * a = 1)
(inv_zero : (0 : α)⁻¹ = 0)
(zero_ne_one : (0 : α) ≠ 1)

section division_ring
variables [division_ring α] {a b : α}

instance division_ring.to_nonzero : nonzero α :=
⟨division_ring.zero_ne_one⟩

instance division_ring_has_div : has_div α :=
⟨λ a b, a * b⁻¹⟩

/-- Every division ring is a `group_with_zero`. -/
@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_group_with_zero :
  group_with_zero α :=
{ .. ‹division_ring α›,
  .. (infer_instance : semiring α) }

@[simp] lemma one_div_eq_inv (a : α) : 1 / a = a⁻¹ := one_mul a⁻¹

@[field_simps] lemma inv_eq_one_div (a : α) : a⁻¹ = 1 / a := by simp

local attribute [simp]
  division_def mul_comm mul_assoc
  mul_left_comm mul_inv_cancel inv_mul_cancel

@[field_simps] lemma mul_div_assoc' (a b c : α) : a * (b / c) = (a * b) / c :=
by simp [mul_div_assoc]

lemma one_div_neg_one_eq_neg_one : (1:α) / (-1) = -1 :=
have (-1) * (-1) = (1:α), by rw [neg_mul_neg, one_mul],
eq.symm (eq_one_div_of_mul_eq_one this)

lemma one_div_neg_eq_neg_one_div (a : α) : 1 / (- a) = - (1 / a) :=
calc
  1 / (- a) = 1 / ((-1) * a)        : by rw neg_eq_neg_one_mul
        ... = (1 / a) * (1 / (- 1)) : by rw one_div_mul_one_div_rev
        ... = (1 / a) * (-1)        : by rw one_div_neg_one_eq_neg_one
        ... = - (1 / a)             : by rw [mul_neg_eq_neg_mul_symm, mul_one]

lemma div_neg_eq_neg_div (a b : α) : b / (- a) = - (b / a) :=
calc
  b / (- a) = b * (1 / (- a)) : by rw [← inv_eq_one_div, division_def]
        ... = b * -(1 / a)    : by rw one_div_neg_eq_neg_one_div
        ... = -(b * (1 / a))  : by rw neg_mul_eq_mul_neg
        ... = - (b * a⁻¹)     : by rw inv_eq_one_div

lemma neg_div (a b : α) : (-b) / a = - (b / a) :=
by rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps] lemma neg_div' {α : Type*} [division_ring α] (a b : α) : - (b / a) = (-b) / a :=
by simp [neg_div]

lemma neg_div_neg_eq (a b : α) : (-a) / (-b) = a / b :=
by rw [div_neg_eq_neg_div, neg_div, neg_neg]

@[field_simps] lemma div_add_div_same (a b c : α) : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma div_sub_div_same (a b c : α) : (a / c) - (b / c) = (a - b) / c :=
by rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

lemma neg_inv : - a⁻¹ = (- a)⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma add_div (a b c : α) : (a + b) / c = a / c + b / c :=
(div_add_div_same _ _ _).symm

lemma sub_div (a b c : α) : (a - b) / c = a / c - b / c :=
(div_sub_div_same _ _ _).symm

lemma div_neg (a : α) : a / -b = -(a / b) :=
by rw [← div_neg_eq_neg_div]

lemma inv_neg : (-a)⁻¹ = -(a⁻¹) :=
by rw neg_inv

lemma one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (a + b) * (1 / b) = 1 / a + 1 / b :=
by rw [(left_distrib (1 / a)), (one_div_mul_cancel ha), right_distrib, one_mul,
       mul_assoc, (mul_one_div_cancel hb), mul_one, add_comm]

lemma one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (b - a) * (1 / b) = 1 / a - 1 / b :=
by rw [(mul_sub_left_distrib (1 / a)), (one_div_mul_cancel ha), mul_sub_right_distrib,
       one_mul, mul_assoc, (mul_one_div_cancel hb), mul_one]

lemma add_div_eq_mul_add_div (a b : α) {c : α} (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
(eq_div_iff_mul_eq hc).2 $ by rw [right_distrib, (div_mul_cancel _ hc)]

instance division_ring.to_domain : domain α :=
{ ..‹division_ring α›, ..(by apply_instance : semiring α),
  ..(by apply_instance : no_zero_divisors α) }

end division_ring

@[protect_proj, ancestor division_ring comm_ring]
class field (α : Type u) extends comm_ring α, has_inv α :=
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : α)⁻¹ = 0)
(zero_ne_one : (0 : α) ≠ 1)

section field

variable [field α]

instance field.to_division_ring : division_ring α :=
{ inv_mul_cancel := λ _ h, by rw [mul_comm, field.mul_inv_cancel h]
  ..show field α, by apply_instance }

/-- Every field is a `comm_group_with_zero`. -/
instance field.to_comm_group_with_zero :
  comm_group_with_zero α :=
{ .. (_ : group_with_zero α), .. ‹field α› }

lemma one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
by rw [add_comm, ← div_mul_left ha, ← div_mul_right _ hb,
       division_def, division_def, division_def, ← right_distrib, mul_comm a]

local attribute [simp] mul_assoc mul_comm mul_left_comm

lemma div_add_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
      (a / b) + (c / d) = ((a * d) + (b * c)) / (b * d) :=
by rw [← mul_div_mul_right _ b hd, ← mul_div_mul_left c d hb, div_add_div_same]

@[field_simps] lemma div_sub_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
  (a / b) - (c / d) = ((a * d) - (b * c)) / (b * d) :=
begin
  simp [sub_eq_add_neg],
  rw [neg_eq_neg_one_mul, ← mul_div_assoc, div_add_div _ _ hb hd,
      ← mul_assoc, mul_comm b, mul_assoc, ← neg_eq_neg_one_mul]
end

lemma inv_add_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

lemma inv_sub_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]

@[field_simps] lemma add_div' (a b c : α) (hc : c ≠ 0) : b + a / c = (b * c + a) / c :=
by simpa using div_add_div b a one_ne_zero hc

@[field_simps] lemma sub_div' (a b c : α) (hc : c ≠ 0) : b - a / c = (b * c - a) / c :=
by simpa using div_sub_div b a one_ne_zero hc

@[field_simps] lemma div_add' (a b c : α) (hc : c ≠ 0) : a / c + b = (a + b * c) / c :=
by rwa [add_comm, add_div', add_comm]

@[field_simps] lemma div_sub' (a b c : α) (hc : c ≠ 0) : a / c - b = (a - c * b) / c :=
by simpa using div_sub_div a b hc one_ne_zero

@[priority 100] -- see Note [lower instance priority]
instance field.to_integral_domain : integral_domain α :=
{ ..‹field α›, ..division_ring.to_domain }

end field

namespace ring_hom

section

variables {β : Type*} [division_ring α] [division_ring β] (f : α →+* β) {x y : α}

lemma map_ne_zero : f x ≠ 0 ↔ x ≠ 0 := (f : α →* β).map_ne_zero f.map_zero

lemma map_eq_zero : f x = 0 ↔ x = 0 := (f : α →* β).map_eq_zero f.map_zero

variables (x y)

lemma map_inv : f x⁻¹ = (f x)⁻¹ := (f : α →* β).map_inv' f.map_zero x

lemma map_div : f (x / y) = f x / f y := (f : α →* β).map_div f.map_zero x y

protected lemma injective : function.injective f := f.injective_iff.2 $ λ x, f.map_eq_zero.1

end

end ring_hom
