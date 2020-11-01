/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.ring.basic
import algebra.group_with_zero
open set

set_option old_structure_cmd true

universe u
variables {α : Type u}

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor ring has_inv]
class division_ring (α : Type u) extends ring α, has_inv α, nontrivial α :=
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_mul_cancel : ∀ {a : α}, a ≠ 0 → a⁻¹ * a = 1)
(inv_zero : (0 : α)⁻¹ = 0)

section division_ring
variables [division_ring α] {a b : α}

@[priority 100] -- see Note [lower instance priority]
instance division_ring_has_div : has_div α :=
⟨λ a b, a * b⁻¹⟩

/-- Every division ring is a `group_with_zero`. -/
@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_group_with_zero :
  group_with_zero α :=
{ .. ‹division_ring α›,
  .. (infer_instance : semiring α) }

lemma inverse_eq_has_inv : (ring.inverse : α → α) = has_inv.inv :=
begin
  ext x,
  by_cases hx : x = 0,
  { simp [hx] },
  { exact ring.inverse_unit (units.mk0 x hx) }
end

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

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_domain : domain α :=
{ ..‹division_ring α›, ..(by apply_instance : semiring α),
  ..(by apply_instance : no_zero_divisors α) }

end division_ring

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor division_ring comm_ring]
class field (α : Type u) extends comm_ring α, has_inv α, nontrivial α :=
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : α)⁻¹ = 0)

section field

variable [field α]

@[priority 100] -- see Note [lower instance priority]
instance field.to_division_ring : division_ring α :=
{ inv_mul_cancel := λ _ h, by rw [mul_comm, field.mul_inv_cancel h]
  ..show field α, by apply_instance }

/-- Every field is a `comm_group_with_zero`. -/
@[priority 100] -- see Note [lower instance priority]
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

section is_field

/-- A predicate to express that a ring is a field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a field. -/
structure is_field (R : Type u) [ring R] : Prop :=
(exists_pair_ne : ∃ (x y : R), x ≠ y)
(mul_comm : ∀ (x y : R), x * y = y * x)
(mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1)

/-- Transferring from field to is_field -/
lemma field.to_is_field (R : Type u) [field R] : is_field R :=
{ mul_inv_cancel := λ a ha, ⟨a⁻¹, field.mul_inv_cancel ha⟩,
  ..‹field R› }

open_locale classical

/-- Transferring from is_field to field -/
noncomputable def is_field.to_field (R : Type u) [ring R] (h : is_field R) : field R :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (is_field.mul_inv_cancel h ha),
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ a ha,
    begin
      convert classical.some_spec (is_field.mul_inv_cancel h ha),
      exact dif_neg ha
    end,
  .. ‹ring R›, ..h }

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
lemma uniq_inv_of_is_field (R : Type u) [ring R] (hf : is_field R) :
  ∀ (x : R), x ≠ 0 → ∃! (y : R), x * y = 1 :=
begin
  intros x hx,
  apply exists_unique_of_exists_of_unique,
  { exact hf.mul_inv_cancel hx },
  { intros y z hxy hxz,
    calc y = y * (x * z) : by rw [hxz, mul_one]
       ... = (x * y) * z : by rw [← mul_assoc, hf.mul_comm y x]
       ... = z           : by rw [hxy, one_mul] }
end

end is_field

namespace ring_hom

section

variables {R K : Type*} [semiring R] [division_ring K] (f : R →+* K)

@[simp] lemma map_units_inv (u : units R) :
  f ↑u⁻¹ = (f ↑u)⁻¹ :=
(f : R →* K).map_units_inv u

end

section

variables {β γ : Type*} [division_ring α] [semiring β] [nontrivial β] [division_ring γ]
  (f : α →+* β) (g : α →+* γ) {x y : α}

lemma map_ne_zero : f x ≠ 0 ↔ x ≠ 0 := (f : α →* β).map_ne_zero f.map_zero

lemma map_eq_zero : f x = 0 ↔ x = 0 := (f : α →* β).map_eq_zero f.map_zero

variables (x y)

lemma map_inv : g x⁻¹ = (g x)⁻¹ := (g : α →* γ).map_inv' g.map_zero x

lemma map_div : g (x / y) = g x / g y := (g : α →* γ).map_div g.map_zero x y

protected lemma injective : function.injective f := f.injective_iff.2 $ λ x, f.map_eq_zero.1

end

end ring_hom
