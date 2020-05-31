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

protected definition algebra.div (a b : α) : α :=
a * b⁻¹

instance division_ring_has_div : has_div α :=
⟨algebra.div⟩

lemma division_def (a b : α) : a / b = a * b⁻¹ :=
rfl

@[simp] lemma mul_inv_cancel (h : a ≠ 0) : a * a⁻¹ = 1 :=
division_ring.mul_inv_cancel h

@[simp] lemma inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
division_ring.inv_mul_cancel h

@[simp] lemma one_div_eq_inv (a : α) : 1 / a = a⁻¹ := one_mul a⁻¹

@[field_simps] lemma inv_eq_one_div (a : α) : a⁻¹ = 1 / a := by simp

/-- Every division ring is a `group_with_zero`. -/
@[priority 10] -- see Note [lower instance priority]
instance division_ring.to_group_with_zero :
  group_with_zero α :=
{ mul_inv_cancel := λ _, mul_inv_cancel,
  .. ‹division_ring α›,
  .. (by apply_instance : semiring α) }

local attribute [simp]
  division_def mul_comm mul_assoc
  mul_left_comm mul_inv_cancel inv_mul_cancel

lemma div_eq_mul_one_div (a b : α) : a / b = a * (1 / b) := by simp

lemma mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := by simp [h]

lemma one_div_mul_cancel (h : a ≠ 0) : (1 / a) * a = 1 := by simp [h]

@[simp] lemma div_self (h : a ≠ 0) : a / a = 1 := by simp [h]

lemma one_div_one : 1 / 1 = (1:α) :=
div_self (ne.symm zero_ne_one)

theorem inv_one : (1⁻¹ : α) = 1 := by rw [inv_eq_one_div, one_div_one]

lemma mul_div_assoc (a b c : α) : (a * b) / c = a * (b / c) := by simp

@[field_simps] lemma mul_div_assoc' (a b c : α) : a * (b / c) = (a * b) / c :=
by simp [mul_div_assoc]

lemma one_div_ne_zero (h : a ≠ 0) : 1 / a ≠ 0 :=
assume : 1 / a = 0,
have 0 = (1:α), from eq.symm (by rw [← mul_one_div_cancel h, this, mul_zero]),
absurd this zero_ne_one

lemma ne_zero_of_one_div_ne_zero (h : 1 / a ≠ 0) : a ≠ 0 :=
assume ha : a = 0, begin rw [ha, div_zero] at h, contradiction end

lemma inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 :=
by rw inv_eq_one_div; exact one_div_ne_zero h

lemma eq_zero_of_one_div_eq_zero (h : 1 / a = 0) : a = 0 :=
classical.by_cases
  (assume ha, ha)
  (assume ha, false.elim ((one_div_ne_zero ha) h))

lemma one_inv_eq : 1⁻¹ = (1:α) :=
calc 1⁻¹ = 1 * 1⁻¹ : by rw [one_mul]
     ... = (1:α)   : by simp

local attribute [simp] one_inv_eq

lemma div_one (a : α) : a / 1 = a := by simp

lemma zero_div (a : α) : 0 / a = 0 := by simp

-- note: integral domain has a "mul_ne_zero". a commutative division ring is an integral
-- domain, but let's not define that class for now.
lemma division_ring.mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
assume : a * b = 0,
have   a * 1 = 0, by rw [← mul_one_div_cancel hb, ← mul_assoc, this, zero_mul],
have   a = 0, by rwa mul_one at this,
absurd this ha

lemma mul_ne_zero_comm (h : a * b ≠ 0) : b * a ≠ 0 :=
have h₁ : a ≠ 0, from ne_zero_of_mul_ne_zero_right h,
have h₂ : b ≠ 0, from ne_zero_of_mul_ne_zero_left h,
division_ring.mul_ne_zero h₂ h₁

lemma eq_one_div_of_mul_eq_one (h : a * b = 1) : b = 1 / a :=
have a ≠ 0, from
   assume : a = 0,
   have 0 = (1:α), by rwa [this, zero_mul] at h,
      absurd this zero_ne_one,
have b = (1 / a) * a * b, by rw [one_div_mul_cancel this, one_mul],
show b = 1 / a, by rwa [mul_assoc, h, mul_one] at this

lemma eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a :=
have a ≠ 0, from
  assume : a = 0,
  have 0 = (1:α), by rwa [this, mul_zero] at h,
    absurd this zero_ne_one,
by rw [← h, mul_div_assoc, div_self this, mul_one]

lemma division_ring.one_div_mul_one_div : (1 / a) * (1 / b) = 1 / (b * a) :=
match classical.em (a = 0), classical.em (b = 0) with
| or.inr ha, or.inr hb :=
  have (b * a) * ((1 / a) * (1 / b)) = 1,
    by rw [mul_assoc, ← mul_assoc a, mul_one_div_cancel ha, one_mul, mul_one_div_cancel hb],
  eq_one_div_of_mul_eq_one this
| or.inl ha, _         := by simp [ha]
| _        , or.inl hb := by simp [hb]
end

lemma one_div_neg_one_eq_neg_one : (1:α) / (-1) = -1 :=
have (-1) * (-1) = (1:α), by rw [neg_mul_neg, one_mul],
eq.symm (eq_one_div_of_mul_eq_one this)

lemma one_div_neg_eq_neg_one_div (a : α) : 1 / (- a) = - (1 / a) :=
calc
  1 / (- a) = 1 / ((-1) * a)        : by rw neg_eq_neg_one_mul
        ... = (1 / a) * (1 / (- 1)) : by rw division_ring.one_div_mul_one_div
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

lemma one_div_one_div (a : α) : 1 / (1 / a) = a :=
match classical.em (a = 0) with
| or.inl h := by simp [h]
| or.inr h := eq.symm (eq_one_div_of_mul_eq_one_left (mul_one_div_cancel h))
end

lemma inv_inv' (a : α) : a⁻¹⁻¹ = a :=
by rw [inv_eq_one_div, inv_eq_one_div, one_div_one_div]

lemma eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b :=
by rw [← one_div_one_div a, h,one_div_one_div]

lemma mul_inv' (a b : α) : (b * a)⁻¹ = a⁻¹ * b⁻¹ :=
eq.symm $ calc
  a⁻¹ * b⁻¹ = (1 / a) * (1 / b) : by simp
        ... = (1 / (b * a))     : division_ring.one_div_mul_one_div
        ... = (b * a)⁻¹         : by simp

lemma one_div_div (a b : α) : 1 / (a / b) = b / a :=
by rw [one_div_eq_inv, division_def, mul_inv',
       inv_inv', division_def]

lemma div_helper (b : α) (h : a ≠ 0) : (1 / (a * b)) * a = 1 / b :=
by simp only [division_def, mul_inv', one_mul, mul_assoc, inv_mul_cancel h, mul_one]

lemma mul_div_cancel (a : α) {b : α} (hb : b ≠ 0) : a * b / b = a :=
by simp [hb]

lemma div_mul_cancel (a : α) {b : α} (hb : b ≠ 0) : a / b * b = a :=
by simp [hb]

@[field_simps] lemma div_div_eq_mul_div (a b c : α) : a / (b / c) = (a * c) / b :=
by rw [div_eq_mul_one_div, one_div_div, ← mul_div_assoc]

lemma div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a :=
by simp only [division_def, mul_inv', ← mul_assoc, mul_inv_cancel hb]

lemma mul_div_mul_right (a : α) (b : α) {c : α} (hc : c ≠ 0) :
      (a * c) / (b * c) = a / b :=
by rw [mul_div_assoc, div_mul_left hc, ← mul_div_assoc, mul_one]

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

lemma division_ring.inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
inv_inj'' _ _

lemma division_ring.inv_eq_iff  : a⁻¹ = b ↔ b⁻¹ = a :=
inv_eq_iff

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

lemma div_eq_one_iff_eq (a : α) {b : α} (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
iff.intro
 (assume : a / b = 1, calc
      a   = a / b * b : by simp [hb]
      ... = 1 * b     : by rw this
      ... = b         : by simp)
 (assume : a = b, by simp [this, hb])

lemma eq_of_div_eq_one (a : α) {b : α} (Hb : b ≠ 0) : a / b = 1 → a = b :=
iff.mp $ div_eq_one_iff_eq a Hb

lemma eq_div_iff_mul_eq (a b : α) {c : α} (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
iff.intro
  (assume : a = b / c, by rw [this, (div_mul_cancel _ hc)])
  (assume : a * c = b, by rw [← this, mul_div_cancel _ hc])

lemma eq_div_of_mul_eq (a b : α) {c : α} (hc : c ≠ 0) : a * c = b → a = b / c :=
iff.mpr $ eq_div_iff_mul_eq a b hc

lemma mul_eq_of_eq_div (a b: α) {c : α} (hc : c ≠ 0) : a = b / c → a * c = b :=
iff.mp $ eq_div_iff_mul_eq a b hc

lemma add_div_eq_mul_add_div (a b : α) {c : α} (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
have (a + b / c) * c = a * c + b, by rw [right_distrib, (div_mul_cancel _ hc)],
  (iff.mpr (eq_div_iff_mul_eq _ _ hc)) this

lemma mul_mul_div (a : α) {c : α} (hc : c ≠ 0) : a = a * c * (1 / c) :=
by simp [hc]

lemma eq_of_mul_eq_mul_of_nonzero_left {a b c : α} (h : a ≠ 0) (h₂ : a * b = a * c) : b = c :=
by rw [← one_mul b, ← inv_mul_cancel h, mul_assoc, h₂, ← mul_assoc, inv_mul_cancel h, one_mul]

lemma eq_of_mul_eq_mul_of_nonzero_right {a b c : α} (h : c ≠ 0) (h2 : a * c = b * c) : a = b :=
by rw [← mul_one a, ← mul_inv_cancel h, ← mul_assoc, h2, mul_assoc, mul_inv_cancel h, mul_one]

instance division_ring.to_domain : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h,
    classical.by_contradiction $ λ hn,
      division_ring.mul_ne_zero (mt or.inl hn) (mt or.inr hn) h
  ..‹division_ring α›, ..(by apply_instance : semiring α) }

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

lemma one_div_mul_one_div (a b : α) : (1 / a) * (1 / b) =  1 / (a * b) :=
by rw [division_ring.one_div_mul_one_div, mul_comm b]

lemma div_mul_right {a : α} (b : α) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
by rw [mul_comm, div_mul_left ha]

lemma mul_div_cancel_left {a : α} (b : α) (ha : a ≠ 0) : a * b / a = b :=
by rw [mul_comm a, (mul_div_cancel _ ha)]

lemma mul_div_cancel' (a : α) {b : α} (hb : b ≠ 0) : b * (a / b) = a :=
by rw [mul_comm, (div_mul_cancel _ hb)]

lemma one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
by rw [add_comm, ← div_mul_left ha, ← div_mul_right _ hb,
       division_def, division_def, division_def, ← right_distrib, mul_comm a]

local attribute [simp] mul_assoc mul_comm mul_left_comm

lemma div_mul_div (a b c d : α) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
begin simp [division_def], rw [mul_inv', mul_comm d⁻¹] end

lemma mul_div_mul_left (a b : α) {c : α} (hc : c ≠ 0) :
      (c * a) / (c * b) = a / b :=
by rw [← div_mul_div, div_self hc, one_mul]

@[field_simps] lemma div_mul_eq_mul_div (a b c : α) : (b / c) * a = (b * a) / c :=
by simp [division_def]

lemma div_mul_eq_mul_div_comm (a b c : α) :
      (b / c) * a = b * (a / c) :=
by rw [div_mul_eq_mul_div, ← one_mul c, ← div_mul_div,
       div_one, one_mul]

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

lemma mul_eq_mul_of_div_eq_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0)
  (hd : d ≠ 0) (h : a / b = c / d) : a * d = c * b :=
by rw [← mul_one (a*d), mul_assoc, mul_comm d, ← mul_assoc, ← div_self hb,
       ← div_mul_eq_mul_div_comm, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps] lemma div_div_eq_div_mul (a b c : α) : (a / b) / c = a / (b * c) :=
by rw [div_eq_mul_one_div, div_mul_div, mul_one]

lemma div_div_div_div_eq (a : α) {b c d : α} :
      (a / b) / (c / d) = (a * d) / (b * c) :=
by rw [div_div_eq_mul_div, div_mul_eq_mul_div,
       div_div_eq_div_mul]

lemma div_mul_eq_div_mul_one_div (a b c : α) :
      a / (b * c) = (a / b) * (1 / c) :=
by rw [← div_div_eq_div_mul, ← div_eq_mul_one_div]

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

/-- Every field is a `comm_group_with_zero`. -/
instance field.to_comm_group_with_zero :
  comm_group_with_zero α :=
{ .. (_ : group_with_zero α), .. ‹field α› }

@[priority 100] -- see Note [lower instance priority]
instance field.to_integral_domain : integral_domain α :=
{ ..‹field α›, ..division_ring.to_domain }

end field

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
  apply (domain.mul_right_inj (f.map_ne_zero.2 h)).1,
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
