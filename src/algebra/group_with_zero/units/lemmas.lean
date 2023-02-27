/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group_with_zero.commute
import algebra.hom.units
import group_theory.group_action.units

/-!
# Further lemmas about units in a `monoid_with_zero` or a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α M₀ G₀ M₀' G₀' F F' : Type*}

variables [monoid_with_zero M₀]

section group_with_zero
variables [group_with_zero G₀] {a b c : G₀}

@[simp] lemma div_self (h : a ≠ 0) : a / a = 1 := h.is_unit.div_self

lemma eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
hc.is_unit.eq_mul_inv_iff_mul_eq

lemma eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
hb.is_unit.eq_inv_mul_iff_mul_eq

lemma inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
ha.is_unit.inv_mul_eq_iff_eq_mul

lemma mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
hb.is_unit.mul_inv_eq_iff_eq_mul

lemma mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b := hb.is_unit.mul_inv_eq_one
lemma inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b := ha.is_unit.inv_mul_eq_one

lemma mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ := hb.is_unit.mul_eq_one_iff_eq_inv
lemma mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b := ha.is_unit.mul_eq_one_iff_inv_eq

@[simp] lemma div_mul_cancel (a : G₀) (h : b ≠ 0) : a / b * b = a := h.is_unit.div_mul_cancel _
@[simp] lemma mul_div_cancel (a : G₀) (h : b ≠ 0) : a * b / b = a := h.is_unit.mul_div_cancel _

lemma mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := h.is_unit.mul_one_div_cancel
lemma one_div_mul_cancel (h : a ≠ 0) : (1 / a) * a = 1 := h.is_unit.one_div_mul_cancel

lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b := hc.is_unit.div_left_inj

@[field_simps] lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b := hb.is_unit.div_eq_iff
@[field_simps] lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a := hb.is_unit.eq_div_iff

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a := hb.is_unit.div_eq_iff.trans eq_comm
lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b := hc.is_unit.eq_div_iff

lemma div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c := hb.is_unit.div_eq_of_eq_mul
lemma eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c := hc.is_unit.eq_div_of_mul_eq

lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b := hb.is_unit.div_eq_one_iff_eq

lemma div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a := hb.is_unit.div_mul_left

lemma mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : (a * c) / (b * c) = a / b :=
hc.is_unit.mul_div_mul_right _ _

lemma mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) := (hb.is_unit.mul_mul_div _).symm

lemma div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
by rw [div_div_eq_mul_div, div_mul_cancel _ hc]

lemma div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
by rw [← mul_div_assoc, div_mul_cancel _ hc]

lemma div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (div_mul_cancel a)

lemma mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (mul_div_cancel a)

@[simp] theorem divp_mk0 (a : G₀) {b : G₀} (hb : b ≠ 0) :
  a /ₚ units.mk0 b hb = a / b :=
divp_eq_div _ _

end group_with_zero

section comm_group_with_zero -- comm
variables [comm_group_with_zero G₀] {a b c d : G₀}

lemma div_mul_right (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b := ha.is_unit.div_mul_right _

lemma mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b :=
by rw [mul_comm, mul_div_cancel_of_imp h]

lemma mul_div_cancel_left (b : G₀) (ha : a ≠ 0) : a * b / a = b := ha.is_unit.mul_div_cancel_left _

lemma mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a :=
by rw [mul_comm, div_mul_cancel_of_imp h]

lemma mul_div_cancel' (a : G₀) (hb : b ≠ 0) : b * (a / b) = a := hb.is_unit.mul_div_cancel' _

lemma mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : (c * a) / (c * b) = a / b :=
hc.is_unit.mul_div_mul_left _ _

lemma mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0) (hd : d ≠ 0)
  (h : a / b = c / d) : a * d = c * b :=
by rw [←mul_one a, ←div_self hb, ←mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps] lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
hb.is_unit.div_eq_div_iff hd.is_unit

lemma div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b := ha.is_unit.div_div_cancel

lemma div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ := ha.is_unit.div_div_cancel_left

lemma div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b :=
by rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

end comm_group_with_zero


section monoid_with_zero
variables [group_with_zero G₀] [nontrivial M₀]
  [monoid_with_zero M₀'] [monoid_with_zero_hom_class F G₀ M₀]
  [monoid_with_zero_hom_class F' G₀ M₀'] (f : F) {a : G₀}
include M₀

lemma map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
⟨λ hfa ha, hfa $ ha.symm ▸ map_zero f, λ ha, ((is_unit.mk0 a ha).map f).ne_zero⟩

@[simp] lemma map_eq_zero : f a = 0 ↔ a = 0 := not_iff_not.1 (map_ne_zero f)

omit M₀
include M₀'

lemma eq_on_inv₀ (f g : F') (h : f a = g a) : f a⁻¹ = g a⁻¹ :=
begin
  rcases eq_or_ne a 0 with rfl|ha,
  { rw [inv_zero, map_zero, map_zero] },
  { exact (is_unit.mk0 a ha).eq_on_inv f g h }
end

end monoid_with_zero

section group_with_zero

variables [group_with_zero G₀] [group_with_zero G₀'] [monoid_with_zero_hom_class F G₀ G₀']
  (f : F) (a b : G₀)
include G₀'

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp] lemma map_inv₀ : f a⁻¹ = (f a)⁻¹ :=
begin
  by_cases h : a = 0, by simp [h],
  apply eq_inv_of_mul_eq_one_left,
  rw [← map_mul, inv_mul_cancel h, map_one]
end

@[simp] lemma map_div₀ : f (a / b) = f a / f b := map_div' f (map_inv₀ f) a b

end group_with_zero

/-- We define the inverse as a `monoid_with_zero_hom` by extending the inverse map by zero
on non-units. -/
noncomputable
def monoid_with_zero.inverse {M : Type*} [comm_monoid_with_zero M] :
  M →*₀ M :=
{ to_fun := ring.inverse,
  map_zero' := ring.inverse_zero _,
  map_one' := ring.inverse_one _,
  map_mul' := λ x y, (ring.mul_inverse_rev x y).trans (mul_comm _ _) }

@[simp]
lemma monoid_with_zero.coe_inverse {M : Type*} [comm_monoid_with_zero M] :
  (monoid_with_zero.inverse : M → M) = ring.inverse := rfl

@[simp]
lemma monoid_with_zero.inverse_apply {M : Type*} [comm_monoid_with_zero M] (a : M) :
  monoid_with_zero.inverse a = ring.inverse a := rfl

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
def inv_monoid_with_zero_hom {G₀ : Type*} [comm_group_with_zero G₀] : G₀ →*₀ G₀ :=
{ map_zero' := inv_zero,
  ..inv_monoid_hom }

namespace units
variables [group_with_zero G₀]
variables {a b : G₀}

@[simp] lemma smul_mk0 {α : Type*} [has_smul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) :
  (mk0 g hg) • a = g • a :=
rfl

end units
