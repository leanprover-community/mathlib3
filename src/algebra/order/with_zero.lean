/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
import algebra.hom.equiv.units.group_with_zero
import algebra.group_with_zero.inj_surj
import algebra.order.group.units
import algebra.order.monoid.basic
import algebra.order.monoid.with_zero.defs
import algebra.order.group.instances
import algebra.order.monoid.type_tags

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `nnreal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.

Note that to avoid issues with import cycles, `linear_ordered_comm_monoid_with_zero` is defined
in another file. However, the lemmas about it are stated here.
-/

set_option old_structure_cmd true

/-- A linearly ordered commutative group with a zero element. -/
@[protect_proj, ancestor linear_ordered_comm_monoid_with_zero comm_group_with_zero]
class linear_ordered_comm_group_with_zero (α : Type*)
  extends linear_ordered_comm_monoid_with_zero α, comm_group_with_zero α

variables {α : Type*}
variables {a b c d x y z : α}

instance [linear_ordered_add_comm_monoid_with_top α] :
  linear_ordered_comm_monoid_with_zero (multiplicative αᵒᵈ) :=
{ zero := multiplicative.of_add (⊤ : α),
  zero_mul := top_add,
  mul_zero := add_top,
  zero_le_one := (le_top : (0 : α) ≤ ⊤),
  ..multiplicative.ordered_comm_monoid,
  ..multiplicative.linear_order }

instance [linear_ordered_add_comm_group_with_top α] :
  linear_ordered_comm_group_with_zero (multiplicative αᵒᵈ) :=
{ inv_zero := linear_ordered_add_comm_group_with_top.neg_top,
  mul_inv_cancel := linear_ordered_add_comm_group_with_top.add_neg_cancel,
  ..multiplicative.div_inv_monoid,
  ..multiplicative.linear_ordered_comm_monoid_with_zero,
  ..multiplicative.nontrivial }

instance [linear_ordered_comm_monoid α] :
  linear_ordered_comm_monoid_with_zero (with_zero α) :=
{ mul_le_mul_left := λ x y, mul_le_mul_left',
  zero_le_one     := with_zero.zero_le _,
  ..with_zero.linear_order,
  ..with_zero.comm_monoid_with_zero }

instance [linear_ordered_comm_group α] :
  linear_ordered_comm_group_with_zero (with_zero α) :=
{ ..with_zero.linear_ordered_comm_monoid_with_zero,
  ..with_zero.comm_group_with_zero }

section linear_ordered_comm_monoid

variables [linear_ordered_comm_monoid_with_zero α]
/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/

/-- Pullback a `linear_ordered_comm_monoid_with_zero` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.linear_ordered_comm_monoid_with_zero {β : Type*}
  [has_zero β] [has_one β] [has_mul β] [has_pow β ℕ] [has_sup β] [has_inf β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_comm_monoid_with_zero β :=
{ zero_le_one := show f 0 ≤ f 1, by simp only [zero, one,
    linear_ordered_comm_monoid_with_zero.zero_le_one],
  ..linear_order.lift f hf hsup hinf,
  ..hf.ordered_comm_monoid f one mul npow,
  ..hf.comm_monoid_with_zero f zero one mul npow }

@[simp] lemma zero_le' : 0 ≤ a :=
by simpa only [mul_zero, mul_one] using mul_le_mul_left' zero_le_one a

@[simp] lemma not_lt_zero' : ¬a < 0 :=
not_lt_of_le zero_le'

@[simp] lemma le_zero_iff : a ≤ 0 ↔ a = 0 :=
⟨λ h, le_antisymm h zero_le', λ h, h ▸ le_rfl⟩

lemma zero_lt_iff : 0 < a ↔ a ≠ 0 :=
⟨ne_of_gt, λ h, lt_of_le_of_ne zero_le' h.symm⟩

lemma ne_zero_of_lt (h : b < a) : a ≠ 0 :=
λ h1, not_lt_zero' $ show b < 0, from h1 ▸ h

instance : linear_ordered_add_comm_monoid_with_top (additive αᵒᵈ) :=
{ top := (0 : α),
  top_add' := λ a, (zero_mul a : (0 : α) * a = 0),
  le_top := λ _, zero_le',
  ..additive.ordered_add_comm_monoid,
  ..additive.linear_order }

end linear_ordered_comm_monoid

variables [linear_ordered_comm_group_with_zero α]

-- TODO: Do we really need the following two?

/-- Alias of `mul_le_one'` for unification. -/
lemma mul_le_one₀ (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := mul_le_one' ha hb

/-- Alias of `one_le_mul'` for unification. -/
lemma one_le_mul₀ (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := one_le_mul ha hb

lemma le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b :=
by simpa only [mul_inv_cancel_right₀ h] using (mul_le_mul_right' hab c⁻¹)

lemma le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma mul_inv_le_of_le_mul (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
begin
  by_cases h : c = 0,
  { simp [h], },
  { exact le_of_le_mul_right h (by simpa [h] using hab), },
end

lemma inv_le_one₀ (ha : a ≠ 0) : a⁻¹ ≤ 1 ↔ 1 ≤ a := @inv_le_one' _ _ _ _ $ units.mk0 a ha

lemma one_le_inv₀ (ha : a ≠ 0) : 1 ≤ a⁻¹ ↔ a ≤ 1 := @one_le_inv' _ _ _ _ $ units.mk0 a ha

lemma le_mul_inv_iff₀ (hc : c ≠ 0) : a ≤ b * c⁻¹ ↔ a * c ≤ b :=
⟨λ h, inv_inv c ▸ mul_inv_le_of_le_mul h, le_mul_inv_of_mul_le hc⟩

lemma mul_inv_le_iff₀ (hc : c ≠ 0) : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
⟨λ h, inv_inv c ▸ le_mul_inv_of_mul_le (inv_ne_zero hc) h, mul_inv_le_of_le_mul⟩

lemma div_le_div₀ (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) :
  a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
if ha : a = 0 then by simp [ha] else
if hc : c = 0 then by simp [inv_ne_zero hb, hc, hd] else
show (units.mk0 a ha) * (units.mk0 b hb)⁻¹ ≤ (units.mk0 c hc) * (units.mk0 d hd)⁻¹ ↔
  (units.mk0 a ha) * (units.mk0 d hd) ≤ (units.mk0 c hc) * (units.mk0 b hb),
from mul_inv_le_mul_inv_iff'

@[simp] lemma units.zero_lt (u : αˣ) : (0 : α) < u :=
zero_lt_iff.2 $ u.ne_zero

lemma mul_lt_mul_of_lt_of_le₀ (hab : a ≤ b) (hb : b ≠ 0) (hcd : c < d) : a * c < b * d :=
have hd : d ≠ 0 := ne_zero_of_lt hcd,
if ha : a = 0 then by { rw [ha, zero_mul, zero_lt_iff], exact mul_ne_zero hb hd } else
if hc : c = 0 then by { rw [hc, mul_zero, zero_lt_iff], exact mul_ne_zero hb hd } else
show (units.mk0 a ha) * (units.mk0 c hc) < (units.mk0 b hb) * (units.mk0 d hd),
from mul_lt_mul_of_le_of_lt hab hcd

lemma mul_lt_mul₀ (hab : a < b) (hcd : c < d) : a * c < b * d :=
mul_lt_mul_of_lt_of_le₀ hab.le (ne_zero_of_lt hab) hcd

lemma mul_inv_lt_of_lt_mul₀ (h : x < y * z) : x * z⁻¹ < y :=
by { contrapose! h, simpa only [inv_inv] using mul_inv_le_of_le_mul h }

lemma inv_mul_lt_of_lt_mul₀ (h : x < y * z) : y⁻¹ * x < z :=
by { rw mul_comm at *, exact mul_inv_lt_of_lt_mul₀ h }

lemma mul_lt_right₀ (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c :=
by { contrapose! h, exact le_of_le_mul_right hc h }

lemma inv_lt_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
show (units.mk0 a ha)⁻¹ < (units.mk0 b hb)⁻¹ ↔ (units.mk0 b hb) < (units.mk0 a ha),
from inv_lt_inv_iff

lemma inv_le_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
show (units.mk0 a ha)⁻¹ ≤ (units.mk0 b hb)⁻¹ ↔ (units.mk0 b hb) ≤ (units.mk0 a ha),
from inv_le_inv_iff

lemma lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d :=
begin
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh),
  simp_rw ← inv_le_inv₀ ha (ne_of_gt hc) at hh,
  have := mul_lt_mul_of_lt_of_le₀ hh (inv_ne_zero (ne_of_gt hc)) h,
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ (ne_of_gt hc)] using this,
end

lemma mul_le_mul_right₀ (hc : c ≠ 0) : a * c ≤ b * c ↔ a ≤ b :=
⟨le_of_le_mul_right hc, λ hab, mul_le_mul_right' hab _⟩

lemma mul_le_mul_left₀ (ha : a ≠ 0) : a * b ≤ a * c ↔ b ≤ c :=
by {simp only [mul_comm a], exact mul_le_mul_right₀ ha }

lemma div_le_div_right₀ (hc : c ≠ 0) : a / c ≤ b / c ↔ a ≤ b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_le_mul_right₀ (inv_ne_zero hc)]

lemma div_le_div_left₀ (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / b ≤ a / c ↔ c ≤ b :=
by simp only [div_eq_mul_inv, mul_le_mul_left₀ ha, inv_le_inv₀ hb hc]

lemma le_div_iff₀ (hc : c ≠ 0) : a ≤ b / c ↔ a*c ≤ b :=
by rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

lemma div_le_iff₀ (hc : c ≠ 0) : a / c ≤ b ↔ a ≤ b*c :=
by rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- `equiv.mul_left₀` as an order_iso on a `linear_ordered_comm_group_with_zero.`.

Note that `order_iso.mul_left₀` refers to the `linear_ordered_field` version. -/
@[simps apply to_equiv {simp_rhs := tt}]
def order_iso.mul_left₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
{ map_rel_iff' := λ x y,  mul_le_mul_left₀ ha, ..equiv.mul_left₀ a ha }

lemma order_iso.mul_left₀'_symm {a : α} (ha : a ≠ 0) :
  (order_iso.mul_left₀' ha).symm = order_iso.mul_left₀' (inv_ne_zero ha) :=
by { ext, refl }

/-- `equiv.mul_right₀` as an order_iso on a `linear_ordered_comm_group_with_zero.`.

Note that `order_iso.mul_right₀` refers to the `linear_ordered_field` version. -/
@[simps apply to_equiv {simp_rhs := tt}]
def order_iso.mul_right₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
{ map_rel_iff' := λ _ _, mul_le_mul_right₀ ha, ..equiv.mul_right₀ a ha }

lemma order_iso.mul_right₀'_symm {a : α} (ha : a ≠ 0) :
  (order_iso.mul_right₀' ha).symm = order_iso.mul_right₀' (inv_ne_zero ha) :=
by { ext, refl }

instance : linear_ordered_add_comm_group_with_top (additive αᵒᵈ) :=
{ neg_top := inv_zero,
  add_neg_cancel := λ a ha, mul_inv_cancel ha,
  ..additive.sub_neg_monoid,
  ..additive.linear_ordered_add_comm_monoid_with_top,
  ..additive.nontrivial }
