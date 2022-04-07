/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/

import algebra.order.group
import tactic.abel

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

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
class linear_ordered_comm_group_with_zero (α : Type*)
  extends linear_ordered_comm_monoid_with_zero α, comm_group_with_zero α

variables {α : Type*}
variables {a b c d x y z : α}

instance [linear_ordered_add_comm_monoid_with_top α] :
  linear_ordered_comm_monoid_with_zero (multiplicative (order_dual α)) :=
{ zero := multiplicative.of_add (⊤ : α),
  zero_mul := top_add,
  mul_zero := add_top,
  zero_le_one := (le_top : (0 : α) ≤ ⊤),
  ..multiplicative.ordered_comm_monoid,
  ..multiplicative.linear_order }

instance [linear_ordered_add_comm_group_with_top α] :
  linear_ordered_comm_group_with_zero (multiplicative (order_dual α)) :=
{ inv_zero := linear_ordered_add_comm_group_with_top.neg_top,
  mul_inv_cancel := linear_ordered_add_comm_group_with_top.add_neg_cancel,
  ..multiplicative.div_inv_monoid,
  ..multiplicative.linear_ordered_comm_monoid_with_zero,
  ..multiplicative.nontrivial }

section monoid
variable [monoid α]

section preorder
variable [preorder α]

section left
variable [covariant_class α α (*) (≤)]

lemma left.one_le_pow_of_le : ∀ {n : ℕ} {x : α}, 1 ≤ x → 1 ≤ x^n
| 0       x _ := (pow_zero x).symm.le
| (n + 1) x H := calc 1 ≤ x          : H
                    ... = x * 1      : (mul_one x).symm
                    ... ≤ x * x ^ n  : mul_le_mul_left' (left.one_le_pow_of_le H) x
                    ... = x ^ n.succ : (pow_succ x n).symm

end left

section right
variable [covariant_class α α (function.swap (*)) (≤)]

lemma right.one_le_pow_of_le {x : α} (H : 1 ≤ x) :
  ∀ {n : ℕ}, 1 ≤ x^n
| 0       := (pow_zero _).symm.le
| (n + 1) := calc 1 ≤ x          : H
                ... = 1 * x      : (one_mul x).symm
                ... ≤ x ^ n * x  : mul_le_mul_right' right.one_le_pow_of_le x
                ... = x ^ n.succ : (pow_succ' x n).symm

lemma right.pow_le_one_of_le {x : α} (H : x ≤ 1) :
  ∀ {n : ℕ}, x^n ≤ 1
| 0       := (pow_zero _).le
| (n + 1) := calc x ^ n.succ = x ^ n * x : pow_succ' x n
                         ... ≤ 1 * x     : mul_le_mul_right' right.pow_le_one_of_le x
                         ... = x         : one_mul x
                         ... ≤ 1         : H

end right

lemma pow_le_pow_of_le [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]
  {x y : α} (H : x ≤ y) :
  ∀ {n : ℕ} , x^n ≤ y^n
| 0       := (pow_zero _).le.trans (pow_zero _).symm.le
| (n + 1) := calc  x ^ n.succ = x * x ^ n  : pow_succ x n
                          ... ≤ y * x ^ n  : mul_le_mul_right' H (x ^ n)
                          ... ≤ y * y ^ n  : mul_le_mul_left' pow_le_pow_of_le y
                          ... = y ^ n.succ : (pow_succ y n).symm

lemma left.pow_lt_one_of_lt [covariant_class α α (*) (<)] {n : ℕ} {x : α} (n0 : 0 < n) (H : x < 1) :
  x^n < 1 :=
begin
  refine nat.le_induction ((pow_one _).le.trans_lt H) (λ n n1 hn, _) _ (nat.succ_le_iff.mpr n0),
  calc x ^ (n + 1) = x * x ^ n : pow_succ x n
               ... < x * 1     : mul_lt_mul_left' hn x
               ... = x         : mul_one x
               ... < 1         : H
end

lemma left.pow_lt_one_iff {α: Type*} [monoid α] [linear_order α]
  [covariant_class α α (*) (<)] {n : ℕ} {x : α} (n0 : 0 < n) :
  x^n < 1 ↔ x < 1 :=
⟨λ H, not_le.mp (λ k, not_le.mpr H (by
  { haveI := has_mul.to_covariant_class_left α,
    exact left.one_le_pow_of_le k})), left.pow_lt_one_of_lt n0⟩

lemma right.pow_lt_one_of_lt [covariant_class α α (function.swap (*)) (<)] {n : ℕ} {x : α}
  (n0 : 0 < n) (H : x < 1) :
  x^n < 1 :=
begin
  refine nat.le_induction ((pow_one _).le.trans_lt H) (λ n n1 hn, _) _ (nat.succ_le_iff.mpr n0),
  calc x ^ (n + 1) = x ^ n * x : pow_succ' x n
               ... < 1 * x     : mul_lt_mul_right' hn x
               ... = x         : one_mul x
               ... < 1         : H
end

lemma right.pow_lt_one_iff {α: Type*} [monoid α] [linear_order α]
  [covariant_class α α (function.swap (*)) (<)] {n : ℕ} {x : α} (n0 : 0 < n) :
  x^n < 1 ↔ x < 1 :=
⟨λ H, not_le.mp (λ k, not_le.mpr H (by
  { haveI := has_mul.to_covariant_class_right α,
    exact right.one_le_pow_of_le k})), right.pow_lt_one_of_lt n0⟩

end preorder

section left_right
variables [linear_order α]
  [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]

end left_right

end monoid
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
  [has_zero β] [has_one β] [has_mul β] [has_pow β ℕ]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) :
  linear_ordered_comm_monoid_with_zero β :=
{ zero_le_one := show f 0 ≤ f 1, by simp only [zero, one,
    linear_ordered_comm_monoid_with_zero.zero_le_one],
  ..linear_order.lift f hf,
  ..hf.ordered_comm_monoid f one mul npow,
  ..hf.comm_monoid_with_zero f zero one mul npow }

lemma zero_le_one' : (0 : α) ≤ 1 :=
linear_ordered_comm_monoid_with_zero.zero_le_one

@[simp] lemma zero_le' : 0 ≤ a :=
by simpa only [mul_zero, mul_one] using mul_le_mul_left' (@zero_le_one' α _) a

@[simp] lemma not_lt_zero' : ¬a < 0 :=
not_lt_of_le zero_le'

@[simp] lemma le_zero_iff : a ≤ 0 ↔ a = 0 :=
⟨λ h, le_antisymm h zero_le', λ h, h ▸ le_rfl⟩

lemma zero_lt_iff : 0 < a ↔ a ≠ 0 :=
⟨ne_of_gt, λ h, lt_of_le_of_ne zero_le' h.symm⟩

lemma ne_zero_of_lt (h : b < a) : a ≠ 0 :=
λ h1, not_lt_zero' $ show b < 0, from h1 ▸ h

lemma pow_pos_iff [no_zero_divisors α] {n : ℕ} (hn : 0 < n) : 0 < a ^ n ↔ 0 < a :=
by simp_rw [zero_lt_iff, pow_ne_zero_iff hn]

instance : linear_ordered_add_comm_monoid_with_top (additive (order_dual α)) :=
{ top := (0 : α),
  top_add' := λ a, (zero_mul a : (0 : α) * a = 0),
  le_top := λ _, zero_le',
  ..additive.ordered_add_comm_monoid,
  ..additive.linear_order }

end linear_ordered_comm_monoid

variables [linear_ordered_comm_group_with_zero α]

lemma zero_lt_one₀ : (0 : α) < 1 :=
lt_of_le_of_ne zero_le_one' zero_ne_one

lemma le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b :=
by simpa only [mul_inv_cancel_right₀ h] using (mul_le_mul_right' hab c⁻¹)

lemma le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma mul_inv_le_of_le_mul (h : c ≠ 0) (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma le_mul_inv_iff₀ (hc : c ≠ 0) : a ≤ b * c⁻¹ ↔ a * c ≤ b :=
⟨λ h, inv_inv c ▸ mul_inv_le_of_le_mul (inv_ne_zero hc) h, le_mul_inv_of_mul_le hc⟩

lemma mul_inv_le_iff₀ (hc : c ≠ 0) : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
⟨λ h, inv_inv c ▸ le_mul_inv_of_mul_le (inv_ne_zero hc) h, mul_inv_le_of_le_mul hc⟩

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
have hz : z ≠ 0 := (mul_ne_zero_iff.1 $ ne_zero_of_lt h).2,
by { contrapose! h, simpa only [inv_inv] using mul_inv_le_of_le_mul (inv_ne_zero hz) h }

lemma inv_mul_lt_of_lt_mul₀ (h : x < y * z) : y⁻¹ * x < z :=
by { rw mul_comm at *, exact mul_inv_lt_of_lt_mul₀ h }

lemma mul_lt_right₀ (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c :=
by { contrapose! h, exact le_of_le_mul_right hc h }

lemma pow_lt_pow_succ {x : α} {n : ℕ} (hx : 1 < x) : x ^ n < x ^ n.succ :=
by { rw [← one_mul (x ^ n), pow_succ],
exact mul_lt_right₀ _ hx (pow_ne_zero _ $ ne_of_gt (lt_trans zero_lt_one₀ hx)) }

lemma pow_lt_pow₀ {x : α} {m n : ℕ} (hx : 1 < x) (hmn : m < n) : x ^ m < x ^ n :=
by { induction hmn with n hmn ih, exacts [pow_lt_pow_succ hx, lt_trans ih (pow_lt_pow_succ hx)] }

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

lemma div_le_div_right₀ (hc : c ≠ 0) : a/c ≤ b/c ↔ a ≤ b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_le_mul_right₀ (inv_ne_zero hc)]

lemma le_div_iff₀ (hc : c ≠ 0) : a ≤ b/c ↔ a*c ≤ b :=
by rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

lemma div_le_iff₀ (hc : c ≠ 0) : a/c ≤ b ↔ a ≤ b*c :=
by rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

instance : linear_ordered_add_comm_group_with_top (additive (order_dual α)) :=
{ neg_top := inv_zero,
  add_neg_cancel := λ a ha, mul_inv_cancel ha,
  ..additive.sub_neg_monoid,
  ..additive.linear_ordered_add_comm_monoid_with_top,
  ..additive.nontrivial }

namespace monoid_hom

variables {R : Type*} [ring R] (f : R →* α)

theorem map_neg_one : f (-1) = 1 :=
(pow_eq_one_iff (nat.succ_ne_zero 1)).1 $
  calc f (-1) ^ 2 = f (-1) * f(-1) : sq _
              ... = f ((-1) * - 1) : (f.map_mul _ _).symm
              ... = f ( - - 1)     : congr_arg _ (neg_one_mul _)
              ... = f 1            : congr_arg _ (neg_neg _)
              ... = 1              : map_one f

@[simp] lemma map_neg (x : R) : f (-x) = f x :=
calc f (-x) = f (-1 * x)   : congr_arg _ (neg_one_mul _).symm
        ... = f (-1) * f x : map_mul _ _ _
        ... = 1 * f x      : _root_.congr_arg (λ g, g * (f x)) (map_neg_one f)
        ... = f x          : one_mul _

lemma map_sub_swap (x y : R) : f (x - y) = f (y - x) :=
calc f (x - y) = f (-(y - x)) : congr_arg _ (neg_sub _ _).symm
           ... = _            : map_neg _ _

end monoid_hom
