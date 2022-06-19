/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, other
-/
import algebra.field_power

/-!
# Algebraic structures on the set of positive numbers

In this file we define various instances (`add_semigroup`, `ordered_comm_monoid` etc) on the
type `{x : R // 0 < x}`. In each case we try to require the weakest possible typeclass
assumptions on `R` but possibly, there is a room for improvements.
-/
open function

namespace positive

variables {M R K : Type*}

section add_basic

variables [add_monoid M] [preorder M] [covariant_class M M (+) (<)]

instance : has_add {x : M // 0 < x} := ⟨λ x y, ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast] lemma coe_add (x y : {x : M // 0 < x}) : ↑(x + y) = (x + y : M) := rfl

instance : add_semigroup {x : M // 0 < x} := subtype.coe_injective.add_semigroup _ coe_add

instance {M : Type*} [add_comm_monoid M] [preorder M] [covariant_class M M (+) (<)] :
  add_comm_semigroup {x : M // 0 < x} :=
subtype.coe_injective.add_comm_semigroup _ coe_add

instance {M : Type*} [add_left_cancel_monoid M] [preorder M] [covariant_class M M (+) (<)] :
  add_left_cancel_semigroup {x : M // 0 < x} :=
subtype.coe_injective.add_left_cancel_semigroup _ coe_add

instance {M : Type*} [add_right_cancel_monoid M] [preorder M] [covariant_class M M (+) (<)] :
  add_right_cancel_semigroup {x : M // 0 < x} :=
subtype.coe_injective.add_right_cancel_semigroup _ coe_add

instance covariant_class_add_lt : covariant_class {x : M // 0 < x} {x : M // 0 < x} (+) (<) :=
⟨λ x y z hyz, subtype.coe_lt_coe.1 $ add_lt_add_left hyz _⟩

instance covariant_class_swap_add_lt [covariant_class M M (swap (+)) (<)] :
  covariant_class {x : M // 0 < x} {x : M // 0 < x} (swap (+)) (<) :=
⟨λ x y z hyz, subtype.coe_lt_coe.1 $ add_lt_add_right hyz _⟩

instance contravariant_class_add_lt [contravariant_class M M (+) (<)] :
  contravariant_class {x : M // 0 < x} {x : M // 0 < x} (+) (<) :=
⟨λ x y z h, subtype.coe_lt_coe.1 $ lt_of_add_lt_add_left h⟩

instance contravariant_class_swap_add_lt [contravariant_class M M (swap (+)) (<)] :
  contravariant_class {x : M // 0 < x} {x : M // 0 < x} (swap (+)) (<) :=
⟨λ x y z h, subtype.coe_lt_coe.1 $ lt_of_add_lt_add_right h⟩

instance contravariant_class_add_le [contravariant_class M M (+) (≤)] :
  contravariant_class {x : M // 0 < x} {x : M // 0 < x} (+) (≤) :=
⟨λ x y z h, subtype.coe_le_coe.1 $ le_of_add_le_add_left h⟩

instance contravariant_class_swap_add_le [contravariant_class M M (swap (+)) (≤)] :
  contravariant_class {x : M // 0 < x} {x : M // 0 < x} (swap (+)) (≤) :=
⟨λ x y z h, subtype.coe_le_coe.1 $ le_of_add_le_add_right h⟩

end add_basic

instance covariant_class_add_le [add_monoid M] [partial_order M] [covariant_class M M (+) (<)] :
  covariant_class {x : M // 0 < x} {x : M // 0 < x} (+) (≤) :=
⟨λ x, strict_mono.monotone $ λ _ _ h, add_lt_add_left h _⟩

section mul

variables [ordered_semiring R] [linear_ordered_field K]

instance : has_mul {x : R // 0 < x} := ⟨λ x y, ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp] lemma coe_mul (x y : {x : R // 0 < x}) : ↑(x * y) = (x * y : R) := rfl

instance : has_pow {x : R // 0 < x} ℕ := ⟨λ x n, ⟨x ^ n, pow_pos x.2 n⟩⟩

@[simp] lemma coe_pow (x : {x : R // 0 < x}) (n : ℕ) : ↑(x ^ n) = (x ^ n : R) := rfl

instance : semigroup {x : R // 0 < x} := subtype.coe_injective.semigroup coe coe_mul

instance : distrib {x : R // 0 < x} := subtype.coe_injective.distrib _ coe_add coe_mul

instance [nontrivial R] : has_one {x : R // 0 < x} := ⟨⟨1, one_pos⟩⟩

@[simp] lemma coe_one [nontrivial R] : ((1 : {x : R // 0 < x}) : R) = 1 := rfl

instance [nontrivial R] : monoid {x : R // 0 < x} :=
subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

instance : has_inv {x : K // 0 < x} := ⟨λ x, ⟨x⁻¹, inv_pos.2 x.2⟩⟩

@[simp] lemma coe_inv (x : {x : K // 0 < x}) : ↑x⁻¹ = (x⁻¹ : K) := rfl

end mul

section mul_comm

instance [ordered_comm_semiring R] [nontrivial R] : ordered_comm_monoid {x : R // 0 < x} :=
{ mul_le_mul_left := λ x y hxy c, subtype.coe_le_coe.1 $ mul_le_mul_of_nonneg_left hxy c.2.le,
  .. subtype.partial_order _,
  .. subtype.coe_injective.comm_monoid (coe : {x : R // 0 < x} → R) coe_one coe_mul coe_pow }

instance [linear_ordered_comm_ring R] [nontrivial R] :
  linear_ordered_comm_monoid {x : R // 0 < x} :=
{ .. subtype.linear_order _, .. positive.subtype.ordered_comm_monoid }

variables [linear_ordered_field K]

instance : has_pow {x : K // 0 < x} ℤ :=
⟨λ x n, ⟨x ^ n, zpow_pos_of_pos x.2 _⟩⟩

@[simp] lemma coe_zpow (x : {x : K // 0 < x}) (n : ℤ) : ↑(x ^ n) = (x ^ n : K) := rfl

instance : linear_ordered_comm_group {x : K // 0 < x} :=
{ mul_left_inv := λ a, subtype.ext $ inv_mul_cancel a.2.ne',
  .. positive.subtype.has_inv, .. positive.subtype.linear_ordered_comm_monoid }

end mul_comm

end positive
