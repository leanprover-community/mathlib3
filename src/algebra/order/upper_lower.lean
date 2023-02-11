/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.group.defs
import data.set.pointwise.smul
import order.upper_lower.basic

/-!
# Algebraic operations on upper/lower sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Upper/lower sets are preserved under pointwise algebraic operations in ordered groups.
-/

open function set
open_locale pointwise

section ordered_comm_monoid
variables {α : Type*} [ordered_comm_monoid α] {s : set α} {x : α}

@[to_additive] lemma is_upper_set.smul_subset (hs : is_upper_set s) (hx : 1 ≤ x) : x • s ⊆ s :=
smul_set_subset_iff.2 $ λ y, hs $ le_mul_of_one_le_left' hx

@[to_additive] lemma is_lower_set.smul_subset (hs : is_lower_set s) (hx : x ≤ 1) : x • s ⊆ s :=
smul_set_subset_iff.2 $ λ y, hs $ mul_le_of_le_one_left' hx

end ordered_comm_monoid

section ordered_comm_group
variables {α : Type*} [ordered_comm_group α] {s t : set α} {a : α}

@[to_additive] lemma is_upper_set.smul (hs : is_upper_set s) : is_upper_set (a • s) :=
begin
  rintro _ y hxy ⟨x, hx, rfl⟩,
  exact mem_smul_set_iff_inv_smul_mem.2 (hs (le_inv_mul_iff_mul_le.2 hxy) hx),
end

@[to_additive] lemma is_lower_set.smul (hs : is_lower_set s) : is_lower_set (a • s) :=
hs.of_dual.smul

@[to_additive] lemma set.ord_connected.smul (hs : s.ord_connected) : (a • s).ord_connected :=
begin
  rw [←hs.upper_closure_inter_lower_closure, smul_set_inter],
  exact (upper_closure _).upper.smul.ord_connected.inter (lower_closure _).lower.smul.ord_connected,
end

@[to_additive] lemma is_upper_set.mul_left (ht : is_upper_set t) : is_upper_set (s * t) :=
by { rw [←smul_eq_mul, ←bUnion_smul_set], exact is_upper_set_Union₂ (λ x hx, ht.smul) }

@[to_additive] lemma is_upper_set.mul_right (hs : is_upper_set s) : is_upper_set (s * t) :=
by { rw mul_comm, exact hs.mul_left }

@[to_additive] lemma is_lower_set.mul_left (ht : is_lower_set t) : is_lower_set (s * t) :=
ht.of_dual.mul_left

@[to_additive] lemma is_lower_set.mul_right (hs : is_lower_set s) : is_lower_set (s * t) :=
hs.of_dual.mul_right

@[to_additive] lemma is_upper_set.inv (hs : is_upper_set s) : is_lower_set s⁻¹ :=
λ x y h, hs $ inv_le_inv' h

@[to_additive] lemma is_lower_set.inv (hs : is_lower_set s) : is_upper_set s⁻¹ :=
λ x y h, hs $ inv_le_inv' h

@[to_additive] lemma is_upper_set.div_left (ht : is_upper_set t) : is_lower_set (s / t) :=
by { rw div_eq_mul_inv, exact ht.inv.mul_left }

@[to_additive] lemma is_upper_set.div_right (hs : is_upper_set s) : is_upper_set (s / t) :=
by { rw div_eq_mul_inv, exact hs.mul_right }

@[to_additive] lemma is_lower_set.div_left (ht : is_lower_set t) : is_upper_set (s / t) :=
ht.of_dual.div_left

@[to_additive] lemma is_lower_set.div_right (hs : is_lower_set s) : is_lower_set (s / t) :=
hs.of_dual.div_right

namespace upper_set

@[to_additive] instance : has_one (upper_set α) := ⟨Ici 1⟩
@[to_additive] instance : has_mul (upper_set α) := ⟨λ s t, ⟨image2 (*) s t, s.2.mul_right⟩⟩
@[to_additive] instance : has_div (upper_set α) := ⟨λ s t, ⟨image2 (/) s t, s.2.div_right⟩⟩
@[to_additive] instance : has_smul α (upper_set α) := ⟨λ a s, ⟨(•) a '' s, s.2.smul⟩⟩

@[simp, norm_cast, to_additive] lemma coe_one : ((1 : upper_set α) : set α) = set.Ici 1 := rfl
@[simp, norm_cast, to_additive]
lemma coe_smul (a : α) (s : upper_set α) : (↑(a • s) : set α) = a • s := rfl
@[simp, norm_cast, to_additive]
lemma coe_mul (s t : upper_set α) : (↑(s * t) : set α) = s * t := rfl
@[simp, norm_cast, to_additive]
lemma coe_div (s t : upper_set α) : (↑(s / t) : set α) = s / t := rfl

@[simp, to_additive] lemma Ici_one : Ici (1 : α) = 1 := rfl

@[to_additive] instance : mul_action α (upper_set α) := set_like.coe_injective.mul_action _ coe_smul

@[to_additive]
instance : comm_semigroup (upper_set α) :=
{ mul := (*),
  ..(set_like.coe_injective.comm_semigroup _ coe_mul : comm_semigroup (upper_set α)) }

@[to_additive]
private lemma one_mul (s : upper_set α) : 1 * s = s :=
set_like.coe_injective $ (subset_mul_right _ left_mem_Ici).antisymm' $
    by { rw [←smul_eq_mul, ←bUnion_smul_set], exact Union₂_subset (λ _, s.upper.smul_subset) }

@[to_additive] instance : comm_monoid (upper_set α) :=
{ one := 1,
  one_mul := one_mul,
  mul_one := λ s, by { rw mul_comm, exact one_mul _ },
  ..upper_set.comm_semigroup }

end upper_set

namespace lower_set

@[to_additive] instance : has_one (lower_set α) := ⟨Iic 1⟩
@[to_additive] instance : has_mul (lower_set α) := ⟨λ s t, ⟨image2 (*) s t, s.2.mul_right⟩⟩
@[to_additive] instance : has_div (lower_set α) := ⟨λ s t, ⟨image2 (/) s t, s.2.div_right⟩⟩
@[to_additive] instance : has_smul α (lower_set α) := ⟨λ a s, ⟨(•) a '' s, s.2.smul⟩⟩

@[simp, norm_cast, to_additive]
lemma coe_smul (a : α) (s : lower_set α) : (↑(a • s) : set α) = a • s := rfl
@[simp, norm_cast, to_additive]
lemma coe_mul (s t : lower_set α) : (↑(s * t) : set α) = s * t := rfl
@[simp, norm_cast, to_additive]
lemma coe_div (s t : lower_set α) : (↑(s / t) : set α) = s / t := rfl

@[simp, to_additive] lemma Iic_one : Iic (1 : α) = 1 := rfl

@[to_additive] instance : mul_action α (lower_set α) := set_like.coe_injective.mul_action _ coe_smul

@[to_additive]
instance : comm_semigroup (lower_set α) :=
{ mul := (*),
  ..(set_like.coe_injective.comm_semigroup _ coe_mul : comm_semigroup (lower_set α)) }

@[to_additive]
private lemma one_mul (s : lower_set α) : 1 * s = s :=
set_like.coe_injective $ (subset_mul_right _ right_mem_Iic).antisymm' $
    by { rw [←smul_eq_mul, ←bUnion_smul_set], exact Union₂_subset (λ _, s.lower.smul_subset) }

@[to_additive] instance : comm_monoid (lower_set α) :=
{ one := 1,
  one_mul := one_mul,
  mul_one := λ s, by { rw mul_comm, exact one_mul _ },
  ..lower_set.comm_semigroup }

end lower_set

variables (a s t)

@[simp, to_additive] lemma upper_closure_one : upper_closure (1 : set α) = 1 :=
upper_closure_singleton _

@[simp, to_additive] lemma lower_closure_one : lower_closure (1 : set α) = 1 :=
lower_closure_singleton _

@[simp, to_additive] lemma upper_closure_smul : upper_closure (a • s) = a • upper_closure s :=
upper_closure_image $ order_iso.mul_left a

@[simp, to_additive] lemma lower_closure_smul : lower_closure (a • s) = a • lower_closure s :=
lower_closure_image $ order_iso.mul_left a

@[to_additive] lemma mul_upper_closure : s * upper_closure t = upper_closure (s * t) :=
by simp_rw [←smul_eq_mul, ←bUnion_smul_set, upper_closure_Union, upper_closure_smul,
  upper_set.coe_infi₂, upper_set.coe_smul]

@[to_additive] lemma mul_lower_closure : s * lower_closure t = lower_closure (s * t) :=
by simp_rw [←smul_eq_mul, ←bUnion_smul_set, lower_closure_Union, lower_closure_smul,
  lower_set.coe_supr₂, lower_set.coe_smul]

@[to_additive] lemma upper_closure_mul : ↑(upper_closure s) * t = upper_closure (s * t) :=
by { simp_rw mul_comm _ t, exact mul_upper_closure _ _ }

@[to_additive] lemma lower_closure_mul : ↑(lower_closure s) * t = lower_closure (s * t) :=
by { simp_rw mul_comm _ t, exact mul_lower_closure _ _ }

@[simp, to_additive]
lemma upper_closure_mul_distrib : upper_closure (s * t) = upper_closure s * upper_closure t :=
set_like.coe_injective $
  by rw [upper_set.coe_mul, mul_upper_closure, upper_closure_mul, upper_set.upper_closure]

@[simp, to_additive]
lemma lower_closure_mul_distrib : lower_closure (s * t) = lower_closure s * lower_closure t :=
set_like.coe_injective $
  by rw [lower_set.coe_mul, mul_lower_closure, lower_closure_mul, lower_set.lower_closure]

end ordered_comm_group
