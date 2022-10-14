/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.group
import order.upper_lower

/-!
# Algebraic operations on upper/lower sets

Upper/lower sets are preserved under pointwise algebraic operations in ordered groups.
-/

alias ne_of_eq_of_ne ← eq.trans_ne
alias ne_of_ne_of_eq ← ne.trans_eq

open function set
open_locale pointwise

section
variables {α : Type*} [mul_one_class α] [has_lt α] [contravariant_class α α (*) (<)] {a b : α}

@[to_additive] lemma one_lt_of_lt_mul_right : a < a * b → 1 < b :=
by simpa only [mul_one] using (lt_of_mul_lt_mul_left' : a * 1 < a * b → 1 < b)

end

section
variables {α : Type*} [mul_one_class α] [preorder α] [contravariant_class α α (*) (<)]
  [has_exists_mul_of_le α] {a b : α}

@[to_additive] lemma exists_one_lt_mul_of_lt' (h : a < b) : ∃ c, 1 < c ∧ a * c = b :=
by { obtain ⟨c, rfl⟩ := exists_mul_of_le h.le, exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩ }

end

section finite
variables {α ι : Type*} [linear_ordered_semifield α] [has_exists_add_of_le α] [finite ι]
  {x y : ι → α}

lemma pi.exists_forall_pos_add_lt (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i :=
begin
  casesI nonempty_fintype ι,
  casesI is_empty_or_nonempty ι,
  { exact ⟨1, zero_lt_one, is_empty_elim⟩ },
  choose ε hε hxε using λ i, exists_pos_add_of_lt' (h i),
  obtain rfl : x + ε = y := funext hxε,
  have hε : 0 < finset.univ.inf' finset.univ_nonempty ε := (finset.lt_inf'_iff _).2 (λ i _, hε _),
  exact ⟨_, half_pos hε, λ i, add_lt_add_left ((half_lt_self hε).trans_le $ finset.inf'_le _ $
    finset.mem_univ _) _⟩,
end

end finite

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
⟨begin
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz,
  exact mem_smul_set_iff_inv_smul_mem.2
    (hs.out hx hy ⟨le_inv_mul_iff_mul_le.2 hz.1, inv_mul_le_iff_le_mul.2 hz.2⟩),
end⟩

@[to_additive] lemma is_upper_set.mul_left (ht : is_upper_set t) : is_upper_set (s * t) :=
by { rw [←smul_eq_mul, ←bUnion_smul_set], exact is_upper_set_Union₂ (λ x hx, ht.smul) }

@[to_additive] lemma is_upper_set.mul_right (hs : is_upper_set s) : is_upper_set (s * t) :=
by { rw mul_comm, exact hs.mul_left }

@[to_additive] lemma is_lower_set.mul_left (ht : is_lower_set t) : is_lower_set (s * t) :=
ht.of_dual.mul_left

@[to_additive] lemma is_lower_set.mul_right (hs : is_lower_set s) : is_lower_set (s * t) :=
hs.of_dual.mul_right

@[to_additive] lemma is_upper_set.div_left (ht : is_upper_set t) : is_lower_set (s / t) :=
begin
  rw [←image2_div, ←Union_image_left],
  refine is_lower_set_Union₂ (λ x hx, _),
  rintro _ z hyz ⟨y, hy, rfl⟩,
  exact ⟨x / z, ht (by rwa le_div'') hy, div_div_cancel _ _⟩,
end

@[to_additive] lemma is_upper_set.div_right (hs : is_upper_set s) : is_upper_set (s / t) :=
begin
  rw [←image2_div, ←Union_image_right],
  refine is_upper_set_Union₂ (λ x hx, _),
  rintro _ z hyz ⟨y, hy, rfl⟩,
  exact ⟨x * z, hs (by rwa ←div_le_iff_le_mul') hy, mul_div_cancel''' _ _⟩,
end

@[to_additive] lemma is_lower_set.div_left (ht : is_lower_set t) : is_upper_set (s / t) :=
ht.of_dual.div_left

@[to_additive] lemma is_lower_set.div_right (hs : is_lower_set s) : is_lower_set (s / t) :=
hs.of_dual.div_right

namespace upper_set

@[to_additive] instance : has_mul (upper_set α) := ⟨λ s t, ⟨s * t, s.2.mul_right⟩⟩
@[to_additive] instance : has_div (upper_set α) := ⟨λ s t, ⟨s / t, s.2.div_right⟩⟩
@[to_additive] instance : has_smul α (upper_set α) := ⟨λ a s, ⟨a • s, s.2.smul⟩⟩

@[simp, norm_cast, to_additive]
lemma coe_smul (a : α) (s : upper_set α) : (↑(a • s) : set α) = a • s := rfl
@[simp, norm_cast, to_additive]
lemma coe_mul (s t : upper_set α) : (↑(s * t) : set α) = s * t := rfl
@[simp, norm_cast, to_additive]
lemma coe_div (s t : upper_set α) : (↑(s / t) : set α) = s / t := rfl

@[to_additive] instance : mul_action α (upper_set α) := set_like.coe_injective.mul_action _ coe_smul

end upper_set

namespace lower_set

@[to_additive] instance : has_mul (lower_set α) := ⟨λ s t, ⟨s * t, s.2.mul_right⟩⟩
@[to_additive] instance : has_div (lower_set α) := ⟨λ s t, ⟨s / t, s.2.div_right⟩⟩
@[to_additive] instance : has_smul α (lower_set α) := ⟨λ a s, ⟨a • s, s.2.smul⟩⟩

@[simp, norm_cast, to_additive]
lemma coe_smul (a : α) (s : lower_set α) : (↑(a • s) : set α) = a • s := rfl
@[simp, norm_cast, to_additive]
lemma coe_mul (s t : lower_set α) : (↑(s * t) : set α) = s * t := rfl
@[simp, norm_cast, to_additive]
lemma coe_div (s t : lower_set α) : (↑(s / t) : set α) = s / t := rfl

@[to_additive] instance : mul_action α (lower_set α) := set_like.coe_injective.mul_action _ coe_smul

end lower_set

end ordered_comm_group
