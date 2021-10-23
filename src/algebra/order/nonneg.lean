/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.order.archimedean
import algebra.order.sub
import algebra.order.with_zero
import order.lattice_intervals
import order.conditionally_complete_lattice

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_add_monoid` if `α` is a `linear_ordered_ring`.
* `{x : α // 0 ≤ x}` is a `linear_ordered_comm_group_with_zero` if `α` is a `linear_ordered_field`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing and element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `set.Ici` to this subtype.
-/

open set

variables {α : Type*}

namespace nonneg

instance order_bot [partial_order α] {a : α} : order_bot {x : α // a ≤ x} :=
set.Ici.order_bot

instance no_top_order [partial_order α] [no_top_order α] {a : α} : no_top_order {x : α // a ≤ x} :=
set.Ici.no_top_order

instance semilattice_inf_bot [semilattice_inf α] {a : α} : semilattice_inf_bot {x : α // a ≤ x} :=
set.Ici.semilattice_inf_bot

instance densely_ordered [preorder α] [densely_ordered α] {a : α} :
  densely_ordered {x : α // a ≤ x} :=
show densely_ordered (Ici a), from set.densely_ordered

/-- If `Sup ∅ ≤ a` then `{x : α // a ≤ x}` is a `conditionally_complete_linear_order_bot`. -/
@[reducible]
protected noncomputable def conditionally_complete_linear_order_bot
  [conditionally_complete_linear_order α] {a : α} (h : Sup ∅ ≤ a) :
  conditionally_complete_linear_order_bot {x : α // a ≤ x} :=
{ cSup_empty := (function.funext_iff.1
    (@subset_Sup_def α (set.Ici a) _ ⟨⟨a, le_rfl⟩⟩) ∅).trans $ subtype.eq $
      by { cases h.lt_or_eq with h2 h2, { simp [h2.not_le] }, simp [h2] },
  ..nonneg.order_bot,
  .. @ord_connected_subset_conditionally_complete_linear_order α (set.Ici a) _ ⟨⟨a, le_rfl⟩⟩ _ }

instance inhabited [preorder α] {a : α} : inhabited {x : α // a ≤ x} :=
⟨⟨a, le_rfl⟩⟩

instance has_zero [has_zero α] [preorder α] : has_zero {x : α // 0 ≤ x} :=
⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]
protected lemma coe_zero [has_zero α] [preorder α] : ((0 : {x : α // 0 ≤ x}) : α) = 0 := rfl

@[simp] lemma mk_eq_zero [has_zero α] [preorder α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) = 0 ↔ x = 0 :=
subtype.ext_iff

instance has_add [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)] :
  has_add {x : α // 0 ≤ x} :=
⟨λ x y, ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp] lemma mk_add_mk [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)] {x y : α}
  (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : {x : α // 0 ≤ x}) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
rfl

@[simp, norm_cast]
protected lemma coe_add [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)]
  (a b : {x : α // 0 ≤ x}) : ((a + b : {x : α // 0 ≤ x}) : α) = a + b := rfl

instance ordered_add_comm_monoid [ordered_add_comm_monoid α] :
  ordered_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_add_comm_monoid (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

instance linear_ordered_add_comm_monoid [linear_ordered_add_comm_monoid α] :
  linear_ordered_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_add_comm_monoid (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

instance ordered_cancel_add_comm_monoid [ordered_cancel_add_comm_monoid α] :
  ordered_cancel_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_cancel_add_comm_monoid (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

instance linear_ordered_cancel_add_comm_monoid [linear_ordered_cancel_add_comm_monoid α] :
  linear_ordered_cancel_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_cancel_add_comm_monoid
  (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

/-- Coercion `{x : α // 0 ≤ x} → α` as a `add_monoid_hom`. -/
def coe_add_monoid_hom [ordered_add_comm_monoid α] : {x : α // 0 ≤ x} →+ α :=
⟨coe, nonneg.coe_zero, nonneg.coe_add⟩

@[norm_cast]
lemma nsmul_coe [ordered_add_comm_monoid α] (n : ℕ) (r : {x : α // 0 ≤ x}) :
  ↑(n • r) = n • (r : α) :=
nonneg.coe_add_monoid_hom.map_nsmul _ _

instance archimedean [ordered_add_comm_monoid α] [archimedean α] : archimedean {x : α // 0 ≤ x} :=
⟨ assume x y pos_y,
  let ⟨n, hr⟩ := archimedean.arch (x : α) (pos_y : (0 : α) < y) in
  ⟨n, show (x : α) ≤ (n • y : {x : α // 0 ≤ x}), by simp [*, -nsmul_eq_mul, nsmul_coe]⟩ ⟩

instance has_one [ordered_semiring α] : has_one {x : α // 0 ≤ x} :=
{ one := ⟨1, zero_le_one⟩ }

@[simp, norm_cast]
protected lemma coe_one [ordered_semiring α] : ((1 : {x : α // 0 ≤ x}) : α) = 1 := rfl

@[simp] lemma mk_eq_one [ordered_semiring α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) = 1 ↔ x = 1 :=
subtype.ext_iff

instance has_mul [ordered_semiring α] : has_mul {x : α // 0 ≤ x} :=
{ mul := λ x y, ⟨x * y, mul_nonneg x.2 y.2⟩ }

@[simp, norm_cast]
protected lemma coe_mul [ordered_semiring α] (a b : {x : α // 0 ≤ x}) :
  ((a * b : {x : α // 0 ≤ x}) : α) = a * b := rfl

@[simp] lemma mk_mul_mk [ordered_semiring α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
rfl

instance ordered_semiring [ordered_semiring α] : ordered_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_semiring
  (coe : {x : α // 0 ≤ x} → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance ordered_comm_semiring [ordered_comm_semiring α] : ordered_comm_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_comm_semiring
  (coe : {x : α // 0 ≤ x} → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance nontrivial [linear_ordered_semiring α] : nontrivial {x : α // 0 ≤ x} :=
⟨ ⟨0, 1, λ h, zero_ne_one (congr_arg subtype.val h)⟩ ⟩

instance linear_ordered_semiring [linear_ordered_semiring α] :
  linear_ordered_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_semiring
  (coe : {x : α // 0 ≤ x} → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance linear_ordered_comm_monoid_with_zero [linear_ordered_comm_ring α] :
  linear_ordered_comm_monoid_with_zero {x : α // 0 ≤ x} :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_of_nonneg_left h c.2,
  ..nonneg.linear_ordered_semiring,
  ..nonneg.ordered_comm_semiring }

/-- Coercion `{x : α // 0 ≤ x} → α` as a `ring_hom`. -/
def coe_ring_hom [ordered_semiring α] : {x : α // 0 ≤ x} →+* α :=
⟨coe, nonneg.coe_one, nonneg.coe_mul, nonneg.coe_zero, nonneg.coe_add⟩

instance has_inv [linear_ordered_field α] : has_inv {x : α // 0 ≤ x} :=
{ inv := λ x, ⟨x⁻¹, inv_nonneg.mpr x.2⟩ }

@[simp, norm_cast]
protected lemma coe_inv [linear_ordered_field α] (a : {x : α // 0 ≤ x}) :
  ((a⁻¹ : {x : α // 0 ≤ x}) : α) = a⁻¹ := rfl

@[simp] lemma inv_mk [linear_ordered_field α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x})⁻¹ = ⟨x⁻¹, inv_nonneg.mpr hx⟩ :=
rfl

instance linear_ordered_comm_group_with_zero [linear_ordered_field α] :
  linear_ordered_comm_group_with_zero {x : α // 0 ≤ x} :=
{ inv_zero := by { ext, exact inv_zero },
  mul_inv_cancel := by { intros a ha, ext, refine mul_inv_cancel (mt (λ h, _) ha), ext, exact h },
  ..nonneg.nontrivial,
  ..nonneg.has_inv,
  ..nonneg.linear_ordered_comm_monoid_with_zero }

instance has_div [linear_ordered_field α] : has_div {x : α // 0 ≤ x} :=
{ div := λ x y, ⟨x / y, div_nonneg x.2 y.2⟩ }

@[simp, norm_cast]
protected lemma coe_div [linear_ordered_field α] (a b : {x : α // 0 ≤ x}) :
  ((a / b : {x : α // 0 ≤ x}) : α) = a / b := rfl

@[simp] lemma mk_div_mk [linear_ordered_field α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
rfl

instance canonically_ordered_add_monoid [ordered_ring α] :
  canonically_ordered_add_monoid {x : α // 0 ≤ x} :=
{ le_iff_exists_add     := λ ⟨a, ha⟩ ⟨b, hb⟩,
    by simpa only [mk_add_mk, subtype.exists, subtype.mk_eq_mk] using le_iff_exists_nonneg_add a b,
  ..nonneg.ordered_add_comm_monoid,
  ..nonneg.order_bot }

instance canonically_ordered_comm_semiring [ordered_comm_ring α] [no_zero_divisors α] :
  canonically_ordered_comm_semiring {x : α // 0 ≤ x} :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by { rintro ⟨a, ha⟩ ⟨b, hb⟩, simp },
  ..nonneg.canonically_ordered_add_monoid,
  ..nonneg.ordered_comm_semiring }

instance canonically_linear_ordered_add_monoid [linear_ordered_ring α] :
  canonically_linear_ordered_add_monoid {x : α // 0 ≤ x} :=
{ ..subtype.linear_order _, ..nonneg.canonically_ordered_add_monoid }

section linear_order

variables [has_zero α] [linear_order α]

/-- The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`. -/
def to_nonneg (a : α) : {x : α // 0 ≤ x} :=
⟨max a 0, le_max_right _ _⟩

@[simp]
lemma coe_to_nonneg {a : α} : (to_nonneg a : α) = max a 0 := rfl

@[simp]
lemma to_nonneg_of_nonneg {a : α} (h : 0 ≤ a) : to_nonneg a = ⟨a, h⟩ :=
by simp [to_nonneg, h]

@[simp]
lemma to_nonneg_coe {a : {x : α // 0 ≤ x}} : to_nonneg (a : α) = a :=
by { cases a with a ha, exact to_nonneg_of_nonneg ha }

@[simp]
lemma to_nonneg_le {a : α} {b : {x : α // 0 ≤ x}} : to_nonneg a ≤ b ↔ a ≤ b :=
by { cases b with b hb, simp [to_nonneg, hb] }

@[simp]
lemma to_nonneg_lt {a : {x : α // 0 ≤ x}} {b : α} : a < to_nonneg b ↔ ↑a < b :=
by { cases a with a ha, simp [to_nonneg, ha.not_lt] }

instance has_sub [has_sub α] : has_sub {x : α // 0 ≤ x} :=
⟨λ x y, to_nonneg (x - y)⟩

@[simp] lemma mk_sub_mk [has_sub α] {x y : α}
  (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : {x : α // 0 ≤ x}) - ⟨y, hy⟩ = to_nonneg (x - y) :=
rfl

end linear_order

instance has_ordered_sub [linear_ordered_ring α] : has_ordered_sub {x : α // 0 ≤ x} :=
⟨by { rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, simp only [sub_le_iff_le_add, subtype.mk_le_mk, mk_sub_mk,
  mk_add_mk, to_nonneg_le, subtype.coe_mk]}⟩

end nonneg
