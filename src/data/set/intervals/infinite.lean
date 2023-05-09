/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import data.set.finite

/-!
# Infinitude of intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/

variables {α : Type*} [preorder α]

/-- A nonempty preorder with no maximal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
lemma no_max_order.infinite [nonempty α] [no_max_order α] : infinite α :=
let ⟨f, hf⟩ := nat.exists_strict_mono α in infinite.of_injective f hf.injective

/-- A nonempty preorder with no minimal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
lemma no_min_order.infinite [nonempty α] [no_min_order α] : infinite α :=
@no_max_order.infinite αᵒᵈ _ _ _

namespace set

section densely_ordered

variables [densely_ordered α] {a b : α} (h : a < b)

lemma Ioo.infinite : infinite (Ioo a b) := @no_max_order.infinite _ _ (nonempty_Ioo_subtype h) _
lemma Ioo_infinite : (Ioo a b).infinite := infinite_coe_iff.1 $ Ioo.infinite h

lemma Ico_infinite : (Ico a b).infinite := (Ioo_infinite h).mono Ioo_subset_Ico_self
lemma Ico.infinite : infinite (Ico a b) := infinite_coe_iff.2 $ Ico_infinite h

lemma Ioc_infinite : (Ioc a b).infinite := (Ioo_infinite h).mono Ioo_subset_Ioc_self
lemma Ioc.infinite : infinite (Ioc a b) := infinite_coe_iff.2 $ Ioc_infinite h

lemma Icc_infinite : (Icc a b).infinite := (Ioo_infinite h).mono Ioo_subset_Icc_self
lemma Icc.infinite : infinite (Icc a b) := infinite_coe_iff.2 $ Icc_infinite h

end densely_ordered

instance [no_min_order α] {a : α} : infinite (Iio a) := no_min_order.infinite
lemma Iio_infinite [no_min_order α] (a : α) : (Iio a).infinite := infinite_coe_iff.1 Iio.infinite

instance [no_min_order α] {a : α} : infinite (Iic a) := no_min_order.infinite
lemma Iic_infinite [no_min_order α] (a : α) : (Iic a).infinite := infinite_coe_iff.1 Iic.infinite

instance [no_max_order α] {a : α} : infinite (Ioi a) := no_max_order.infinite
lemma Ioi_infinite [no_max_order α] (a : α) : (Ioi a).infinite := infinite_coe_iff.1 Ioi.infinite

instance [no_max_order α] {a : α} : infinite (Ici a) := no_max_order.infinite
lemma Ici_infinite [no_max_order α] (a : α) : (Ici a).infinite := infinite_coe_iff.1 Ici.infinite

end set
