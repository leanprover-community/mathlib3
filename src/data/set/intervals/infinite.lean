/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import data.set.finite

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/

variables {α : Type*} [preorder α]

@[priority 100]
instance no_max_order.infinite [nonempty α] [no_max_order α] : infinite α :=
let ⟨f, hf⟩ := nat.exists_strict_mono α in infinite.of_injective f hf.injective

@[priority 100]
instance no_min_order.infinite [nonempty α] [no_min_order α] : infinite α :=
@no_max_order.infinite αᵒᵈ _ _ _

namespace set

section bounded

variables [densely_ordered α]

lemma Ioo.infinite {a b : α} (h : a < b) : (Ioo a b).infinite :=
begin
  haveI := nonempty_Ioo_subtype h,
  exact infinite_coe_iff.1 no_max_order.infinite
end

lemma Ico.infinite {a b : α} (h : a < b) : (Ico a b).infinite :=
(Ioo.infinite h).mono Ioo_subset_Ico_self

lemma Ioc.infinite {a b : α} (h : a < b) : (Ioc a b).infinite :=
(Ioo.infinite h).mono Ioo_subset_Ioc_self

lemma Icc.infinite {a b : α} (h : a < b) : (Icc a b).infinite :=
(Ioo.infinite h).mono Ioo_subset_Icc_self

end bounded

section unbounded_below

variables [no_min_order α] {a : α}

lemma Iio.infinite {b : α} : (Iio b).infinite :=
infinite_coe_iff.1 no_min_order.infinite

lemma Iic.infinite {b : α} : (Iic b).infinite :=
Iio.infinite.mono Iio_subset_Iic_self

end unbounded_below

section unbounded_above

variables [no_max_order α]

lemma Ioi.infinite {a : α} : (Ioi a).infinite := @Iio.infinite αᵒᵈ _ _ _

lemma Ici.infinite {a : α} : (Ici a).infinite :=
Ioi.infinite.mono Ioi_subset_Ici_self

end unbounded_above

end set
