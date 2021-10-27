/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import data.set.finite

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side.
-/

namespace set

variables {α : Type*} [preorder α]

section bounded

variables [densely_ordered α]

lemma Ioo.infinite {a b : α} (h : a < b) : infinite (Ioo a b) :=
begin
  rintro (f : finite (Ioo a b)),
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m ∈ Ioo a b, ∀ x ∈ Ioo a b, ¬x < m,
  { simpa [h] using finset.exists_minimal f.to_finset },
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z, a < z ∧ z < m := exists_between hm₁.1,
  exact hm₂ z ⟨hz₁, lt_trans hz₂ hm₁.2⟩ hz₂,
end

lemma Ico.infinite {a b : α} (h : a < b) : infinite (Ico a b) :=
(Ioo.infinite h).mono Ioo_subset_Ico_self

lemma Ioc.infinite {a b : α} (h : a < b) : infinite (Ioc a b) :=
(Ioo.infinite h).mono Ioo_subset_Ioc_self

lemma Icc.infinite {a b : α} (h : a < b) : infinite (Icc a b) :=
(Ioo.infinite h).mono Ioo_subset_Icc_self

end bounded

section unbounded_below

variables [no_bot_order α]

lemma Iio.infinite {b : α} : infinite (Iio b) :=
begin
  rintro (f : finite (Iio b)),
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m < b, ∀ x < b, ¬x < m,
  { simpa using finset.exists_minimal f.to_finset },
  obtain ⟨z, hz⟩ : ∃ z, z < m := no_bot _,
  exact hm₂ z (lt_trans hz hm₁) hz
end

lemma Iic.infinite {b : α} : infinite (Iic b) :=
Iio.infinite.mono Iio_subset_Iic_self

end unbounded_below

section unbounded_above

variables [no_top_order α]

lemma Ioi.infinite {a : α} : infinite (Ioi a) :=
by apply @Iio.infinite (order_dual α)

lemma Ici.infinite {a : α} : infinite (Ici a) :=
Ioi.infinite.mono Ioi_subset_Ici_self

end unbounded_above

end set
