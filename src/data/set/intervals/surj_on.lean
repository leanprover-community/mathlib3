/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import data.set.intervals.basic
import data.set.function

/-!
# Monotone surjective functions are surjective on intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range.  This is expressed in this file using `set.surj_on`, and provided for all
permutations of interval endpoints.
-/

variables {α : Type*} {β : Type*} [linear_order α] [partial_order β] {f : α → β}

open set function order_dual (to_dual)

lemma surj_on_Ioo_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a b : α) :
  surj_on f (Ioo a b) (Ioo (f a) (f b)) :=
begin
  intros p hp,
  rcases h_surj p with ⟨x, rfl⟩,
  refine ⟨x, mem_Ioo.2 _, rfl⟩,
  contrapose! hp,
  exact λ h, h.2.not_le (h_mono $ hp $ h_mono.reflect_lt h.1)
end

lemma surj_on_Ico_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a b : α) :
  surj_on f (Ico a b) (Ico (f a) (f b)) :=
begin
  obtain hab | hab := lt_or_le a b,
  { intros p hp,
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with rfl|hp',
    { exact mem_image_of_mem f (left_mem_Ico.mpr hab) },
    { have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp',
      exact image_subset f Ioo_subset_Ico_self this } },
  { rw Ico_eq_empty (h_mono hab).not_lt,
    exact surj_on_empty f _ }
end

lemma surj_on_Ioc_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a b : α) :
  surj_on f (Ioc a b) (Ioc (f a) (f b)) :=
by simpa using surj_on_Ico_of_monotone_surjective h_mono.dual h_surj (to_dual b) (to_dual a)

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
lemma surj_on_Icc_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) {a b : α} (hab : a ≤ b) :
  surj_on f (Icc a b) (Icc (f a) (f b)) :=
begin
  intros p hp,
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl|rfl|hp'),
  { exact ⟨a, left_mem_Icc.mpr hab, rfl⟩ },
  { exact ⟨b, right_mem_Icc.mpr hab, rfl⟩ },
  { have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp',
    exact image_subset f Ioo_subset_Icc_self this }
end

lemma surj_on_Ioi_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Ioi a) (Ioi (f a)) :=
begin
  rw [← compl_Iic, ← compl_compl (Ioi (f a))],
  refine maps_to.surj_on_compl _ h_surj,
  exact λ x hx, (h_mono hx).not_lt
end

lemma surj_on_Iio_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Iio a) (Iio (f a)) :=
@surj_on_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a

lemma surj_on_Ici_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Ici a) (Ici (f a)) :=
begin
  rw [← Ioi_union_left, ← Ioi_union_left],
  exact (surj_on_Ioi_of_monotone_surjective h_mono h_surj a).union_union
    (@image_singleton _ _ f a ▸ surj_on_image _ _)
end

lemma surj_on_Iic_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Iic a) (Iic (f a)) :=
@surj_on_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
