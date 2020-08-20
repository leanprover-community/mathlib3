/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Heather Macbeth
-/
import data.set.intervals.basic
import data.set.function

/-!
# Strictly monotone, surjective functions are surjective on intervals

A strictly monotone, surjective function sends any interval in the domain to the interval with
corresponding endpoints in the range.  This is expressed in this file using `set.surj_on`, and
provided for all permutations of interval endpoints.
-/

variables {α : Type*} {β : Type*} [linear_order α] [preorder β] {f : α → β}

open set function

lemma surj_on_Icc_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a b : α) :
  surj_on f (set.Icc a b) (set.Icc (f a) (f b)) :=
begin
  refine surj_on_of_surjective h_surj _,
  intros p hp,
  exact ⟨h_mono.le_iff_le.mp hp.1, h_mono.le_iff_le.mp hp.2⟩
end

lemma surj_on_Ico_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a b : α) :
  set.surj_on f (set.Ico a b) (set.Ico (f a) (f b)) :=
begin
  refine surj_on_of_surjective h_surj _,
  intros p hp,
  exact ⟨h_mono.le_iff_le.mp hp.1, h_mono.lt_iff_lt.mp hp.2⟩
end

lemma surj_on_Ioc_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a b : α) :
  set.surj_on f (set.Ioc a b) (set.Ioc (f a) (f b)) :=
begin
  convert @surj_on_Ico_of_strict_mono_surjective _ _ _ _ _ (strict_mono.order_dual h_mono) h_surj b a;
  simp
end

lemma surj_on_Ioo_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a b : α) :
  set.surj_on f (set.Ioo a b) (set.Ioo (f a) (f b)) :=
begin
  refine surj_on_of_surjective h_surj _,
  intros p hp,
  exact ⟨h_mono.lt_iff_lt.mp hp.1, h_mono.lt_iff_lt.mp hp.2⟩
end

lemma surj_on_Ici_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a : α) :
  set.surj_on f (set.Ici a) (set.Ici (f a)) :=
begin
  refine surj_on_of_surjective h_surj _,
  intros p hp,
  exact h_mono.le_iff_le.mp hp
end

lemma surj_on_Iic_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a : α) :
  set.surj_on f (set.Iic a) (set.Iic (f a)) :=
@surj_on_Ici_of_strict_mono_surjective _ _ _ _ _ (strict_mono.order_dual h_mono) h_surj a

lemma surj_on_Ioi_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a : α) :
  set.surj_on f (set.Ioi a) (set.Ioi (f a)) :=
begin
  refine surj_on_of_surjective h_surj _,
  intros p hp,
  exact h_mono.lt_iff_lt.mp hp
end

lemma surj_on_Iio_of_strict_mono_surjective
  (h_mono : strict_mono f) (h_surj : function.surjective f) (a : α) :
  set.surj_on f (set.Iio a) (set.Iio (f a)) :=
@surj_on_Ioi_of_strict_mono_surjective _ _ _ _ _ (strict_mono.order_dual h_mono) h_surj a
