/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex J. Best
-/
import measure_theory.group.arithmetic

/-!
# Pointwise set operations on `measurable_set`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `measurable_set.mul` etc.
-/

open_locale pointwise
open set

@[to_additive]
lemma measurable_set.const_smul {G α : Type*} [group G] [mul_action G α] [measurable_space G]
  [measurable_space α] [has_measurable_smul G α] {s : set α} (hs : measurable_set s) (a : G) :
  measurable_set (a • s) :=
begin
  rw ← preimage_smul_inv,
  exact measurable_const_smul _ hs
end

lemma measurable_set.const_smul_of_ne_zero {G₀ α : Type*} [group_with_zero G₀] [mul_action G₀ α]
  [measurable_space G₀] [measurable_space α] [has_measurable_smul G₀ α] {s : set α}
  (hs : measurable_set s) {a : G₀} (ha : a ≠ 0) :
  measurable_set (a • s) :=
begin
  rw ← preimage_smul_inv₀ ha,
  exact measurable_const_smul _ hs
end

lemma measurable_set.const_smul₀ {G₀ α : Type*} [group_with_zero G₀] [has_zero α]
  [mul_action_with_zero G₀ α] [measurable_space G₀] [measurable_space α] [has_measurable_smul G₀ α]
  [measurable_singleton_class α] {s : set α} (hs : measurable_set s) (a : G₀) :
  measurable_set (a • s) :=
begin
  rcases eq_or_ne a 0 with (rfl|ha),
  exacts [(subsingleton_zero_smul_set s).measurable_set, hs.const_smul_of_ne_zero ha]
end
