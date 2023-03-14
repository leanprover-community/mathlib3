/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.constructions.borel_space

/-!
# Measurability of `⌊x⌋` etc

In this file we prove that `int.floor`, `int.ceil`, `int.fract`, `nat.floor`, and `nat.ceil` are
measurable under some assumptions on the (semi)ring.
-/

open set

section floor_ring

variables {α R : Type*} [measurable_space α] [linear_ordered_ring R] [floor_ring R]
  [topological_space R] [order_topology R] [measurable_space R]

lemma int.measurable_floor [opens_measurable_space R] :
  measurable (int.floor : R → ℤ) :=
measurable_to_countable $ λ x, by simpa only [int.preimage_floor_singleton]
  using measurable_set_Ico

@[measurability] lemma measurable.floor [opens_measurable_space R]
  {f : α → R} (hf : measurable f) : measurable (λ x, ⌊f x⌋) :=
int.measurable_floor.comp hf

lemma int.measurable_ceil [opens_measurable_space R] :
  measurable (int.ceil : R → ℤ) :=
measurable_to_countable $ λ x,
  by simpa only [int.preimage_ceil_singleton] using measurable_set_Ioc

@[measurability] lemma measurable.ceil [opens_measurable_space R]
  {f : α → R} (hf : measurable f) : measurable (λ x, ⌈f x⌉) :=
int.measurable_ceil.comp hf

lemma measurable_fract [borel_space R] : measurable (int.fract : R → R) :=
begin
  intros s hs,
  rw int.preimage_fract,
  exact measurable_set.Union (λ z, measurable_id.sub_const _ (hs.inter measurable_set_Ico))
end

@[measurability] lemma measurable.fract [borel_space R]
  {f : α → R} (hf : measurable f) : measurable (λ x, int.fract (f x)) :=
measurable_fract.comp hf

lemma measurable_set.image_fract [borel_space R] {s : set R} (hs : measurable_set s) :
  measurable_set (int.fract '' s) :=
begin
  simp only [int.image_fract, sub_eq_add_neg, image_add_right'],
  exact measurable_set.Union (λ m, (measurable_add_const _ hs).inter measurable_set_Ico)
end

end floor_ring

section floor_semiring

variables {α R : Type*} [measurable_space α] [linear_ordered_semiring R] [floor_semiring R]
  [topological_space R] [order_topology R] [measurable_space R] [opens_measurable_space R]
  {f : α → R}

lemma nat.measurable_floor : measurable (nat.floor : R → ℕ) :=
measurable_to_countable $ λ n, by cases eq_or_ne ⌊n⌋₊ 0; simp [*, nat.preimage_floor_of_ne_zero]

@[measurability] lemma measurable.nat_floor (hf : measurable f) : measurable (λ x, ⌊f x⌋₊) :=
nat.measurable_floor.comp hf

lemma nat.measurable_ceil : measurable (nat.ceil : R → ℕ) :=
measurable_to_countable $ λ n, by cases eq_or_ne ⌈n⌉₊ 0; simp [*, nat.preimage_ceil_of_ne_zero]

@[measurability] lemma measurable.nat_ceil (hf : measurable f) : measurable (λ x, ⌈f x⌉₊) :=
nat.measurable_ceil.comp hf

end floor_semiring
