/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.continuous_on

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuous_within_at_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuous_within_at_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuous_at_iff_continuous_left_right`, `continuous_at_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

We also define the (strict) left and right limits of a function and prove some properties:
* `left_lim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `right_lim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).
* `monotone.left_lim_eq_right_lim_iff_continuous_at` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `monotone.countable_not_continuous_at` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

## Tags

left continuous, right continuous
-/

open set filter
open_locale topological_space

section partial_order

variables {α β : Type*} [topological_space α] [partial_order α] [topological_space β]

lemma continuous_within_at_Ioi_iff_Ici {a : α} {f : α → β} :
  continuous_within_at f (Ioi a) a ↔ continuous_within_at f (Ici a) a :=
by simp only [← Ici_diff_left, continuous_within_at_diff_self]

lemma continuous_within_at_Iio_iff_Iic {a : α} {f : α → β} :
  continuous_within_at f (Iio a) a ↔ continuous_within_at f (Iic a) a :=
@continuous_within_at_Ioi_iff_Ici αᵒᵈ _ ‹topological_space α› _ _ _ f

lemma nhds_left'_le_nhds_ne (a : α) :
  𝓝[<] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_lt hy)

lemma nhds_right'_le_nhds_ne (a : α) :
  𝓝[>] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_gt hy)

end partial_order

section topological_space

variables {α β : Type*} [topological_space α] [linear_order α] [topological_space β]

lemma nhds_left'_le_nhds_ne (a : α) :
  𝓝[<] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_lt hy)

lemma nhds_right'_le_nhds_ne (a : α) :
  𝓝[>] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_gt hy)

lemma nhds_left_sup_nhds_right (a : α) :
  𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a :=
by rw [← nhds_within_union, Iic_union_Ici, nhds_within_univ]

lemma nhds_left'_sup_nhds_right (a : α) :
  𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a :=
by rw [← nhds_within_union, Iio_union_Ici, nhds_within_univ]

lemma nhds_left_sup_nhds_right' (a : α) :
  𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a :=
by rw [← nhds_within_union, Iic_union_Ioi, nhds_within_univ]

lemma nhds_left'_sup_nhds_right' (a : α) :
  𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a :=
by rw [← nhds_within_union, Iio_union_Ioi]

lemma continuous_at_iff_continuous_left_right {a : α} {f : α → β} :
  continuous_at f a ↔ continuous_within_at f (Iic a) a ∧ continuous_within_at f (Ici a) a :=
by simp only [continuous_within_at, continuous_at, ← tendsto_sup, nhds_left_sup_nhds_right]

lemma continuous_at_iff_continuous_left'_right' {a : α} {f : α → β} :
  continuous_at f a ↔ continuous_within_at f (Iio a) a ∧ continuous_within_at f (Ioi a) a :=
by rw [continuous_within_at_Ioi_iff_Ici, continuous_within_at_Iio_iff_Iic,
  continuous_at_iff_continuous_left_right]

end topological_space
