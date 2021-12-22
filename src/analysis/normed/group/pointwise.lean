/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.normed.group.basic

/-!
# Properties of pointwise addition of sets in normed groups.

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

open metric set
open_locale pointwise topological_space

section semi_normed_group

variables {E : Type*} [semi_normed_group E]

lemma bounded_iff_exists_norm_le {s : set E} :
  bounded s ↔ ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
by simp [subset_def, bounded_iff_subset_ball (0 : E)]

lemma metric.bounded.add
  {s t : set E} (hs : bounded s) (ht : bounded t) :
  bounded (s + t) :=
begin
  obtain ⟨Rs, hRs⟩ : ∃ (R : ℝ), s ⊆ closed_ball 0 R := hs.subset_ball 0,
  obtain ⟨Rt, hRt⟩ : ∃ (R : ℝ), t ⊆ closed_ball 0 R := ht.subset_ball 0,
  refine (bounded_iff_exists_norm_le).2 ⟨Rs + Rt, _⟩,
  rintros z ⟨x, y, hx, hy, rfl⟩,
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ : norm_add_le _ _
  ... ≤ Rs + Rt :
    add_le_add (mem_closed_ball_zero_iff.1 (hRs hx)) (mem_closed_ball_zero_iff.1 (hRt hy))
end

@[simp] lemma singleton_add_ball (x y : E) (r : ℝ) :
  {x} + ball y r = ball (x + y) r :=
by simp only [preimage_add_ball, image_add_left, singleton_add, sub_neg_eq_add, add_comm y x]

@[simp] lemma ball_add_singleton (x y : E) (r : ℝ) :
  ball x r + {y} = ball (x + y) r :=
by simp [add_comm _ {y}, add_comm y]

lemma singleton_add_ball_zero (x : E) (r : ℝ) :
  {x} + ball 0 r = ball x r :=
by simp

lemma ball_zero_add_singleton (x : E) (r : ℝ) :
  ball 0 r + {x} = ball x r :=
by simp

@[simp] lemma singleton_add_closed_ball (x y : E) (r : ℝ) :
  {x} + closed_ball y r = closed_ball (x + y) r :=
by simp only [add_comm y x, preimage_add_closed_ball, image_add_left, singleton_add, sub_neg_eq_add]

@[simp] lemma closed_ball_add_singleton (x y : E) (r : ℝ) :
  closed_ball x r + {y} = closed_ball (x + y) r :=
by simp [add_comm _ {y}, add_comm y]

lemma singleton_add_closed_ball_zero (x : E) (r : ℝ) :
  {x} + closed_ball 0 r = closed_ball x r :=
by simp

lemma closed_ball_zero_add_singleton (x : E) (r : ℝ) :
  closed_ball 0 r + {x} = closed_ball x r :=
by simp

end semi_normed_group
