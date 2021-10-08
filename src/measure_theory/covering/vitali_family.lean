/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import measure_theory.constructions.borel_space

open measure_theory metric set

variables {α : Type*} [metric_space α]

structure is_vitali_family (f : Π (x : α), set (set α)) {m : measurable_space α} (μ : measure α) :=
(center_mem : ∀ (x : α), ∀ (y : set α), y ∈ f x → x ∈ y)
(is_closed : ∀ (x : α), ∀ (y : set α), y ∈ f x → is_closed y)
(nonempty_interior : ∀ (x : α), ∀ (y : set α), y ∈ f x → (interior y).nonempty)
(covering : ∀ (s : set α) (g : Π (x : α), set (set α)),
  measurable_set s → ∀ x, g x ⊆ f x → (∀ (x ∈ s) (ε > (0 : ℝ)), ∃ t ∈ g x, t ⊆ closed_ball x ε)
  → ∃ (t : set α) (u : α → set α), pairwise_on t (disjoint on u) ∧ (∀ x ∈ t, u x ∈ g x)
  ∧ μ (s \ ⋃ x ∈ t, u x) = 0)
