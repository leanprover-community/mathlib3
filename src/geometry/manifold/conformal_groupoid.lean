/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.calculus.conformal.normed_space
import geometry.manifold.charted_space

/-!
# Conformal Groupoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the groupoid of conformal maps on normed spaces.

## Main definitions

* `conformal_groupoid`: the groupoid of conformal local homeomorphisms.

## Tags

conformal, groupoid
-/

variables {X : Type*} [normed_add_comm_group X] [normed_space ℝ X]

/-- The pregroupoid of conformal maps. -/
def conformal_pregroupoid : pregroupoid X :=
{ property := λ f u, ∀ x, x ∈ u → conformal_at f x,
  comp := λ f g u v hf hg hu hv huv x hx, (hg (f x) hx.2).comp x (hf x hx.1),
  id_mem := λ x hx, conformal_at_id x,
  locality := λ f u hu h x hx, let ⟨v, h₁, h₂, h₃⟩ := h x hx in h₃ x ⟨hx, h₂⟩,
  congr := λ f g u hu h hf x hx, (hf x hx).congr hx hu h, }

/-- The groupoid of conformal maps. -/
def conformal_groupoid : structure_groupoid X := conformal_pregroupoid.groupoid
