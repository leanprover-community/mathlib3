/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.normed_space.conformal
import geometry.manifold.charted_space

/-!
## Conformal Groupoid

In this file we define the groupoid of conformal maps on normed spaces.

# Main results

* `conformal_groupoid`: the groupoid of conformal local homeomorphisms.

# Tags

conformal, groupoid
-/

variables {X : Type*} [normed_group X] [normed_space ℝ X]

/-- The pregroupoid of conformal maps. -/
def conformal_pregroupoid : pregroupoid X :=
{ property := λ f u, conformal_on f u,
  comp := λ f g u v hf hg hu hv huv, hf.comp hg,
  id_mem := conformal.conformal_on conformal_id,
  locality := λ f u hu h x hx, let ⟨v, h₁, h₂, h₃⟩ := h x hx in h₃ x ⟨hx, h₂⟩,
  congr := λ f g u hu h hf, conformal_on.congr hu h hf, }

/-- The groupoid of conformal maps. -/
def conformal_groupoid : structure_groupoid X := conformal_pregroupoid.groupoid
