/-
Copyright (c) 2022 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import topology.homotopy.equiv
import category_theory.equivalence

/-
# Covering spaces

## Main definitions

  - `no_retraction`
  - `brouwer_fixed_point`
-/


section no_retraction

variables {X : Type*} {A : set X} [topological_space X]

def sphere := metric.ball (ℝ × ℝ) 1

variables {h_x_homeo_to_ball : X ≃ₜ sphere} {h_a_homeo_to_boundary : X ≃ₜ frontier sphere}

lemma

end no_retraction


section brouwer_fixed_point

variable (n : ℕ)

end brouwer_fixed_point
