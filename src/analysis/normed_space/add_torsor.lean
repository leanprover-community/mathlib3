/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.add_torsor
import analysis.normed_space.basic

noncomputable theory

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.

-/

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A `normed_add_torsor V P` is a torsor of an additive normed group
action by a `normed_group V` on points `P`. We bundle the metric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a metric space, but
bundling just the distance and using an instance for the metric space
results in type class problems). -/
class normed_add_torsor (V : Type*) (P : Type*) [normed_group V] [metric_space P]
  extends add_torsor V P :=
(norm_dist' : ∀ (x y : P), dist x y = ∥(x -ᵥ y : V)∥)
end prio

/-- The distance equals the norm of subtracting two points. This lemma
is needed to make V an explicit rather than implicit argument. -/
lemma norm_dist (V : Type*) {P : Type*} [normed_group V] [metric_space P] [normed_add_torsor V P]
    (x y : P) :
  dist x y = ∥(x -ᵥ y : V)∥ :=
normed_add_torsor.norm_dist' x y
