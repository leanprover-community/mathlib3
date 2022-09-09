/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.locally_convex.with_seminorms
import topology.semicontinuous

/-!
# Barrels and barreled spaces

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

def is_barrel (𝕜) {E} [semi_normed_ring 𝕜] [add_comm_monoid E] [has_smul 𝕜 E] [has_smul ℝ E]
  [topological_space E] (S : set E) : Prop :=
is_closed S ∧ convex ℝ S ∧ balanced 𝕜 S ∧ absorbent 𝕜 S

section barrel_seminorms

#check seminorm.balanced_ball_zero
#check seminorm.absorbent_ball_zero
#check convex_on

variables {𝕜 E : Type*} [normed_field 𝕜] [normed_space ℝ 𝕜] [add_comm_group E] [module 𝕜 E]
  [module ℝ E] [is_scalar_tower ℝ 𝕜 E] [topological_space E]

lemma lower_semicontinuous.is_barrel_le_one {p : seminorm 𝕜 E} (h : lower_semicontinuous p) :
  is_barrel 𝕜 {x | p x ≤ 1} :=
⟨h.is_closed_preimage 1, by simpa only [set.sep_univ] using p.convex_on.convex_le 1,
  _,
  p.absorbent_preimage (real.absorbent_Iic zero_lt_one)⟩

end barrel_seminorms
