/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.algebra.module.locally_convex
import topology.semicontinuous
import analysis.seminorm

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

variables {𝕜 E : Type*} [semi_normed_ring 𝕜] [add_comm_group E] [has_smul 𝕜 E] [has_smul ℝ E]
  [topological_space E]

lemma lower_semicontinuous.is_barrel_le_one {p : seminorm 𝕜 E} (h : lower_semicontinuous p) :
  is_barrel 𝕜 {x | p x ≤ 1} :=
⟨h.is_closed_le _, _, _, _⟩

end barrel_seminorms
