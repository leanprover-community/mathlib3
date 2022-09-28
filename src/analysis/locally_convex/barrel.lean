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

open_locale topological_space

def is_barrel (𝕜) {E} [semi_normed_ring 𝕜] [add_comm_monoid E] [has_smul 𝕜 E] [has_smul ℝ E]
  [topological_space E] (S : set E) : Prop :=
is_closed S ∧ convex ℝ S ∧ balanced 𝕜 S ∧ absorbent 𝕜 S

lemma lower_semicontinuous.is_barrel_closed_ball {𝕜 E : Type*} [normed_field 𝕜] [normed_space ℝ 𝕜]
  [add_comm_group E] [module 𝕜 E] [module ℝ E] [is_scalar_tower ℝ 𝕜 E] [topological_space E]
  {p : seminorm 𝕜 E} (h : lower_semicontinuous p) :
  is_barrel 𝕜 (p.closed_ball 0 1) :=
⟨by rw p.closed_ball_zero_eq; exact h.is_closed_preimage 1,
  p.convex_closed_ball _ _,
  p.balanced_closed_ball_zero 1,
  p.absorbent_closed_ball_zero zero_lt_one⟩

class barreled_space (𝕜) (E) [semi_normed_ring 𝕜] [add_comm_monoid E] [has_smul 𝕜 E] [has_smul ℝ E]
  [topological_space E] : Prop :=
(barrel_mem_nhds : ∀ s : set E, is_barrel 𝕜 s → s ∈ 𝓝 (0 : E))

lemma is_barrel.mem_nhds {𝕜 E} [semi_normed_ring 𝕜] [add_comm_monoid E] [has_smul 𝕜 E]
  [has_smul ℝ E] [topological_space E] [barreled_space 𝕜 E] {s : set E} (hs : is_barrel 𝕜 s) :
  s ∈ 𝓝 (0 : E) :=
barreled_space.barrel_mem_nhds s hs

lemma seminorm.continuous_of_lower_semicontinuous {𝕜 E} [semi_normed_ring 𝕜] [add_comm_group E]
  [has_smul 𝕜 E] [has_smul ℝ E] [topological_space E] [barreled_space 𝕜 E] {p : seminorm 𝕜 E}
  (h : lower_semicontinuous p) : continuous p :=
sorry

#lint
#check seminorm.closed_ball_zero'

lemma is_barrel.eq_closed_ball {𝕜 E : Type*} [normed_field 𝕜] [normed_space ℝ 𝕜]
  [add_comm_group E] [module 𝕜 E] [module ℝ E] [is_scalar_tower ℝ 𝕜 E] [topological_space E]
  {s : set E} (hs : is_barrel 𝕜 s) :
  ∃ p : seminorm 𝕜 E, lower_semicontinuous p ∧ s = p.closed_ball 0 1 :=
begin
  let ι := {u : E →L[𝕜] 𝕜 // ∀ x ∈ s, ∥u x∥ ≤ 1},
  haveI : nonempty ι := ⟨⟨0, λ x hx, by simp⟩⟩,
  let p : seminorm 𝕜 E := ⨆ u : ι, (norm_seminorm 𝕜 𝕜).comp u,
  have : (p : E → ℝ) = ⨆ u : ι, norm ∘ u,
  { sorry }, --should be easy
  use p,
  split,
  { rw this,
    --refine lower_semicontinuous_supr _,
    sorry },
  { refine subset_antisymm (λ x hx, p.mem_closed_ball_zero.mpr _) _,
    { rw [this, supr_apply],
      exact csupr_le (λ u, u.2 x hx) },
    { refine λ x, not_imp_not.mp (λ hx, _),
      --hard part
      sorry } }
end
