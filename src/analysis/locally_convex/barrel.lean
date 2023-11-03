/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.locally_convex.with_seminorms
import analysis.normed_space.hahn_banach.separation
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

section basic

variables {𝕜 E : Type*} [semi_normed_ring 𝕜] [add_comm_monoid E] [has_smul 𝕜 E] [has_smul ℝ E]
  [topological_space E] {S : set E} (hS : is_barrel 𝕜 S)

lemma is_barrel.is_closed : is_closed S := hS.1
lemma is_barrel.convex : convex ℝ S := hS.2.1
lemma is_barrel.balanced : balanced 𝕜 S := hS.2.2.1
lemma is_barrel.absorbent : absorbent 𝕜 S := hS.2.2.2

end basic

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

lemma seminorm.continuous_of_lower_semicontinuous {𝕜 E} [nontrivially_normed_field 𝕜]
  [normed_algebra ℝ 𝕜] [add_comm_group E] [module 𝕜 E] [module ℝ E] [is_scalar_tower ℝ 𝕜 E]
  [topological_space E] [topological_add_group E] [has_continuous_const_smul 𝕜 E]
  [barreled_space 𝕜 E] {p : seminorm 𝕜 E} (h : lower_semicontinuous p) : continuous p :=
seminorm.continuous' (h.is_barrel_closed_ball).mem_nhds

lemma is_barrel.eq_closed_ball {E} [add_comm_group E] [module ℝ E] [topological_space E]
  [topological_add_group E] [has_continuous_smul ℝ E] [locally_convex_space ℝ E] {s : set E}
  (hs : is_barrel ℝ s) :
  ∃ p : seminorm ℝ E, lower_semicontinuous p ∧ s = p.closed_ball 0 1 :=
begin
  let ι := {u : E →L[ℝ] ℝ // ∀ x ∈ s, ‖u x‖ ≤ 1},
  haveI : nonempty ι :=
    ⟨⟨0, λ x hx, by simp only [continuous_linear_map.zero_apply, norm_zero, zero_le_one]⟩⟩,
  let p : seminorm ℝ E := ⨆ u : ι, (norm_seminorm ℝ ℝ).comp (u : E →ₗ[ℝ] ℝ),
  have p_def : (p : E → ℝ) = ⨆ u : ι, norm ∘ u,
  { sorry }, --should be easy
  use p,
  split,
  { rw p_def,
    --refine lower_semicontinuous_supr _,
    sorry },
  { refine subset_antisymm (λ x hx, p.mem_closed_ball_zero.mpr _) _,
    { rw [p_def, supr_apply],
      exact csupr_le (λ u, u.2 x hx) },
    { refine λ x, not_imp_not.mp (λ hx, _),
      -- TODO : version where we get one directly
      rcases geometric_hahn_banach_closed_point hs.convex hs.is_closed hx with ⟨f, r, hfs, hfx⟩,
      have : 0 < r,
      { specialize hfs 0 (hs.absorbent.zero_mem),
        rwa map_zero at hfs },
      have : ∀ y ∈ s, ‖(r⁻¹ • f) y‖ < 1,
      { intros y hys,
        rw [continuous_linear_map.smul_apply, norm_smul, norm_inv, real.norm_of_nonneg this.le,
            inv_mul_lt_iff this, mul_one, real.norm_eq_abs, abs_lt', ← map_neg],
        exact ⟨hfs y hys, hfs (-y) (hs.balanced.neg_mem_iff.mpr hys)⟩ },
      let u : ι := ⟨r⁻¹ • f, λ y hys, (this y hys).le⟩,
      rw [seminorm.mem_closed_ball_zero, not_le, p_def, supr_apply],
      sorry } }
end
