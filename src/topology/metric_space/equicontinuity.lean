/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import topology.metric_space.basic
import topology.uniform_space.equicontinuity
/-!
# Equicontinuity in metric spaces

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

open filter
open_locale topological_space uniformity

variables {α β ι : Type*} [pseudo_metric_space α]

namespace metric

/-- Characterization of equicontinuity for families of functions taking values in a (pseudo) metric
space. -/
lemma equicontinuous_at_iff_right {ι : Type*} [topological_space β] {F : ι → β → α} {x₀ : β} :
  equicontinuous_at F x₀ ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) < ε :=
uniformity_basis_dist.equicontinuous_at_iff_right

/-- Characterization of equicontinuity for families of functions between (pseudo) metric spaces. -/
lemma equicontinuous_at_iff {ι : Type*} [pseudo_metric_space β] {F : ι → β → α} {x₀ : β} :
  equicontinuous_at F x₀ ↔ ∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε :=
nhds_basis_ball.equicontinuous_at_iff uniformity_basis_dist

/-- Reformulation of `equicontinuous_at_iff_pair` for families of functions taking values in a
(pseudo) metric space. -/
protected lemma equicontinuous_at_iff_pair {ι : Type*} [topological_space β] {F : ι → β → α}
  {x₀ : β} :
  equicontinuous_at F x₀ ↔ ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∀ (x x' ∈ U), ∀ i, dist (F i x) (F i x') < ε :=
begin
  rw equicontinuous_at_iff_pair,
  split; intros H,
  { intros ε hε,
    refine exists_imp_exists (λ V, exists_imp_exists $ λ hV h, _) (H _ (dist_mem_uniformity hε)),
    exact λ x hx x' hx', h _ hx _ hx' },
  { intros U hU,
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩,
    refine exists_imp_exists (λ V, exists_imp_exists $ λ hV h, _) (H _ hε),
    exact λ x hx x' hx' i, hεU (h _ hx _ hx' i) }
end

/-- Characterization of uniform equicontinuity for families of functions taking values in a
(pseudo) metric space. -/
lemma uniform_equicontinuous_iff_right {ι : Type*} [uniform_space β] {F : ι → β → α} :
  uniform_equicontinuous F ↔
  ∀ ε > 0, ∀ᶠ (xy : β × β) in 𝓤 β, ∀ i, dist (F i xy.1) (F i xy.2) < ε :=
uniformity_basis_dist.uniform_equicontinuous_iff_right

/-- Characterization of uniform equicontinuity for families of functions between
(pseudo) metric spaces. -/
lemma uniform_equicontinuous_iff {ι : Type*} [pseudo_metric_space β] {F : ι → β → α} :
  uniform_equicontinuous F ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ i, dist (F i x) (F i y) < ε :=
uniformity_basis_dist.uniform_equicontinuous_iff uniformity_basis_dist

section uniform_convergence

local attribute [-instance] Pi.topological_space
local attribute [-instance] Pi.uniform_space
local attribute [instance] uniform_convergence.topological_space

/-- For a family of functions to a (pseudo) metric spaces, a convenient way to prove
equicontinuity at a point is to show that all of the functions share a common *local* continuity
modulus. -/
lemma equicontinuous_at_of_continuity_modulus {ι : Type*} [topological_space β] {x₀ : β}
  (b : β → ℝ)
  (b_lim : tendsto b (𝓝 x₀) (𝓝 0))
  (F : ι → β → α)
  (H : ∀(x:β) i, dist (F i x₀) (F i x) ≤ b x) :
  equicontinuous_at F x₀ :=
begin
  rw metric.equicontinuous_at_iff_right,
  intros ε ε0,
  filter_upwards [b_lim (Iio_mem_nhds ε0)] using λ x hx i, (H x i).trans_lt hx,
end

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
uniform equicontinuity is to show that all of the functions share a common *global* continuity
modulus. -/
lemma uniform_equicontinuous_of_continuity_modulus {ι : Type*} [pseudo_metric_space β] (b : ℝ → ℝ)
  (b_lim : tendsto b (𝓝 0) (𝓝 0))
  (F : ι → β → α)
  (H : ∀(x y:β) i, dist (F i x) (F i y) ≤ b (dist x y)) :
  uniform_equicontinuous F :=
begin
  rw metric.uniform_equicontinuous_iff,
  intros ε ε0,
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩,
  refine ⟨δ, δ0, λ x y hxy i, _⟩,
  calc
    dist (F i x) (F i y) ≤ b (dist x y) : H x y i
    ... ≤ |b (dist x y)| : le_abs_self _
    ... = dist (b (dist x y)) 0 : by simp [real.dist_eq]
    ... < ε : hδ (by simpa only [real.dist_eq, tsub_zero, abs_dist] using hxy)
end

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
equicontinuity is to show that all of the functions share a common *global* continuity modulus. -/
lemma equicontinuous_of_continuity_modulus {ι : Type*} [pseudo_metric_space β] (b : ℝ → ℝ)
  (b_lim : tendsto b (𝓝 0) (𝓝 0))
  (F : ι → β → α)
  (H : ∀(x y:β) i, dist (F i x) (F i y) ≤ b (dist x y)) :
  equicontinuous F :=
(uniform_equicontinuous_of_continuity_modulus b b_lim F H).equicontinuous

end uniform_convergence

end metric
