/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.emetric_paracompact
import analysis.convex.partition_of_unity

/-!
# Lemmas about (e)metric spaces that need partition of unity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main lemma in this file (see `metric.exists_continuous_real_forall_closed_ball_subset`) says the
following. Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets,
let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, → ℝ)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. We also formulate versions of this lemma for extended metric
spaces and for different codomains (`ℝ`, `ℝ≥0`, and `ℝ≥0∞`).

We also prove a few auxiliary lemmas to be used later in a proof of the smooth version of this
lemma.

## Tags

metric space, partition of unity, locally finite
-/

open_locale topology ennreal big_operators nnreal filter
open set function filter topological_space

variables {ι X : Type*}

namespace emetric

variables [emetric_space X] {K : ι → set X} {U : ι → set X}

/-- Let `K : ι → set X` be a locally finitie family of closed sets in an emetric space. Let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then for any point
`x : X`, for sufficiently small `r : ℝ≥0∞` and for `y` sufficiently close to `x`, for all `i`, if
`y ∈ K i`, then `emetric.closed_ball y r ⊆ U i`. -/
lemma eventually_nhds_zero_forall_closed_ball_subset (hK : ∀ i, is_closed (K i))
  (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) (x : X) :
  ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ᶠ 𝓝 x, ∀ i, p.2 ∈ K i → closed_ball p.2 p.1 ⊆ U i :=
begin
  suffices : ∀ i, x ∈ K i → ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ᶠ 𝓝 x, closed_ball p.2 p.1 ⊆ U i,
  { filter_upwards [tendsto_snd (hfin.Inter_compl_mem_nhds hK x),
      (eventually_all_finite (hfin.point_finite x)).2 this],
    rintro ⟨r, y⟩ hxy hyU i hi,
    simp only [mem_Inter₂, mem_compl_iff, not_imp_not, mem_preimage] at hxy,
    exact hyU _ (hxy _ hi) },
  intros i hi,
  rcases nhds_basis_closed_eball.mem_iff.1 ((hU i).mem_nhds $ hKU i hi) with ⟨R, hR₀, hR⟩,
  rcases ennreal.lt_iff_exists_nnreal_btwn.mp hR₀ with ⟨r, hr₀, hrR⟩,
  filter_upwards [prod_mem_prod (eventually_lt_nhds hr₀)
    (closed_ball_mem_nhds x (tsub_pos_iff_lt.2 hrR))] with p hp z hz,
  apply hR,
  calc edist z x ≤ edist z p.2 + edist p.2 x : edist_triangle _ _ _
  ... ≤ p.1 + (R - p.1) : add_le_add hz $ le_trans hp.2 $ tsub_le_tsub_left hp.1.out.le _
  ... = R : add_tsub_cancel_of_le (lt_trans hp.1 hrR).le,
end

lemma exists_forall_closed_ball_subset_aux₁ (hK : ∀ i, is_closed (K i))
  (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) (x : X) :
  ∃ r : ℝ, ∀ᶠ y in 𝓝 x, r ∈ Ioi (0 : ℝ) ∩
    ennreal.of_real ⁻¹' ⋂ i (hi : y ∈ K i), {r | closed_ball y r ⊆ U i} :=
begin
  have := (ennreal.continuous_of_real.tendsto' 0 0 ennreal.of_real_zero).eventually
    (eventually_nhds_zero_forall_closed_ball_subset hK hU hKU hfin x).curry,
  rcases this.exists_gt with ⟨r, hr0, hr⟩,
  refine ⟨r, hr.mono (λ y hy, ⟨hr0, _⟩)⟩,
  rwa [mem_preimage, mem_Inter₂]
end

lemma exists_forall_closed_ball_subset_aux₂ (y : X) :
  convex ℝ (Ioi (0 : ℝ) ∩ ennreal.of_real ⁻¹' ⋂ i (hi : y ∈ K i), {r | closed_ball y r ⊆ U i}) :=
(convex_Ioi _).inter $ ord_connected.convex $ ord_connected.preimage_ennreal_of_real $
  ord_connected_Inter $ λ i, ord_connected_Inter $
    λ hi, ord_connected_set_of_closed_ball_subset y (U i)

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (ennreal.of_real (δ x)) ⊆ U i`. -/
lemma exists_continuous_real_forall_closed_ball_subset (hK : ∀ i, is_closed (K i))
  (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) :
  ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), closed_ball x (ennreal.of_real $ δ x) ⊆ U i :=
by simpa only [mem_inter_iff, forall_and_distrib, mem_preimage, mem_Inter, @forall_swap ι X]
  using exists_continuous_forall_mem_convex_of_local_const exists_forall_closed_ball_subset_aux₂
    (exists_forall_closed_ball_subset_aux₁ hK hU hKU hfin)

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
lemma exists_continuous_nnreal_forall_closed_ball_subset (hK : ∀ i, is_closed (K i))
  (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) :
  ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), closed_ball x (δ x) ⊆ U i :=
begin
  rcases exists_continuous_real_forall_closed_ball_subset hK hU hKU hfin with ⟨δ, hδ₀, hδ⟩,
  lift δ to C(X, ℝ≥0) using λ x, (hδ₀ x).le,
  refine ⟨δ, hδ₀, λ i x hi, _⟩,
  simpa only [← ennreal.of_real_coe_nnreal] using hδ i x hi
end

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0∞)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
lemma exists_continuous_ennreal_forall_closed_ball_subset (hK : ∀ i, is_closed (K i))
  (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) :
  ∃ δ : C(X, ℝ≥0∞), (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), closed_ball x (δ x) ⊆ U i :=
let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nnreal_forall_closed_ball_subset hK hU hKU hfin
in ⟨continuous_map.comp ⟨coe, ennreal.continuous_coe⟩ δ, λ x, ennreal.coe_pos.2 (hδ₀ x), hδ⟩

end emetric

namespace metric

variables [metric_space X] {K : ι → set X} {U : ι → set X}

/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
lemma exists_continuous_nnreal_forall_closed_ball_subset (hK : ∀ i, is_closed (K i))
  (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) :
  ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), closed_ball x (δ x) ⊆ U i :=
begin
  rcases emetric.exists_continuous_nnreal_forall_closed_ball_subset hK hU hKU hfin
    with ⟨δ, hδ0, hδ⟩,
  refine ⟨δ, hδ0, λ i x hx, _⟩,
  rw [← emetric_closed_ball_nnreal],
  exact hδ i x hx
end

/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
lemma exists_continuous_real_forall_closed_ball_subset (hK : ∀ i, is_closed (K i))
  (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) :
  ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), closed_ball x (δ x) ⊆ U i :=
let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nnreal_forall_closed_ball_subset hK hU hKU hfin
in ⟨continuous_map.comp ⟨coe, nnreal.continuous_coe⟩ δ, hδ₀, hδ⟩

end metric
