/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.complex.abs_max
import geometry.manifold.mfderiv

/-! # Holomorphic functions on complex manifolds

Thanks to the rigidity of complex-differentiability compared to real-differentiability, there are
many results about complex manifolds with no analogue for manifolds a general normed field.  For
now, this file contains just one such result:

## Main results

* `mdifferentiable.const_of_compact_space_of_connected_space`: A complex-differentiable function on
  a compact preconnected complex manifold is constant.

## TODO

There is a whole theory to develop here, but an obvious next step would be to generalize the above
result to possibly disconnected compact complex manifolds, where the result should be that a
complex-differentiable function is `is_locally_constant`.  There are some gaps in the
`is_locally_constant` API that need to be filled for this.
-/

open_locale manifold topological_space
open complex

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E]
variables {F : Type*} [normed_add_comm_group F] [normed_space ℂ F] [strict_convex_space ℝ F]

variables {M : Type*} [topological_space M] [charted_space E M]
  [smooth_manifold_with_corners 𝓘(ℂ, E) M]

/-- A holomorphic function on a complex manifold is constant on every compact, preconnected, clopen
subset. -/
lemma mdifferentiable.const_of_is_preconnected {s : set M} (hs₁ : is_compact s)
  (hs₂ : is_preconnected s) (hs₃ : is_clopen s)
  {f : M → F} (hf : mdifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) {a b : M} (ha : a ∈ s) (hb : b ∈ s) :
  f a = f b :=
begin
  -- for an empty set this fact is trivial
  rcases s.eq_empty_or_nonempty with rfl | hs',
  { exact false.rec _ ha },
  -- otherwise, let `p₀` be a point where the value of `f` has maximal norm
  obtain ⟨p₀, hp₀s, hp₀⟩ := hs₁.exists_forall_ge hs' hf.continuous.norm.continuous_on,
  -- we will show `f` agrees everywhere with `f p₀`
  suffices : s ⊆ {r : M | f r = f p₀} ∩ s,
  { exact (this ha).1.trans (this hb).1.symm }, clear ha hb a b,
  refine hs₂.subset_clopen _ ⟨p₀, hp₀s, ⟨rfl, hp₀s⟩⟩,
  -- closedness of the set of points sent to `f p₀`
  refine ⟨_, (is_closed_singleton.preimage hf.continuous).inter hs₃.2⟩,
  -- we will show this set is open by showing it is a neighbourhood of each of its members
  rw is_open_iff_mem_nhds,
  rintros p ⟨hp : f p = _, hps⟩, -- let `p` be  in this set
  have hps' : s ∈ 𝓝 p := hs₃.1.mem_nhds hps,
  have key₁ : (chart_at E p).symm ⁻¹' s ∈ 𝓝 (chart_at E p p),
  { rw [← filter.mem_map, (chart_at E p).symm_map_nhds_eq (mem_chart_source E p)],
    exact hps' },
  have key₂ : (chart_at E p).target ∈ 𝓝 (chart_at E p p) :=
    (local_homeomorph.open_target _).mem_nhds (mem_chart_target E p),
  -- `f` pulled back by the chart at `p` is differentiable around `chart_at E p p`
  have hf' : ∀ᶠ (z : E) in 𝓝 (chart_at E p p), differentiable_at ℂ (f ∘ (chart_at E p).symm) z,
  { apply filter.eventually_of_mem key₂,
    intros z hz,
    have H₁ : (chart_at E p).symm z ∈ (chart_at E p).source := (chart_at E p).map_target hz,
    have H₂ : f ((chart_at E p).symm z) ∈ (chart_at F (0:F)).source := trivial,
    have H := hf ((chart_at E p).symm z),
    rw mdifferentiable_at_iff_of_mem_source H₁ H₂ at H,
    simp only [differentiable_within_at_univ] with mfld_simps at H,
    simpa [local_homeomorph.right_inv _ hz] using H.2,
    apply_instance,
    apply_instance },
  -- `f` pulled back by the chart at `p` has a local max at `chart_at E p p`
  have hf'' : is_local_max (norm ∘ f ∘ (chart_at E p).symm) (chart_at E p p),
  { apply filter.eventually_of_mem key₁,
    intros z hz,
    refine (hp₀ ((chart_at E p).symm z) hz).trans (_ : ∥f p₀∥ ≤ ∥f _∥),
    rw [← hp, local_homeomorph.left_inv _ (mem_chart_source E p)] },
  -- so by the maximum principle `f` is equal to `f p` near `p`
  obtain ⟨U, hU, hUf⟩ := (complex.eventually_eq_of_is_local_max_norm hf' hf'').exists_mem,
  have H₁ : (chart_at E p) ⁻¹' U ∈ 𝓝 p := (chart_at E p).continuous_at (mem_chart_source E p) hU,
  have H₂ : (chart_at E p).source ∈ 𝓝 p :=
    (local_homeomorph.open_source _).mem_nhds (mem_chart_source E p),
  apply filter.mem_of_superset (filter.inter_mem hps' (filter.inter_mem H₁ H₂)),
  rintros q ⟨hqs, hq : chart_at E p q ∈ _, hq'⟩,
  refine ⟨_, hqs⟩,
  simpa [local_homeomorph.left_inv _ hq', hp, -norm_eq_abs] using hUf (chart_at E p q) hq,
end

/-- A holomorphic function on a compact connected complex manifold is constant. -/
lemma mdifferentiable.const_of_compact_space_of_preconnected_space [compact_space M]
  [preconnected_space M] {f : M → F} (hf : mdifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (a b : M) :
  f a = f b :=
hf.const_of_is_preconnected compact_univ is_preconnected_univ is_clopen_univ (set.mem_univ _)
  (set.mem_univ _)
