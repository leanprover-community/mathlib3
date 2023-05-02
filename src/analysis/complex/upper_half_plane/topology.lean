/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.upper_half_plane.basic
import analysis.convex.contractible
import analysis.convex.complex
import analysis.complex.re_im_topology
import geometry.manifold.cont_mdiff_mfderiv

/-!
# Topology on the upper half plane

In this file we introduce a `topological_space` structure on the upper half plane and provide
various instances.
-/

noncomputable theory
open set filter function topological_space complex
open_locale filter topology upper_half_plane manifold

namespace upper_half_plane

instance : topological_space ℍ := subtype.topological_space

lemma open_embedding_coe : open_embedding (coe : ℍ → ℂ) :=
is_open.open_embedding_subtype_coe $ is_open_lt continuous_const complex.continuous_im

lemma embedding_coe : embedding (coe : ℍ → ℂ) := embedding_subtype_coe
lemma continuous_coe : continuous (coe : ℍ → ℂ) := embedding_coe.continuous

lemma continuous_re : continuous re := complex.continuous_re.comp continuous_coe
lemma continuous_im : continuous im := complex.continuous_im.comp continuous_coe

instance : topological_space.second_countable_topology ℍ :=
topological_space.subtype.second_countable_topology _ _

instance : t3_space ℍ := subtype.t3_space
instance : normal_space ℍ := normal_space_of_t3_second_countable ℍ

instance : contractible_space ℍ :=
(convex_halfspace_im_gt 0).contractible_space ⟨I, one_pos.trans_eq I_im.symm⟩

instance : loc_path_connected_space ℍ :=
loc_path_connected_of_is_open $ is_open_lt continuous_const complex.continuous_im

instance : noncompact_space ℍ :=
begin
  refine ⟨λ h, _⟩,
  have : is_compact (complex.im ⁻¹' Ioi 0), from is_compact_iff_is_compact_univ.2 h,
  replace := this.is_closed.closure_eq,
  rw [closure_preimage_im, closure_Ioi, set.ext_iff] at this,
  exact absurd ((this 0).1 left_mem_Ici) (lt_irrefl _)
end

instance : locally_compact_space ℍ := open_embedding_coe.locally_compact_space

instance upper_half_plane.charted_space : charted_space ℂ ℍ :=
upper_half_plane.open_embedding_coe.singleton_charted_space

instance upper_half_plane.smooth_manifold_with_corners : smooth_manifold_with_corners 𝓘(ℂ) ℍ :=
upper_half_plane.open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(ℂ)

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
lemma smooth_coe : smooth 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) :=
λ x, cont_mdiff_at_ext_chart_at

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
lemma mdifferentiable_coe : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) :=
smooth_coe.mdifferentiable

end upper_half_plane
