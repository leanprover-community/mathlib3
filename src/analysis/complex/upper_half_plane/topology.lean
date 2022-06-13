/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.upper_half_plane.basic
import analysis.convex.topology
import analysis.convex.star
import analysis.convex.complex
import analysis.complex.re_im_topology
import topology.homotopy.contractible

/-!
# Topology on the upper half plane
-/

noncomputable theory
open set filter function topological_space complex
open_locale filter topological_space upper_half_plane

section convex

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [has_continuous_add E] [has_continuous_smul ℝ E] {s : set E} {x : E}

protected lemma star_convex.contractible_space (h : star_convex ℝ x s) (hne : s.nonempty) :
  contractible_space s :=
begin
  refine (contractible_iff_id_nullhomotopic _).2 ⟨⟨x, h.mem hne⟩,
    ⟨⟨⟨λ p, ⟨p.1.1 • x + (1 - p.1.1) • p.2, _⟩, _⟩, λ x, _, λ x, _⟩⟩⟩,
  { exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel'_right _ _) },
  { exact continuous_subtype_mk _
      (((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
        ((continuous_const.sub $ continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd))) },
  { ext1, simp },
  { ext1, simp }
end

protected lemma convex.contractible_space (hs : convex ℝ s) (hne : s.nonempty) :
  contractible_space s :=
let ⟨x, hx⟩ := hne in (hs.star_convex hx).contractible_space hne

@[priority 100]
instance real_tvs.contractible_space : contractible_space E :=
(homeomorph.set.univ E).contractible_space_iff.mp $ convex_univ.contractible_space univ_nonempty

end convex

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

instance : regular_space ℍ := subtype.regular_space
instance : normal_space ℍ := normal_space_of_regular_second_countable ℍ

instance : contractible_space ℍ :=
(convex_halfspace_im_gt 0).contractible_space ⟨I, one_pos.trans_eq I_im.symm⟩

instance : loc_path_connected_space ℍ :=
loc_path_connected_of_is_open $ is_open_lt continuous_const complex.continuous_im

instance : noncompact_space ℍ :=
begin
  refine ⟨λ h, _⟩,
  have : is_compact (complex.im ⁻¹' Ioi 0), from is_compact_iff_is_compact_univ.2 h,
  replace := this.is_closed.closure_eq,
  rw [closure_preimage_im, closure_Ioi, im_surjective.preimage_injective.eq_iff] at this,
  exact Ioi_ssubset_Ici_self.ne' this
end

instance : locally_compact_space ℍ := open_embedding_coe.locally_compact_space

end upper_half_plane
