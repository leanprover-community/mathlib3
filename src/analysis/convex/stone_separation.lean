/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.join

/-!
# Stone's separation theorem
-/

open set

variables {𝕜 E ι : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {x y : E}
  {s t : set E}

/-- **Stone's Separation Theorem** -/
lemma exists_convex_convex_compl_subset (hs : convex 𝕜 s) (ht : convex 𝕜 t) (hst : disjoint s t) :
  ∃ C : set E, convex 𝕜 C ∧ convex 𝕜 Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ :=
begin
  let S : set (set E) := {C | convex 𝕜 C ∧ C ⊆ tᶜ},
  obtain ⟨C, hC, hsC, hCmax⟩ := zorn_subset_nonempty S
    (λ c hcS hc ⟨t, ht⟩, ⟨⋃₀ c, ⟨hc.directed_on.convex_sUnion (λ s hs, (hcS hs).1),
    sUnion_subset (λ C hC, (hcS hC).2)⟩, λ s, subset_sUnion_of_mem⟩) s
    ⟨hs, disjoint_iff_subset_compl_right.1 hst⟩,
  refine ⟨C, hC.1, convex_iff_segment_subset.2 $ λ x y hx hy z hz hzC, _, hsC,
    subset_compl_comm.1 hC.2⟩,
  suffices h : ∀ c ∈ Cᶜ, ∃ a ∈ C, (segment 𝕜 c a ∩ t).nonempty,
  { obtain ⟨p, hp, u, huC, hut⟩ := h x hx,
    obtain ⟨q, hq, v, hvC, hvt⟩ := h y hy,
    rw disjoint_iff_subset_compl_left at hst,
    -- apply hst,
    sorry
  },
  rintro c hc,
  by_contra,
  push_neg at h,
  suffices h : convex_hull 𝕜 (insert c C) ⊆ tᶜ,
  { rw ←hCmax _ ⟨convex_convex_hull _ _, h⟩
     ((subset_insert _ _).trans $ subset_convex_hull _ _) at hc,
    exact hc (subset_convex_hull _ _ $ mem_insert _ _) },
  rw convex_hull_insert ⟨z, hzC⟩,
  refine Union₂_subset (λ a ha b hb hbt, _),
  rw hC.1.convex_hull_eq at ha,
  exact h a ha ⟨b, hb, hbt⟩,
end
