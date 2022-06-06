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

lemma geometrically_obvious {p q u v x y z : E} (hz : z ∈ segment 𝕜 x y) (hu : u ∈ segment 𝕜 x p)
  (hv : v ∈ segment 𝕜 y q) : ¬ disjoint (segment 𝕜 u v) (convex_hull 𝕜 {p, q, z}) :=
begin
  refine not_disjoint_iff.2 _,
  sorry
end

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
  { obtain ⟨p, hp, u, hu, hut⟩ := h x hx,
    obtain ⟨q, hq, v, hv, hvt⟩ := h y hy,
    refine geometrically_obvious hz hu hv ((disjoint_iff_subset_compl_left.2 hC.2).mono _ _),
    exact ht.segment_subset hut hvt,
    refine convex_hull_min _ hC.1,
    simp [insert_subset, hp, hq, singleton_subset_iff.2 hzC] },
  rintro c hc,
  by_contra' h,
  suffices h : convex_hull 𝕜 (insert c C) ⊆ tᶜ,
  { rw ←hCmax _ ⟨convex_convex_hull _ _, h⟩
      ((subset_insert _ _).trans $ subset_convex_hull _ _) at hc,
    exact hc (subset_convex_hull _ _ $ mem_insert _ _) },
  rw [convex_hull_insert ⟨z, hzC⟩, convex_join_singleton_left],
  refine Union₂_subset (λ a ha b hb hbt, h a _ ⟨b, hb, hbt⟩),
  rwa ←hC.1.convex_hull_eq,
end
