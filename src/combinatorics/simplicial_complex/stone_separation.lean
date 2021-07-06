/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.convex_join

open set

variables {E : Type*} [add_comm_group E] [module ℝ E] {x y : E} {A B : set E} {c : set (set E)}

/-- Stone's Separation Theorem -/
lemma subsets_compl_convexes (hA : convex A) (hB : convex B) (hAB : disjoint A B) :
  ∃ C : set E, convex C ∧ convex Cᶜ ∧ A ⊆ C ∧ B ⊆ Cᶜ :=
begin
  let S : set (set E) := {C | convex C ∧ C ⊆ Bᶜ},
  obtain ⟨C, hC, hAC, hCmax⟩ := zorn.zorn_subset_nonempty S (λ c hcS hc ⟨B, hB⟩, ⟨⋃₀c,
    ⟨(zorn.chain.directed_on hc).convex_sUnion (λ A hA, (hcS hA).1), sUnion_subset
    (λ C hC, (hcS hC).2)⟩, λ s, subset_sUnion_of_mem⟩) A ⟨hA, disjoint_iff_subset_compl_right.1 hAB⟩,
  refine ⟨C, hC.1, _, hAC, subset_compl_comm.1 hC.2⟩,
  rw convex_iff_segment_subset,
  rintro x y hx hy z hz hzC,
  suffices h : ∀ c ∈ Cᶜ, ∃ a ∈ C, (segment c a ∩ B).nonempty,
  { obtain ⟨p, hp, u, huC, huB⟩ := h x hx,
    obtain ⟨q, hq, v, hvC, hvB⟩ := h y hy,
    rw disjoint_iff_subset_compl_left at hAB,
    apply hAB,
    sorry
  },
  rintro c hc,
  by_contra,
  push_neg at h,
  suffices h : convex_hull (insert c C) ⊆ Bᶜ,
  { rw ←hCmax _ ⟨convex_convex_hull _, h⟩ (subset.trans (subset_insert _ _)
      (subset_convex_hull _)) at hc,
    exact hc (subset_convex_hull _ (mem_insert _ _)) },
  rw convex_hull_insert ⟨z, hzC⟩,
  refine bUnion_subset _,
  rintro a ha b hb hbB,
  rw convex.convex_hull_eq hC.1 at ha,
  exact h a ha ⟨b, hb, hbB⟩,
end
