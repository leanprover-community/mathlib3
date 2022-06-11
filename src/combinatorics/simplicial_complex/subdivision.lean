/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.specific_limits.basic
import combinatorics.simplicial_complex.basic

/-!
# Subdivision of simplicial complexes
-/

open geometry finset set

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {m : ℕ}
  {K K₁ K₂ K₃ : simplicial_complex 𝕜 E}

/-- `K₁` is a subdivision of `K₂` iff their underlying space is the same and each face of `K₁` is
contained in some face of `K₂`. -/
def subdivides (K₁ K₂ : simplicial_complex 𝕜 E) : Prop :=
K₁.space = K₂.space ∧
  ∀ ⦃s₁⦄, s₁ ∈ K₁ → ∃ s₂ ∈ K₂, convex_hull 𝕜 (s₁ : set E) ⊆ convex_hull 𝕜 (s₂ : set E)

@[refl] lemma subdivides.refl (K : simplicial_complex 𝕜 E) : K.subdivides K :=
⟨rfl, λ s hs, ⟨s, hs, subset.rfl⟩⟩

lemma subdivides.rfl : K.subdivides K := subdivides.refl _

@[trans] lemma subdivides.trans (h₁₂ : K₁.subdivides K₂) (h₂₃ : K₂.subdivides K₃) :
  K₁.subdivides K₃ :=
⟨h₁₂.1.trans h₂₃.1, λ s₁ hs₁, let ⟨s₂, hs₂, hs₁₂⟩ := h₁₂.2 hs₁, ⟨s₃, hs₃, hs₂₃⟩ := h₂₃.2 hs₂ in
  ⟨s₃, hs₃, hs₁₂.trans hs₂₃⟩⟩

end ordered_ring

section semi_normed_group
variables [semi_normed_group E] [t2_space E] [normed_space ℝ E] {s t : finset E} {m : ℕ}
  {K₁ K₂ : simplicial_complex ℝ E}

lemma subdivides_iff_combi_interiors_subset_combi_interiors :
  K₁.subdivides K₂ ↔ K₂.space ⊆ K₁.space ∧
  ∀ s₁ ∈ K₁, ∃ s₂ ∈ K₂, combi_interior ℝ s₁ ⊆ combi_interior ℝ s₂ :=
begin
  refine ⟨λ h, ⟨h.1.symm.subset, λ s hs, _⟩, λ h, ⟨h.1.antisymm' $ λ x hx, _, λ s₁ hs₁, _⟩⟩,
  { obtain ⟨t, ht, hst⟩ := h.2 hs,
    obtain ⟨u, hut, hu, hsu⟩ := simplex_combi_interiors_split_interiors_nonempty (K₁.nonempty hs)
      (K₂.indep ht) hst,
    exact ⟨u, K₂.down_closed ht hut hu, hsu⟩ },
  { obtain ⟨s₁, hs₁, hx⟩ := mem_space_iff.1 hx,
    obtain ⟨s₂, hs₂, hs₁s₂⟩ := h.2 _ hs₁,
    rw mem_space_iff,
    exact ⟨s₂, hs₂, convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior
      (K₁.indep hs₁) (K₂.indep hs₂) hs₁s₂ hx⟩ },
  { obtain ⟨s₂, hs₂, hs₁s₂⟩ := h.2 _ hs₁,
    exact ⟨_, hs₂, convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior
      (K₁.indep hs₁) (K₂.indep hs₂) hs₁s₂⟩ }
end

lemma subdivides_iff_partition :
  K₁.subdivides K₂ ↔ (K₁.faces.nonempty → K₂.faces.nonempty) ∧ K₁.space ⊆ K₂.space ∧
    ∀ s₂ ∈ K₂, ∃ F ⊆ K₁.faces, combi_interior ℝ s₂ = ⋃ (s₁ ∈ F), combi_interior ℝ s₁ :=
begin
  split,
  { rintro ⟨hspace, hsubdiv⟩,
    refine ⟨_, hspace.le, λ s hs, _⟩,
    { rintro ⟨s₁, hs₁⟩,
      obtain ⟨s₂, hs₂, hs₁s₂⟩ := hsubdiv hs₁,
      exact ⟨s₂, hs₂⟩ },
    refine ⟨{t | t ∈ K₁ ∧ combi_interior ℝ t ⊆ combi_interior ℝ s}, (λ t ht, ht.1), _⟩,
    ext x,
    refine ⟨λ hxs, _, _⟩,
    { have hxspace := mem_space_iff.2 ⟨s, hs, hxs.1⟩,
      rw [←hspace, ←combi_interiors_cover, mem_Union₂] at hxspace,
      obtain ⟨t, ht, hxt⟩ := hxspace,
      refine mem_Union₂_of_mem ⟨ht, λ y hyt, _⟩ hxt,
      obtain ⟨u, hu, htu⟩ := hsubdiv ht,
      obtain ⟨W, hWu, htW⟩ := simplex_combi_interiors_split_interiors (K₂.indep hu) htu,
      rw disjoint_interiors hs (K₂.down_closed hu hWu _) hxs (htW hxt),
      exact htW hyt,
      sorry },
    { rw mem_Union₂,
      rintro ⟨t, ⟨ht, hts⟩, hxt⟩,
      exact hts hxt } },
  { rintro ⟨hempty, hspace, hpartition⟩,
    have hspace : K₁.space = K₂.space,
    { refine hspace.antisymm (λ x hx, _),
      rw [←combi_interiors_cover, mem_Union₂] at ⊢ hx,
      obtain ⟨s, hs, hxs⟩ := hx,
      obtain ⟨F, hF, hsint⟩ := hpartition _ hs,
      rw [hsint, mem_Union₂] at hxs,
      obtain ⟨t, ht, hxt⟩ := hxs,
      exact ⟨t, hF ht, hxt⟩ },
    refine ⟨hspace, λ s hs, _⟩,
    obtain rfl | hsnonempty := s.eq_empty_or_nonempty,
    { obtain ⟨t, ht⟩ := hempty ⟨_, hs⟩,
      exact ⟨t, ht, by simp⟩ },
    obtain ⟨x, hx⟩ := hsnonempty.combi_interior (K₁.indep hs),
    have hxspace := mem_space_iff.2 ⟨s, hs, hx.1⟩,
    rw [hspace, ←combi_interiors_cover, mem_Union₂] at hxspace,
    obtain ⟨t, ht, hxt⟩ := hxspace,
    use [t, ht],
    rw ←closure_combi_interior_eq_convex_hull (K₁.indep hs),
    refine closure_minimal (λ x' hx', _) (is_closed_convex_hull _),
    have hxspace := mem_space_iff.2 ⟨s, hs, hx'.1⟩,
    rw [hspace, ←combi_interiors_cover, mem_Union₂] at hxspace,
    obtain ⟨t', ht', hxt'⟩ := hxspace,
    suffices htt' : t = t',
    { rw htt',
      exact hxt'.1 },
    obtain ⟨F, hF, hinterior⟩ := hpartition _ ht,
    obtain ⟨F', hF', hinterior'⟩ := hpartition _ ht',
    apply disjoint_interiors ht ht' (_ : x ∈ _) _,
    { rw [hinterior, mem_Union₂] at ⊢ hxt,
      obtain ⟨u, hu, hxu⟩ := hxt,
      use [u, hu, hxu] },
    { rw [hinterior', mem_Union₂] at ⊢ hxt',
      obtain ⟨u, hu, hxu⟩ := hxt',
      refine ⟨u, hu, _⟩,
      rw ←disjoint_interiors hs (hF' hu) hx' hxu,
      exact hx } }
end

instance : is_partial_order (simplicial_complex ℝ E) subdivides :=
{ refl := subdivides.refl,
  trans := λ K₁ K₂ K₃, subdivides.trans,
  antisymm := begin
    suffices aux_lemma : ∀ {K₁ K₂ : simplicial_complex ℝ E},
      K₁.subdivides K₂ → K₂.subdivides K₁ → ∀ {s}, s ∈ K₁.faces → s ∈ K₂.faces,
    { rintro K₁ K₂ h₁ h₂,
      ext s,
      exact ⟨λ hs, aux_lemma h₁ h₂ hs, λ hs, aux_lemma h₂ h₁ hs⟩ },
    rintro K₁ K₂ h₁ h₂ s hs,
    rw subdivides_iff_partition at h₂ h₁,
    obtain ⟨x, hxs⟩ := (K₁.nonempty hs).combi_interior (K₁.indep hs),
    obtain ⟨F, hF, hFs⟩ := h₂.2.2 _ hs,
    have hxs' := hxs,
    rw [hFs, mem_Union₂] at hxs',
    obtain ⟨t, ht, hxt⟩ := hxs',
    obtain ⟨F', hF', hF't⟩ := h₁.2.2 _ (hF ht),
    rw [hF't, mem_Union₂] at hxt,
    obtain ⟨u, hu, hxu⟩ := hxt,
    have := disjoint_interiors hs (hF' hu) hxs hxu,
    subst this,
    suffices h : s = t,
    { rw h,
      exact hF ht },
    refine combi_interior.inj (K₁.indep hs) (K₂.indep $ hF ht) (subset.antisymm _ _),
    { rw hF't,
      exact subset_bUnion_of_mem hu },
    { rw hFs,
      exact subset_bUnion_of_mem ht }
  end }

end semi_normed_group

/-
/-- max diameter of  simplices -/
def simplicial_complex.mesh_size (S : simplicial_complex 𝕜 E) : 𝕜 := sorry

def barycentrisation : list (fin m → 𝕜) → fin m → 𝕜 :=
  λ L,

def simplicial_complex.barycentric_subdivision (S : simplicial_complex 𝕜 E) :
  simplicial_complex 𝕜 E :=
{ faces := {s | ∃ {L : list (fin m → 𝕜)}, list.to_finset L ∈ S.faces ∧ s = },
  indep := _,
  down_closed := _,
  disjoint := _ }-/

end geometry.simplicial_complex
