/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.specific_limits
import combinatorics.simplicial_complex.basic
import set_theory.fincard

/-!
# Subdivision of simplicial complexes
-/

open affine set

variables {𝕜 E : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] {m : ℕ}
  {S₁ S₂ : simplicial_complex 𝕜 E}

/--
S₁ ≤ S₂ (S₁ is a subdivision of S₂) iff their underlying space is the same and each face of S₁ is
contained in some face of S₂
-/
instance : has_le (simplicial_complex 𝕜 E) := ⟨λ S₁ S₂, S₁.space = S₂.space ∧
  ∀ {X₁ : finset  E}, X₁ ∈ S₁.faces → ∃ X₂ ∈ S₂.faces,
  convex_hull 𝕜 (X₁ : set E) ⊆ convex_hull 𝕜 (X₂ : set E)⟩

lemma subdivision_iff_combi_interiors_subset_combi_interiors :
  S₁ ≤ S₂ ↔ S₂.space ⊆ S₁.space ∧
  ∀ {X₁}, X₁ ∈ S₁.faces → ∃ {X₂}, X₂ ∈ S₂.faces ∧ combi_interior X₁ ⊆ combi_interior X₂ :=
begin
  split,
  { rintro ⟨hspace, hS⟩,
    use ge_of_eq hspace,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := hS hX,
    obtain ⟨Z, hZY, hXZ⟩ := simplex_combi_interiors_split_interiors (S₂.indep hY) hXY,
    exact ⟨Z, S₂.down_closed hY hZY, hXZ⟩ },
  { rintro ⟨hspace, hS⟩,
    split,
    { apply subset.antisymm _ hspace,
      rintro x hx,
      obtain ⟨X₁, hX₁, hx⟩ := mem_space_iff.1 hx,
      obtain ⟨X₂, hX₂, hX₁X₂⟩ := hS hX₁,
      rw mem_space_iff,
      refine ⟨X₂, hX₂, _⟩,
      apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior _ _ hX₁X₂ hx,
      { apply S₁.indep hX₁ },
      { apply S₂.indep hX₂ } },
    { rintro X₁ hX₁,
      obtain ⟨X₂, hX₂, hX₁X₂⟩ := hS hX₁,
      refine ⟨_, hX₂, convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior _ _ _⟩,
      { apply S₁.indep hX₁ },
      { apply S₂.indep hX₂ },
      { apply hX₁X₂ }}}
end

lemma subdivision_iff_partition :
  S₁ ≤ S₂ ↔ (S₁.faces.nonempty → S₂.faces.nonempty) ∧ S₁.space ⊆ S₂.space ∧ ∀ {X₂}, X₂ ∈ S₂.faces →
  ∃ {F}, F ⊆ S₁.faces ∧ combi_interior X₂ = ⋃ (X₁ ∈ F), combi_interior X₁ :=
begin
  split,
  { rintro ⟨hspace, hsubdiv⟩,
    split,
    { rintro ⟨X₁, hX₁⟩,
      obtain ⟨X₂, hX₂, hX₁X₂⟩ := hsubdiv hX₁,
      exact ⟨X₂, hX₂⟩ },
    use le_of_eq hspace,
    rintro X hX,
    use [{Y | Y ∈ S₁.faces ∧ combi_interior Y ⊆ combi_interior X}, (λ Y hY, hY.1)],
    ext x,
    split,
    { rintro hxX,
      have hxspace := mem_space_iff.2 ⟨X, hX, hxX.1⟩,
      rw [←hspace, combi_interiors_cover, mem_bUnion_iff] at hxspace,
      obtain ⟨Y, hY, hxY⟩ := hxspace,
      apply mem_bUnion _ hxY,
      use hY,
      rintro y hyY,
      obtain ⟨Z, hZ, hYZ⟩ := hsubdiv hY,
      obtain ⟨W, hWZ, hYW⟩ := simplex_combi_interiors_split_interiors (S₂.indep hZ) hYZ,
      rw disjoint_interiors hX (S₂.down_closed hZ hWZ) hxX (hYW hxY),
      exact hYW hyY },
    { rw mem_bUnion_iff,
      rintro ⟨Y, ⟨hY, hYX⟩, hxY⟩,
      exact hYX hxY }},
  { rintro ⟨hempty, hspace, hpartition⟩,
    have hspace : S₁.space = S₂.space,
    { apply subset.antisymm hspace,
      rintro x hx,
      rw [combi_interiors_cover, mem_bUnion_iff] at ⊢ hx,
      obtain ⟨X, hX, hxX⟩ := hx,
      obtain ⟨F, hF, hXint⟩ := hpartition hX,
      rw [hXint, mem_bUnion_iff] at hxX,
      obtain ⟨Y, hY, hxY⟩ := hxX,
      exact ⟨Y, hF hY, hxY⟩ },
    use hspace,
    rintro X hX,
    cases finset.eq_empty_or_nonempty X with hXempty hXnonempty,
    { obtain ⟨Y, hY⟩ := hempty ⟨X, hX⟩,
      use [Y, hY],
      rw hXempty,
      simp },
    obtain ⟨x, hx⟩ := nonempty_combi_interior_of_nonempty (S₁.indep hX) hXnonempty,
    have hxspace := mem_space_iff.2 ⟨X, hX, hx.1⟩,
    rw [hspace, combi_interiors_cover, mem_bUnion_iff] at hxspace,
    obtain ⟨Y, hY, hxY⟩ := hxspace,
    use [Y, hY],
    rw ←closure_combi_interior_eq_convex_hull (S₁.indep hX),
    apply closure_minimal _ is_closed_convex_hull,
    rintro x' hx',
    have hxspace := mem_space_iff.2 ⟨X, hX, hx'.1⟩,
    rw [hspace, combi_interiors_cover, mem_bUnion_iff] at hxspace,
    obtain ⟨Y', hY', hxY'⟩ := hxspace,
    suffices hYY' : Y = Y',
    { rw hYY',
      exact hxY'.1 },
    obtain ⟨F, hF, hinterior⟩ := hpartition hY,
    obtain ⟨F', hF', hinterior'⟩ := hpartition hY',
    apply disjoint_interiors hY hY' (_ : x ∈ _) _,
    { rw [hinterior, mem_bUnion_iff] at ⊢ hxY,
      obtain ⟨Z, hZ, hxZ⟩ := hxY,
      use [Z, hZ, hxZ] },
    { rw [hinterior', mem_bUnion_iff] at ⊢ hxY',
      obtain ⟨Z, hZ, hxZ⟩ := hxY',
      use [Z, hZ],
      rw ←disjoint_interiors hX (hF' hZ) hx' hxZ,
      exact hx }}
end

instance : partial_order (simplicial_complex 𝕜 E) :=
{ le := λ S₁ S₂, S₁ ≤ S₂,
  le_refl := (λ S, ⟨rfl, (λ X hX, ⟨X, hX, subset.refl _⟩)⟩),
  le_trans := begin
    rintro S₁ S₂ S₃ h₁₂ h₂₃,
    use eq.trans h₁₂.1 h₂₃.1,
    rintro X₁ hX₁,
    obtain ⟨X₂, hX₂, hX₁₂⟩ := h₁₂.2 hX₁,
    obtain ⟨X₃, hX₃, hX₂₃⟩ := h₂₃.2 hX₂,
    exact ⟨X₃, hX₃, subset.trans hX₁₂ hX₂₃⟩,
  end,
  le_antisymm := begin
    suffices aux_lemma : ∀ {S₁ S₂ : simplicial_complex 𝕜 E}, S₁ ≤ S₂ → S₂ ≤ S₁ → ∀ {X},
      X ∈ S₁.faces → X ∈ S₂.faces,
    { rintro S₁ S₂ h₁ h₂,
      ext X,
      exact ⟨λ hX, aux_lemma h₁ h₂ hX, λ hX, aux_lemma h₂ h₁ hX⟩ },
    rintro S₁ S₂ h₁ h₂ X hX,
    rw subdivision_iff_partition at h₂ h₁,
    cases finset.eq_empty_or_nonempty X with hXempty hXnonempty,
    { rw hXempty,
      exact empty_mem_faces_of_nonempty (h₁.1 ⟨X, hX⟩) },
    obtain ⟨x, hxX⟩ := nonempty_combi_interior_of_nonempty (S₁.indep hX) hXnonempty,
    obtain ⟨F, hF, hFX⟩ := h₂.2.2 hX,
    have hxX' := hxX,
    rw [hFX, mem_bUnion_iff] at hxX',
    obtain ⟨Y, hY, hxY⟩ := hxX',
    obtain ⟨F', hF', hF'Y⟩ := h₁.2.2 (hF hY),
    rw [hF'Y, mem_bUnion_iff] at hxY,
    obtain ⟨Z, hZ, hxZ⟩ := hxY,
    have := disjoint_interiors hX (hF' hZ) hxX hxZ,
    subst this,
    suffices h : X = Y,
    { rw h,
      exact hF hY },
    apply combi_interior.inj (S₁.indep hX) (S₂.indep (hF hY)) (subset.antisymm _ _),
    { rw hF'Y,
      exact subset_bUnion_of_mem hZ },
    { rw hFX,
      exact subset_bUnion_of_mem hY }
  end }

/-
/-- max diameter of  simplices -/
def simplicial_complex.mesh_size (S : simplicial_complex 𝕜 E) : 𝕜 := sorry

def barycentrisation : list (fin m → 𝕜) → fin m → 𝕜 :=
  λ L,

def simplicial_complex.barycentric_subdivision (S : simplicial_complex 𝕜 E) :
  simplicial_complex 𝕜 E :=
{ faces := {X | ∃ {L : list (fin m → 𝕜)}, list.to_finset L ∈ S.faces ∧ X = },
  indep := _,
  down_closed := _,
  disjoint := _ }-/
