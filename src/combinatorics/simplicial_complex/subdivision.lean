import tactic
import data.fincard
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology
import analysis.specific_limits
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.extreme_point
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.simplex

open affine set

variables {m : ℕ}

/--
S₁ ≤ S₂ (S₁ is a subdivision of S₂) iff their underlying space is the same and each face of S₁ is
contained in some face of S₂
-/
instance : has_le (simplicial_complex m) := ⟨λ S₁ S₂, S₁.space = S₂.space ∧
  ∀ {X₁ : finset (fin m → ℝ)}, X₁ ∈ S₁.faces → ∃ X₂ ∈ S₂.faces,
  convex_hull (X₁ : set(fin m → ℝ)) ⊆ convex_hull (X₂ : set(fin m → ℝ))⟩

def subdivision_order : partial_order (simplicial_complex m) :=
  {le := λ S₁ S₂, S₁ ≤ S₂,
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
    have aux_lemma : ∀ {S₁ S₂ : simplicial_complex m}, S₁ ≤ S₂ → S₂ ≤ S₁ → ∀ {X},
      X ∈ S₁.faces → X ∈ S₂.faces,
    { rintro S₁ S₂ h₁ h₂ W hW,
      apply finset.strong_downward_induction_on' (λ X hX, simplex_dimension_le_space_dimension hX)
        hW,
      { rintro X hX h,
        obtain ⟨Y, hY, hXYhull⟩ := h₁.2 hX,
        obtain ⟨Z, hZ, hYZhull⟩ := h₂.2 hY,
        have hXZhull := subset.trans (inter_subset_inter_right (convex_hull ↑X)
          (subset.trans hXYhull hYZhull)) (S₁.disjoint hX hZ),
        rw inter_self at hXZhull,
        norm_cast at hXZhull,
        have hXZ : X ⊆ Z := subset.trans
          (subset_of_convex_hull_eq_convex_hull_of_linearly_independent (S₁.indep hX)
          (subset.antisymm hXZhull (convex_hull_mono (finset.inter_subset_left X Z))))
          (finset.inter_subset_right _ _),
        by_cases hZX : Z ⊆ X,
        { rw finset.subset.antisymm hZX hXZ at hYZhull,
          rw eq_of_convex_hull_eq_convex_hull_of_linearly_independent_of_linearly_independent
            (S₁.indep hX) (S₂.indep hY) (subset.antisymm hXYhull hYZhull),
          exact hY },
        { exact S₂.down_closed (h hZ ⟨hXZ, hZX⟩) hXZ }}},
    rintro S₁ S₂ h₁ h₂,
    ext X,
    exact ⟨λ hX, aux_lemma h₁ h₂ hX, λ hX, aux_lemma h₂ h₁ hX⟩,
  end}

lemma subdivision_iff_combi_interiors_subset_combi_interiors {S₁ S₂ : simplicial_complex m} :
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

lemma subdivision_iff_partition {S₁ S₂ : simplicial_complex m} :
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
      rw disjoint_interiors hX (S₂.down_closed hZ hWZ) x ⟨hxX, hYW hxY⟩,
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
    rw ← closure_combi_interior_eq_convex_hull,
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
    apply disjoint_interiors hY hY' x (mem_inter _ _),
    { rw [hinterior, mem_bUnion_iff] at ⊢ hxY,
      obtain ⟨Z, hZ, hxZ⟩ := hxY,
      use [Z, hZ, hxZ] },
    { rw [hinterior', mem_bUnion_iff] at ⊢ hxY',
      obtain ⟨Z, hZ, hxZ⟩ := hxY',
      use [Z, hZ],
      rw ← disjoint_interiors hX (hF' hZ) x' ⟨hx', hxZ⟩,
      exact hx },
    apply S₁.indep hX }
end
