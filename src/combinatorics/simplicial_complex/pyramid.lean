import combinatorics.simplicial_complex.pure
import combinatorics.simplicial_complex.subdivision

namespace affine

open_locale classical affine big_operators
open set
variables {n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {v : E}

/-The pyramid of a vertex v with respect to a simplicial complex S is the surcomplex consisting of
all faces of S along with all faces of S with v added -/
def pyramid (hS : ∀ X ∈ S.faces, finset.card X ≤ S.dim) {v : E} (hv : v ∉ convex_hull S.space) :
  simplicial_complex E :=
 {faces := {X' | ∃ X ∈ S.faces, X' ⊆ X ∪ {v}},
  indep := begin
    rintro X' ⟨X, hX, hX'X⟩,
    sorry
  end,
  down_closed := λ X' Y ⟨X, hX, hX'X⟩ hYX', ⟨X, hX, subset.trans hYX' hX'X⟩,
  disjoint := begin
    rintro X' Y' ⟨X, hX, hX'X⟩ ⟨Y, hY, hY'Y⟩,
    sorry
  end}

lemma subcomplex_pyramid (hS : ∀ X ∈ S.faces, finset.card X ≤ S.dim)
  (hv : v ∉ convex_hull S.space) :
  S.faces ⊆ (pyramid hS hv).faces := λ X hX, ⟨X, hX, finset.subset_union_left X {v}⟩

--S₁ ≤ S₂ → S₁.space = S₂.space so maybe we can get rid of hv₂?
lemma pyramid_mono {S₁ S₂ : simplicial_complex E}
  (hS₁ : ∀ X ∈ S₁.faces, finset.card X ≤ S.dim) (hS₂ : ∀ X ∈ S₂.faces, finset.card X ≤ S.dim)
  (hv₁ : v ∉ convex_hull S₁.space) (hv₂ : v ∉ convex_hull S₂.space) :
  S₁ ≤ S₂ → pyramid hS₁ hv₁ ≤ pyramid hS₂ hv₂ :=
begin
  rintro h,
  split,
  {
    sorry
  },
  {
    rintro X ⟨Y, hY, hXYv⟩,
    obtain ⟨Z, hZ, hYZhull⟩ := h.2 hY,
    use Z ∪ {v},
    split,
    {
      exact ⟨Z, hZ, subset.refl _⟩,
    },
    have hXYvhull : convex_hull ↑X ⊆ convex_hull ↑(Y ∪ {v}) := convex_hull_mono hXYv,
    have hYvZvhull : convex_hull ↑(Y ∪ {v}) ⊆ convex_hull ↑(Z ∪ {v}),
    {
      sorry
    },
    exact subset.trans hXYvhull hYvZvhull,
  }
end

lemma pure_pyramid_of_pure [finite_dimensional ℝ E] (hn : n ≤ S.dim) (hS : S.pure_of n)
  (hv : v ∉ convex_hull S.space) :
  (pyramid (λ X hX, le_trans (face_card_le_pureness hS hX) hn) hv).pure_of (n + 1) :=
begin
  sorry
end

end affine
