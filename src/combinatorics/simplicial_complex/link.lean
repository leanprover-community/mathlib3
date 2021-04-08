import combinatorics.simplicial_complex.star
import combinatorics.simplicial_complex.closure

namespace affine
open set
variables {m n k : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E]
  {S : simplicial_complex E} {X Y : finset E} {A : set (finset E)}

def simplicial_complex.link (S : simplicial_complex E) (A : set (finset E)) :
  simplicial_complex E :=
{ faces := {X | (∀ {W}, W ∈ A → disjoint W X) ∧ ∃ {Y Z}, Y ∈ A ∧ Z ∈ S.faces ∧ X ⊆ Z ∧ Y ⊆ Z},
  indep := λ X ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩, S.indep (S.down_closed hZ hXZ),
  down_closed := begin
    rintro X W ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩ hWX,
    split,
    { rintro V hV,
      exact finset.disjoint_of_subset_right hWX (hXdisj hV), },
    { exact ⟨Y, Z, hY, hZ, subset.trans hWX hXZ, hYZ⟩ }
  end,
  disjoint := λ X X' ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩ ⟨hXdisj', Y', Z', hY', hZ', hXZ', hYZ'⟩,
    S.disjoint (S.down_closed hZ hXZ) (S.down_closed hZ' hXZ') }

lemma link_empty :
  (S.link ∅).faces = ∅ :=
begin
  unfold simplicial_complex.link,
  simp,
end

lemma link_singleton_empty :
  S.link {∅} = S :=
begin
  ext X,
  split,
  {
    rintro ⟨_, _, Z, _, hZ, hXZ, _⟩,
    exact S.down_closed hZ hXZ,
  },
  {
    rintro hX,
    split,
    { rintro W (h : W = ∅),
      rw h,
      exact finset.disjoint_empty_left X, },
    exact ⟨∅, X, rfl, hX, subset.refl X, empty_subset X⟩,
  }
end

lemma mem_link_singleton_iff :
  Y ∈ (S.link {X}).faces ↔ disjoint X Y ∧ ∃ {Z}, Z ∈ S.faces ∧ Y ⊆ Z ∧ X ⊆ Z :=
begin
  unfold simplicial_complex.link,
  simp,
end

lemma link_singleton_subset (hX : X ≠ ∅) :
  (S.link {X}).faces ⊆ (S.Star {X}).faces \ S.star {X} :=
begin
  rintro Y ⟨hY, W, Z, (hWX : W = X), hZ, hYZ, hWZ⟩,
  simp at hY,
  subst hWX,
  split,
  { exact ⟨W, Z, mem_singleton W, hZ, hYZ, hWZ⟩, },
  { rintro h,
    rw mem_star_singleton_iff at h,
    exact hX (disjoint_self.1 (finset.disjoint_of_subset_right h.2 hY)), }
end

lemma link_singleton_eq_Star_minus_star_iff_singleton (hX : X ≠ ∅) :
  (S.link {X}).faces = (S.Star {X}).faces \ S.star {X} ↔ X.card = 1 :=
begin
  split,
  {
    sorry --true? The PDF claims so but I'm not sure
  },
  {
    rintro hXcard,
    apply subset.antisymm (link_singleton_subset hX),
    rintro Y ⟨h, hYstar⟩,
    obtain ⟨Z, hZ, hYZ, hXZ⟩ := mem_Star_singleton_iff.1 h,
    split,
    {
      obtain ⟨x, hxX⟩ := finset.card_eq_one.1 hXcard,
      rintro W (hW : W = X),
      subst hW,
      subst hxX,
      rw finset.singleton_disjoint,
      rintro hx,
      apply hYstar,
      rw [mem_star_singleton_iff, finset.singleton_subset_iff],
      exact ⟨S.down_closed hZ hYZ, hx⟩,
    },
    exact ⟨X, Z, rfl, hZ, hYZ, hXZ⟩,
  }
end

lemma link_subset :
  (S.link A).faces ⊆ S.faces :=
λ X ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩, S.down_closed hZ hXZ

lemma link_eq_Star_sub_star_closure {S : simplicial_complex E} {A : set (finset E)} :
  (S.link A).faces = (S.Star A).faces \ S.star ((S.closure A).faces \ {∅}) :=
begin
  ext X,
  split,
  {
    rintro ⟨hXdisj, hXStar⟩,
    use hXStar,
    rintro ⟨hX, Y, ⟨⟨hY, Z, hZ, hYZ⟩, (hYnonempty : Y ≠ ∅)⟩, hYX⟩,
    have hYZX : Y ⊆ Z ∩ X := finset.subset_inter hYZ hYX,
    rw finset.disjoint_iff_inter_eq_empty.mp (hXdisj hZ) at hYZX,
    exact hYnonempty (finset.subset_empty.mp hYZX),
  },
  {
    rintro ⟨hXStar, hX'⟩,
    split,
    {
      rintro W hW,
      rw finset.disjoint_iff_inter_eq_empty,
      apply finset.eq_empty_of_forall_not_mem,
      rintro x hx,
      apply hX',
      use Star_subset hXStar,
      use {x},
      split,
      split,
      {
        unfold simplicial_complex.closure simplicial_complex.of_surcomplex,
        simp,
        exact ⟨S.down_closed (Star_subset hXStar) (subset.trans (finset.singleton_subset_iff.2 hx)
          (finset.inter_subset_right _ _)), W, hW, finset.inter_subset_left _ _ hx⟩,
      },
      rintro (h : {x} = ∅),
      exact (finset.singleton_ne_empty x) h,
      exact finset.singleton_subset_iff.2 (finset.inter_subset_right W X hx),
    },
    { exact hXStar }
  }
end
/-

lemma link_facet_iff {S : simplicial_complex E} {A : set (finset E)} {n k : ℕ}
  (hS : S.pure_of n) {X : finset E} (hA : ∀ {W}, W ∈ A → (W : finset _).card = k) :
  X ∈ (S.link A).facets ↔ ∃ {W Y}, W ∈ A ∧ Y ∈ S.facets ∧ W ⊆ Y ∧ X = Y \ W :=-/

-- X ∈ (S.link A).facets ↔ X ∉ S.facets ∧ (∀ {W}, W ∈ A → disjoint W X) ∧ ∃ {Y W Z}, Y ∈ S.facets ∧
--   W ∈ A ∧ Z ∈ S.facets ∧ X ∪ W ⊆ Z ∧ ∀ {y}, y ∈ Y → y ∈ X ∨ ∃ {V}, V ∈ A ∧ y ∈ V
lemma link_facet_iff :
  X ∈ (S.link A).facets ↔ X ∉ S.facets ∧ (∀ {W}, W ∈ A → disjoint W X) ∧ ∃ {W Y Z},
   W ∈ A ∧ Y ∈ S.facets ∧ Z ∈ S.faces ∧ X ∪ W ⊆ Z ∧ ∀ {y}, y ∈ Y → y ∈ X ∨ ∃ {V}, V ∈ A ∧ y ∈ V :=
begin
  split,
  {
    rintro ⟨⟨hXdisj, W, Z, hW, hZ, hXZ, hWZ⟩, hXmax⟩,
    sorry
    /-obtain ⟨Y, hY, hZY⟩ := subfacet hZ,
    split,
    {
      sorry
    },
    {
      use [(λ W, hXdisj), W, Y, Z, hW, hY, hZ, finset.union_subset hXZ hWZ],
      rintro y hy,
      sorry
    }-/
  },
  {
    rintro ⟨stuff, hXdisj, W, Y, Z, hW, hY, hZ, hXYW, hunion⟩,
    split,
    {
      have hXZ : X ⊆ Z := sorry, -- finset.union_subset_iff.1 hXYW
      have hWZ : W ⊆ Z := sorry, -- finset.union_subset_iff.1 hXYW
      exact ⟨(λ V, hXdisj), W, Z, hW, hZ, hXZ, hWZ⟩,
    },
    {
      rintro V ⟨hVdisj, U, R, hU, hR, hVR, hUR⟩ hXV,
      apply finset.subset.antisymm hXV,
      rintro v hv,
      /-have := hA hU hW (facets_subset hY) hWY,
      rw finset.mem_sdiff,-/
      --have := hA hV hW (facets_subset hY) hWY ⟨x, finset.mem_inter.2 ⟨hx.1, hx.2.1⟩⟩,
      sorry
      /-apply finset.eq_of_subset_of_card_le hYWX,
      rw finset.card_sdiff hWY,
      have := finset.card_le_of_subset (finset.union_subset hUV hXV),
      rw [finset.card_disjoint_union (hXdisj hU), hA hU] at this,
      rw [hA hW, hS hY],
      exact nat.le_sub_left_of_add_le (le_trans this (face_card_le_pureness hS hV)),-/
    }
  }
end

lemma pure_link_of_pure (hS : S.pure_of n) (hA : ∀ {X}, X ∈ A → (X : finset _).card = k) :
  (S.link A).pure_of (n - k) :=
begin
  rintro X ⟨⟨hXdisj, W, Z, hW, hZ, hXZ, hWZ⟩, hXmax⟩, --easy once we have `link_facet_iff`
  sorry
end

end affine
