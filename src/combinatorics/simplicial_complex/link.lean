/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENKE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.star

/-!
# Link in a simplicial complex
-/

open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {m n k : ℕ}
  {K : simplicial_complex 𝕜 E} {s t : finset E} {A : set (finset E)}

def link (K : simplicial_complex 𝕜 E) (A : set (finset E)) : simplicial_complex 𝕜 E :=
K.of_subcomplex
  {s | s.nonempty ∧ (∀ ⦃r⦄, r ∈ A → disjoint (r : set E) s) ∧ ∃ (t ∈ A) (u ∈ K), s ⊆ u ∧ t ⊆ u}
  (λ s ⟨hs, hsA, t, ht, u, hu, hsu, htu⟩, K.down_closed hu hsu hs)
  (λ s t ⟨hs, hsA, u, hu, v, hv, hsv, huv⟩ hts ht,
    ⟨ht, λ r hr, (hsA hr).mono_right hts, u, hu, v, hv, hts.trans hsv, huv⟩)

lemma link_le : K.link A ≤ K := K.of_subcomplex_le _

@[simp] lemma link_bot : (⊥ : simplicial_complex 𝕜 E).link A = ⊥ := of_subcomplex_bot _

@[simp] lemma link_empty : K.link ∅ = ⊥ :=
begin
  ext s,
  exact iff_of_false (λ ⟨hs, hsA, t, ht, u, hu, hsu, htu⟩, ht) id,
end

@[simp] lemma link_singleton_empty : K.link {∅} = K :=
begin
  ext s,
  refine ⟨_, λ hs, ⟨K.nonempty hs, _, ⟨∅, rfl, s, hs, subset.refl s, empty_subset s⟩⟩⟩,
  { rintro ⟨hs, _, _, u, _, hu, hsu, _⟩,
    exact K.down_closed hu hsu hs },
  { rintro r (rfl : r = ∅),
    rw coe_empty,
    exact set.empty_disjoint _ }
end

lemma mem_link_singleton_iff [decidable_eq E] :
  t ∈ (K.link {s}).faces ↔ t.nonempty ∧ disjoint s t ∧ ∃ u ∈ K.faces, t ⊆ u ∧ s ⊆ u :=
begin
  unfold link,
  simp,
end

lemma link_singleton_subset (hs : s.nonempty) :
  (K.link {s}).faces ⊆ (K.Star {s}).faces \ K.star {s} :=
begin
  rintro t ⟨ht, W, u, (hWs : W = s), hu, htu, hWu⟩,
  simp at ht,
  subst hWs,
  split,
  { exact ⟨W, u, mem_singleton W, hu, htu, hWu⟩ },
  { rintro h,
    rw mem_star_singleton_iff at h,
    exact hs (disjoint_self.1 (finset.disjoint_of_subset_right h.2 ht)) }
end

lemma link_singleton_eq_Star_minus_star_iff_singleton (hs : s.nonempty) :
  (K.link {s}).faces = (K.Star {s}).faces \ K.star {s} ↔ s.card = 1 :=
begin
  split,
  { sorry --true? The PDF claims so but I'm not sure
  },
  { rintro hscard,
    apply subset.antisymm (link_singleton_subset hs),
    rintro t ⟨h, htstar⟩,
    obtain ⟨u, hu, htu, hsu⟩ := mem_Star_singleton_iff.1 h,
    split,
    {   obtain ⟨x, hxs⟩ := finset.card_eq_one.1 hscard,
      rintro W (hW : W = s),
      subst hW,
      subst hxs,
      rw finset.singleton_disjoint,
      rintro hx,
      apply htstar,
      rw [mem_star_singleton_iff, finset.singleton_subset_iff],
      exact ⟨K.down_closed hu htu, hx⟩,
    },
    exact ⟨s, u, rfl, hu, htu, hsu⟩,
  }
end

lemma link_eq_Star_sub_star_closure {K : simplicial_complex 𝕜 E} {A : set (finset E)} :
  (K.link A).faces = (K.Star A).faces \ K.star ((K.closure A).faces \ {∅}) :=
begin
  ext s,
  split,
  { rintro ⟨hsdisj, hsStar⟩,
    use hsStar,
    rintro ⟨hs, t, ⟨⟨ht, u, hu, htu⟩, (htnonempty : t ≠ ∅)⟩, hts⟩,
    have htus : t ⊆ u ∩ s := finset.subset_inter htu hts,
    rw finset.disjoint_iff_inter_eq_empty.mp (hsdisj hu) at htus,
    exact htnonempty (finset.subset_empty.mp htus) },
  rintro ⟨hsStar, hs'⟩,
  refine ⟨λ W hW x hx, hs' ⟨Star_subset hsStar, {x}, _, _, _⟩, _⟩,
  { unfold simplicial_complex.closure simplicial_complex.of_subcomplex,
      simp,
      exact ⟨K.down_closed (Star_subset hsStar) (subset.trans (finset.singleton_subset_iff.2 hx)
        (finset.inter_subset_right _ _)), W, hW, finset.inter_subset_left _ _ hx⟩ },
  { rintro (h : {x} = ∅),
    exact (finset.singleton_ne_empty x) h },
  { exact finset.singleton_subset_iff.2 (finset.inter_subset_right W s hx) },
  { exact hsStar }
end
/-

lemma link_facet_iff {K : simplicial_complex 𝕜 E} {A : set (finset E)} {n k : ℕ}
  (hK : K.pure_of n) {s : finset E} (hA : ∀ {W}, W ∈ A → (W : finset _).card = k) :
  s ∈ (K.link A).facets ↔ ∃ {W t}, W ∈ A ∧ t ∈ K.facets ∧ W ⊆ t ∧ s = t \ W :=-/

-- s ∈ (K.link A).facets ↔ s ∉ K.facets ∧ (∀ {W}, W ∈ A → disjoint W s) ∧ ∃ {t W u}, t ∈ K.facets ∧
--   W ∈ A ∧ u ∈ K.facets ∧ s ∪ W ⊆ u ∧ ∀ {y}, y ∈ t → y ∈ s ∨ ∃ {V}, V ∈ A ∧ y ∈ V
lemma link_facet_iff :
  s ∈ (K.link A).facets ↔ s ∉ K.facets ∧ (∀ {W}, W ∈ A → disjoint W s) ∧ ∃ {W t u},
   W ∈ A ∧ t ∈ K.facets ∧ u ∈ K.faces ∧ s ∪ W ⊆ u ∧ ∀ {y}, y ∈ t → y ∈ s ∨ ∃ {V}, V ∈ A ∧ y ∈ V :=
begin
  split,
  { rintro ⟨⟨hsdisj, W, u, hW, hu, hsu, hWu⟩, hsmax⟩,
    sorry
    /-obtain ⟨t, ht, hut⟩ := subfacet hu,
    split,
    {   sorry
    },
    {   use [(λ W, hsdisj), W, t, u, hW, ht, hu, finset.union_subset hsu hWu],
      rintro y hy,
      sorry
    }-/
  },
  { rintro ⟨stuff, hsdisj, W, t, u, hW, ht, hu, hstW, hunion⟩,
    split,
    {   have hsu : s ⊆ u := sorry, -- finset.union_subset_iff.1 hstW
      have hWu : W ⊆ u := sorry, -- finset.union_subset_iff.1 hstW
      exact ⟨(λ V, hsdisj), W, u, hW, hu, hsu, hWu⟩,
    },
    {   rintro V ⟨hVdisj, U, R, hU, hR, hVR, hUR⟩ hsV,
      apply finset.subset.antisymm hsV,
      rintro v hv,
      /-have := hA hU hW (facets_subset ht) hWt,
      rw finset.mem_sdiff,-/
      --have := hA hV hW (facets_subset ht) hWt ⟨x, finset.mem_inter.2 ⟨hx.1, hx.2.1⟩⟩,
      sorry
      /-apply finset.eq_of_subset_of_card_le htWs,
      rw finset.card_sdiff hWt,
      have := finset.card_le_of_subset (finset.union_subset hUV hsV),
      rw [finset.card_disjoint_union (hsdisj hU), hA hU] at this,
      rw [hA hW, hK ht],
      exact nat.le_sub_left_of_add_le (le_trans this (face_card_le_pureness hK hV)),-/
    }
  }
end

lemma pure_link_of_pure (hK : K.pure_of n) (hA : ∀ {s}, s ∈ A → (s : finset _).card = k) :
  (K.link A).pure_of (n - k) :=
begin
  rintro s ⟨⟨hsdisj, W, u, hW, hu, hsu, hWu⟩, hsmax⟩, --easy once we have `link_facet_iff`
  sorry
end

end affine
