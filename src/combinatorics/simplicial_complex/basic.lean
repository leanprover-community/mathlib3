/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.simplicial_complex.basic
import combinatorics.simplicial_complex.simplex

/-!
# Simplicial complexes
-/

open_locale classical affine big_operators
open finset geometry

variables {𝕜 E ι : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  {K K₁ K₂ : simplicial_complex 𝕜 E} {x y : E} {s t : finset E} {A : set (finset E)} {m n : ℕ}

protected lemma nonempty (K : simplicial_complex 𝕜 E) (hs : s ∈ K) : s.nonempty :=
nonempty_of_ne_empty $ ne_of_mem_of_not_mem hs K.not_empty_mem

@[simp] lemma mem_faces_iff (K : simplicial_complex 𝕜 E) : s ∈ K.faces ↔ s ∈ K := iff.rfl

lemma le_def : K₁ ≤ K₂ ↔ K₁.faces ⊆ K₂.faces := iff.rfl

lemma facets_singleton (hK : K.faces = {s}) : K.facets = {s} :=
begin
  rw set.eq_singleton_iff_unique_mem at ⊢ hK,
  exact ⟨⟨hK.1, λ t ht _, (hK.2 _ ht).symm⟩, λ t ht, hK.2 _ ht.1⟩,
end

lemma of_subcomplex_le (K : simplicial_complex 𝕜 E) (faces) {subset down_closed} :
  K.of_subcomplex faces subset down_closed ≤ K :=
subset

/-- The cells of a simplicial complex are its simplices whose dimension matches the one of the
space. -/
def cells (K : simplicial_complex 𝕜 E) : set (finset E) :=
{s | s ∈ K ∧ s.card = finite_dimensional.finrank 𝕜 E + 1}

/-- The subcells of a simplicial complex are its simplices whose cardinality matches the dimension
of the space. They are thus one smaller than cells. -/
def simplicial_complex.subcells (K : simplicial_complex 𝕜 E) : set (finset E) :=
{s | s ∈ K ∧ s.card = finite_dimensional.finrank 𝕜 E}

lemma mem_of_mem_convex_hull (hx : x ∈ K.vertices) (hs : s ∈ K)
  (hxs : x ∈ convex_hull 𝕜 (s : set E)) :
  x ∈ s :=
begin
  have h := K.inter_subset_convex_hull hx hs ⟨by simp, hxs⟩,
  by_contra H,
  norm_cast at h,
  rwa [inter_comm, disjoint_iff_inter_eq_empty.1 (disjoint_singleton_right.2 H), coe_empty,
    convex_hull_empty] at h,
end

lemma subset_of_convex_hull_subset_convex_hull (hs : s ∈ K) (ht : t ∈ K)
  (hst : convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t) :
  s ⊆ t :=
λ x hxs, mem_of_mem_convex_hull (K.down_closed hs (singleton_subset_iff.2 hxs) $
  singleton_nonempty _) ht $ hst $ subset_convex_hull 𝕜 ↑s hxs

lemma disjoint_interiors (hs : s ∈ K) (ht : t ∈ K) (hxs : x ∈ combi_interior 𝕜 s)
  (hxt : x ∈ combi_interior 𝕜 t) :
  s = t :=
begin
  by_contra,
  have hst : s ∩ t ⊂ s,
  { use inter_subset_left s t,
    intro H,
    exact hxt.2 (set.mem_bUnion ⟨subset.trans H (inter_subset_right s t), (λ H2,
      h (subset.antisymm (subset.trans H (inter_subset_right s t)) H2))⟩ hxs.1) },
  refine hxs.2 (set.mem_bUnion hst _),
  exact_mod_cast K.inter_subset_convex_hull hs ht ⟨hxs.1, hxt.1⟩,
end

lemma disjoint_interiors_aux (hs : s ∈ K) (ht : t ∈ K) (h : s ≠ t) :
  disjoint (combi_interior 𝕜 s) (combi_interior 𝕜 t) :=
λ x hx, h (disjoint_interiors hs ht hx.1 hx.2)

lemma eq_singleton_of_singleton_mem_combi_interior (hx : {x} ∈ K) (hs : s ∈ K)
  (hxs : x ∈ combi_interior 𝕜 s) :
  s = {x} :=
begin
  apply disjoint_interiors hs hx hxs,
  rw combi_interior_singleton,
  exact set.mem_singleton x,
end

lemma combi_interiors_cover : K.space = ⋃ s ∈ K, combi_interior 𝕜 s :=
begin
  refine (set.bUnion_subset $ λ s hs, _).antisymm
    (set.bUnion_subset_bUnion $ λ t ht, ⟨t, ht, combi_interior_subset_convex_hull⟩),
  rw simplex_combi_interiors_cover,
  refine set.bUnion_subset_bUnion (λ t hts, _),
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { refine ⟨s, hs, _⟩,
    rw combi_interior_empty,
    exact set.empty_subset _ },
  { exact ⟨t, K.down_closed hs hts ht, set.subset.rfl⟩ }
end

/-- The simplices interiors form a partition of the underlying space (except that they contain the
empty set) -/
lemma combi_interiors_partition (hx : x ∈ K.space) : ∃! s, s ∈ K ∧ x ∈ combi_interior 𝕜 s :=
begin
  rw combi_interiors_cover at hx,
  change x ∈ ⋃ (s : finset E) (H : s ∈ K.faces), combi_interior 𝕜 s at hx,
  rw set.mem_bUnion_iff at hx,
  obtain ⟨s, hs, hxs⟩ := hx,
  exact ⟨s, ⟨⟨hs, hxs⟩, λ t ⟨ht, hxt⟩, disjoint_interiors ht hs hxt hxs⟩⟩,
end

lemma mem_convex_hull_iff : x ∈ convex_hull 𝕜 (s : set E) ↔ ∃ t ⊆ s, x ∈ combi_interior 𝕜 t :=
begin
  simp [simplex_combi_interiors_cover],
end

lemma mem_combi_frontier_iff' : x ∈ combi_frontier 𝕜 s ↔ ∃ {t}, t ⊂ s ∧ x ∈ combi_interior 𝕜 t :=
begin
  rw mem_combi_frontier_iff,
  split,
  { rintro ⟨t, hts, hxt⟩,
    --rw [simplex_combi_interiors_cover, mem_bUnion_iff] at hxt,
    --obtain ⟨u, hu⟩ := simplex_combi_interiors_cover
    sorry
  },
  { rintro ⟨t, hts, hxt⟩,
    exact ⟨t, hts, hxt.1⟩ }
end

lemma subset_of_combi_interior_inter_convex_hull_nonempty (hs : s ∈ K) (ht : t ∈ K)
  (hst : (combi_interior 𝕜 s ∩ convex_hull 𝕜 (t : set E)).nonempty) :
  s ⊆ t :=
begin
  obtain ⟨x, hxs, hxt⟩ := hst,
  obtain ⟨u, hut, hxu⟩ := mem_convex_hull_iff.1 hxt,
  rw disjoint_interiors hs (K.down_closed ht hut $ nonempty_of_ne_empty _) hxs hxu,
  exact hut,
  { rintro rfl,
    rwa combi_interior_empty at hxu }
end

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]
  {K : simplicial_complex 𝕜 E} {x y : E} {s t : finset E} {A : set (finset E)} {m n : ℕ}

/-- A constructor for simplicial complexes by specifying a set of faces to close downward. -/
@[simps] def of_set_closure
  (indep : ∀ {s : finset E}, s ∈ A → affine_independent 𝕜 (coe : (s : set E) → E))
  (inter_subset_convex_hull : ∀ {s t}, s ∈ A → t ∈ A →
    convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E)) :
  simplicial_complex 𝕜 E :=
{ faces := {s | s.nonempty ∧ ∃ t, t ∈ A ∧ s ⊆ t},
  indep := λ s ⟨hs, t, ht, hst⟩, (indep ht).mono hst,
  down_closed := λ s t ⟨hs, u, hu, hsu⟩ hts ht, ⟨ht, u, hu, hts.trans hsu⟩,
  inter_subset_convex_hull :=
  begin
    rintro v s ⟨hv, t, ht, hvt⟩ ⟨hs, u, hu, hsu⟩ x ⟨hxv, hxs⟩,
    have hxtu : x ∈ convex_hull 𝕜 (t ∩ u : set E) :=
      inter_subset_convex_hull ht hu ⟨convex_hull_mono hvt hxv, convex_hull_mono hsu hxs⟩,
    have hxvu : x ∈ convex_hull 𝕜 (v ∩ u : set E),
    { have := disjoint_convex_hull_of_subsets (indep ht) hvt (inter_subset_left t u),
      norm_cast at this hxtu,
      exact_mod_cast convex_hull_mono
        (inter_subset_inter_left $ inter_subset_right t u) (this ⟨hxv, hxtu⟩) },
    have hxts : x ∈ convex_hull 𝕜 (t ∩ s : set E),
    { have := disjoint_convex_hull_of_subsets (indep hu) (inter_subset_right t u) hsu,
      norm_cast at this hxtu,
      exact_mod_cast convex_hull_mono
        (inter_subset_inter_right $ inter_subset_left t u) (this ⟨hxtu, hxs⟩) },
    norm_cast at hxvu hxts,
    have hxvs := disjoint_convex_hull_of_subsets (indep ht)
      ((inter_subset_inter_right hvt).trans $ inter_subset_left t u)
      (inter_subset_left t s) ⟨hxvu, hxts⟩,
    norm_cast at hxvs,
    exact_mod_cast convex_hull_mono ((inter_subset_inter_right $ inter_subset_left v u).trans $
      inter_subset_inter_left $ inter_subset_right t s) hxvs,
  end,
  not_empty_mem := λ h, h.1.ne_empty rfl }

/-- A constructor for simplicial complexes by specifying a face to close downward. -/
@[simp] def simplicial_complex.of_simplex (indep : affine_independent 𝕜 (coe : s → E)) :
  simplicial_complex 𝕜 E :=
of_set_closure
  begin rintro t (ht : t = s), rw ht, exact indep end
  begin rintro t u (ht : t = s) (hu : u = s), rw [ht, hu, set.inter_self _, set.inter_self _],
    exact set.subset.rfl end

lemma mem_simplex_complex_iff (hs : affine_independent 𝕜 (coe : s → E)) :
  t ∈ simplicial_complex.of_simplex hs ↔ t.nonempty ∧ t ⊆ s :=
begin
  refine ⟨_, λ h, ⟨h.1, s, rfl, h.2⟩⟩,
  rintro ⟨ht, u, (rfl : u = s), hts⟩,
  exact ⟨ht, hts⟩,
end

variables {𝕜 E}

--noncomputable def simplicial_complex.dim (K : simplicial_complex 𝕜 E) :
--  ℕ :=

-- Corollary of `affine_independent.card_le_finrank_succ`
lemma face_dimension_le_space_dimension [finite_dimensional 𝕜 E] (hs : s ∈ K) :
  s.card ≤ finite_dimensional.finrank 𝕜 E + 1 :=
(K.indep hs).card_le_finrank_succ

lemma subfacet [finite_dimensional 𝕜 E] (hs : s ∈ K) : ∃ {t}, t ∈ K.facets ∧ s ⊆ t :=
begin
  have := id hs,
  revert this,
  apply strong_downward_induction_on s,
  { rintro t h htcard ht,
    by_cases htfacet : t ∈ K.facets,
    { exact ⟨t, htfacet, subset.refl _⟩ },
    obtain ⟨u, hu, htu⟩ := (not_facet_iff_subface ht).mp htfacet,
    obtain ⟨v, hv⟩ := h (face_dimension_le_space_dimension hu) htu hu,
    exact ⟨v, hv.1, htu.1.trans hv.2⟩ },
  exact face_dimension_le_space_dimension hs,
end

lemma facets_empty_iff_eq_bot [finite_dimensional 𝕜 E] : K.facets = ∅ ↔ K = ⊥ :=
begin
  refine ⟨λ h, _, _⟩,
  { ext s,
    refine iff_of_false (λ hs, _) (set.not_mem_empty _),
    obtain ⟨t, ht, hst⟩ := subfacet hs,
    exact h.subset ht },
  { rintro rfl,
    exact facets_bot }
end

lemma cells_subset_facets [finite_dimensional 𝕜 E] : K.cells ⊆ K.facets :=
begin
  rintro s ⟨hs, hscard⟩,
  by_contra,
  obtain ⟨t, ht, hst⟩ := (not_facet_iff_subface hs).mp h,
  have := card_lt_card hst,
  have := face_dimension_le_space_dimension ht,
  linarith,
end

lemma simplex_combi_interiors_split_interiors (ht : affine_independent 𝕜 (coe : (t : set E) → E))
  (hst : convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t) :
  ∃ u ⊆ t, combi_interior 𝕜 s ⊆ combi_interior 𝕜 u :=
begin
  let K := simplicial_complex.of_simplex ht,
  let F := t.powerset.filter (λ v : finset E, (s : set E) ⊆ convex_hull 𝕜 ↑v),
  sorry
  /-obtain ⟨u, hu, humin⟩ := inf' _
  (begin
    use t,
    simp only [true_and, mem_powerset_self, mem_filter],
    exact subset.trans (subset_convex_hull 𝕜 _) hst,
  end : F.nonempty)
  begin
    rintro A B hA hB,
    simp at ⊢ hA hB,
    exact ⟨subset.trans (inter_subset_left _ _) hA.1,
      subset.trans (subset_inter hA.2 hB.2) (K.disjoint ((mem_simplex_complex_iff ht).2 hA.1)
      ((mem_simplex_complex_iff ht).2 hB.1))⟩
  end,
  simp at hu,
  use [u, hu.1],
  rintro x hxs,
  use convex_hull_min hu.2 (convex_convex_hull 𝕜 _) hxs.1,
  rintro hxu,
  rw mem_combi_frontier_iff' at hxu,
  obtain ⟨v, hvu, hxv⟩ := hxu,
  apply hvu.2 (humin v _),
  simp,
  use [subset.trans hvu.1 hu.1],
  rw convex_hull_eq _ at ⊢ hu,
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combi_interior_subset_positive_weighings hxs,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combi_interior_subset_positive_weighings hxv,
  let u : E → E → 𝕜 := λ a, if ha : a ∈ s then classical.some (hu.2 ha) else (λ b, 0),
  have hupos : ∀ {a}, a ∈ s → ∀ (b : E), b ∈ u → 0 < u a b,
  { rintro a ha,
    have := classical.some_spec (hu.2 ha),
    sorry
  },
  have husum : ∀ {a}, a ∈ s → ∑ (b : E) in u, u a b = 1,
  { sorry
  },
  have hucenter : ∀ {a}, a ∈ s → u.center_mass (u a) id = a,
  { sorry
  },
  let t : E → 𝕜 := λ b, if hb : b ∈ u then ∑ (a : E) in s, v a * u a b else 0,-/
  /-rintro y (hys : y ∈ s),
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combi_interior_subset_positive_weighings hxs,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combi_interior_subset_positive_weighings hxv,-/
  --rw mem_convex_hull,
  /-by_contra hsv,
  obtain ⟨y, hys, hyv⟩ := not_subset.1 hsv,-/
  /-apply hxs.2,
  rw mem_combi_frontier_iff at ⊢,
  use [s.filter (λ w : E, w ∈ convex_hull 𝕜 (v : set E)), filter_subset _ _],
  { rintro hsv,
    apply hvu.2 (humin v _),
    simp,
    use [subset.trans hvu.1 hu.1],
    rintro y (hys : y ∈ s),
    have := hsv hys,
    simp at this,
    exact this.2 },
  { simp,
    apply convex_hull_mono (subset_inter (subset.refl _) _) hxs.1,
    by_contra hsv,
    rw not_subset at hsv,
    /-suffices hsv : ↑s ⊆ convex_hull 𝕜 ↑v,
    { apply convex_hull_mono (subset_inter (subset.refl _) hsv) hxs.1,
    },-/
    sorry
  }-/
end

lemma simplex_combi_interiors_split_interiors_nonempty (hs : s.nonempty)
  (ht : affine_independent 𝕜 (coe : (t : set E) → E))
  (hst : convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t) :
  ∃ u ⊆ t, u.nonempty ∧ combi_interior 𝕜 s ⊆ combi_interior 𝕜 u :=
begin
  sorry
end

end linear_ordered_field
end geometry.simplicial_complex
