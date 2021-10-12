/-
Copyright (c) 2021 taël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: taël Dillies, Bhavik Mehta
-/
import analysis.convex.extreme
import analysis.convex.topology
import order.filter.archimedean

/-!
# Simplicial complexes

In this file, we define simplicial complexes in `𝕜`-modules. A simplicial complex is a collection
of simplices closed by inclusion (of vertices) and intersection (of underlying sets).

ue model them by a downward-closed set of affine independent finite sets whose convex hulls "glue
nicely", each finite set and its convex hull corresponding respectively to the vertices and the underlying set of a simplex.

## TODO

Simplicial complexes can be generalized to affine spaces once `convex_hull` has been ported to
convex spaces.
-/

open_locale classical affine big_operators
open set

variables {𝕜 E ι : Type*} [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]

lemma disjoint_convex_hull_of_subsets {s t u : finset E}
  (hs : affine_independent 𝕜 (λ p, p : (s : set E) → E)) (ht : t ⊆ s) (hu : u ⊆ s) :
  convex_hull 𝕜 (t : set E) ∩ convex_hull 𝕜 (u : set E) ⊆ convex_hull 𝕜 (t ∩ u : set E) :=
sorry

variables (𝕜 E)

/-- A simplicial complex in a `𝕜`-module. -/
@[ext] structure simplicial_complex :=
(faces : set (finset E))
(empty_mem : ∅ ∈ faces)
(indep : ∀ {s}, s ∈ faces → affine_independent 𝕜 (λ p, p : (s : set E) → E))
(down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces)
(disjoint : ∀ {s t}, s ∈ faces → t ∈ faces →
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E))

/-- The empty simplicial complex is made up of only the empty simplex. -/
def simplicial_complex.empty : simplicial_complex 𝕜 E :=
{ faces := {∅},
  empty_mem := mem_singleton ∅,
  indep :=
    begin
      rintro _ (rfl : _ = ∅),
      apply affine_independent_of_subsingleton 𝕜 _,
      rw [finset.coe_empty, subsingleton_coe],
      exact subsingleton_empty,
    end,
  down_closed := λ s t hs, hs.symm ▸ finset.subset_empty.1,
  disjoint :=
    begin
      rintro _ _ (rfl : _ = ∅) (rfl : _ = ∅),
      simp_rw [finset.coe_empty, empty_inter, convex_hull_empty, empty_inter],
    end }

instance : has_emptyc (simplicial_complex 𝕜 E) := ⟨simplicial_complex.empty 𝕜 E⟩

variables {𝕜 E} {S S₁ S₂ : simplicial_complex 𝕜 E} {s t : finset E} {x y : E}
  {m n : ℕ}

/-- The underlying space of a simplicial complex. -/
def simplicial_complex.space (S : simplicial_complex 𝕜 E) : set E :=
⋃ s ∈ S.faces, convex_hull 𝕜 (s : set E)

instance : has_coe (simplicial_complex 𝕜 E) (set E) := ⟨simplicial_complex.space⟩

lemma mem_iff : x ∈ (S : set E) ↔ ∃ s ∈ S.faces, x ∈ convex_hull 𝕜 (s : set E) := mem_bUnion_iff

/-- A constructor for simplicial complexes by giving a bigger simplicial complex. -/
@[simps] def simplicial_complex.subset (S : simplicial_complex 𝕜 E)
  (faces : set (finset E))
  (nonempty : faces.nonempty)
  (subset : faces ⊆ S.faces)
  (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces) :
  simplicial_complex 𝕜 E :=
{ faces := faces,
  empty_mem := let ⟨x, hx⟩ := nonempty in down_closed hx x.empty_subset,
  indep := λ s hs, S.indep (subset hs),
  down_closed := λ s t hs hts, down_closed hs hts,
  disjoint := λ s t hs ht, S.disjoint (subset hs) (subset ht) }

/-- A constructor for simplicial complexes by specifying a set of faces to close downward. -/
@[simps] def simplicial_complex.of_faces
  (faces : set (finset E))
  (nonempty : faces.nonempty)
  (indep : ∀ {s}, s ∈ faces → affine_independent 𝕜 (λ p, p : (s : set E) → E))
  (disjoint : ∀ {s t}, s ∈ faces → t ∈ faces →
    convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E)) :
  simplicial_complex 𝕜 E :=
{ faces := {s | ∃ t, t ∈ faces ∧ s ⊆ t},
  empty_mem := let ⟨x, hx⟩ := nonempty in ⟨x, hx, x.empty_subset⟩,
  indep := λ s ⟨t, ht, hst⟩, (indep ht).mono hst,
  down_closed := λ s t ⟨u, hu, hsu⟩ hts, ⟨u, hu, hts.trans hsu⟩,
  disjoint := -- This is actually pretty tricky. The idea is to work in `u`, then in `v`, then
              -- intersect the results.
    begin
      rintro s t ⟨u, hu, hsu⟩ ⟨v, hv, htv⟩ x ⟨hxs, hxt⟩,
      have hxuv : x ∈ convex_hull 𝕜 (u ∩ v : set E) :=
        disjoint hu hv ⟨convex_hull_mono hsu hxs, convex_hull_mono htv hxt⟩,
      have hxsv : x ∈ convex_hull 𝕜 (s ∩ v : set E),
      { refine convex_hull_mono (inter_subset_inter_right _ _) (disjoint_convex_hull_of_subsets (indep hu) hsu (finset.inter_subset_left u v)
          ⟨hxs, _⟩),
          rw finset.coe_inter,
          exact inter_subset_right _ _, },
      have hxts : x ∈ convex_hull 𝕜 (t ∩ s : set E),
      { have := disjoint_convex_hull_of_subsets (indep hu) (finset.inter_subset_right t u) hsu,
        norm_cast at this hxuv,
        exact_mod_cast convex_hull_mono
          (finset.inter_subset_inter_right (finset.inter_subset_left t u)) (this ⟨hxuv, hxs⟩), },
      norm_cast at hxsv hxts,
      have hxus := disjoint_convex_hull_of_subsets (indep ht)
        (subset.trans (finset.inter_subset_inter_right hut) (finset.inter_subset_left t u))
        (finset.inter_subset_left t s) ⟨hxsv, hxts⟩,
      norm_cast at hxus,
      exact_mod_cast convex_hull_mono (subset.trans
        (finset.inter_subset_inter_right (finset.inter_subset_left u u))
        (finset.inter_subset_inter_left (finset.inter_subset_right t s))) hxus,
    end}

/-- A constructor for simplicial complexes by specifying a face to close downward. -/
@[simps] def simplicial_complex.of_face (s : finset E)
  (indep : affine_independent 𝕜 (λ p, p : (s : set E) → E)) :
  simplicial_complex 𝕜 E :=
simplicial_complex.of_faces {s}
  (singleton_nonempty s)
  begin rintro t (ht : t = s), rw ht, exact indep end
  begin rintro t u (ht : t = s) (hu : u = s), rw [ht, hu, inter_self _, inter_self _],
    exact subset.rfl end

lemma simplicial_complex.of_face_mem_simplex_complex_iff
  {hs : affine_independent 𝕜 (λ p, p : (s : set E) → E)} :
  t ∈ (simplicial_complex.of_face _ hs).faces ↔ t ⊆ s :=
begin
  split,
  { rintro ⟨u, (hu : u = s), hts⟩,
    rw ← hu,
    exact hts },
  { rintro hts,
    exact ⟨s, rfl, hts⟩ }
end

variables {𝕜 E}

lemma empty_mem_faces_of_nonempty :
  (S.faces).nonempty → ∅ ∈ S.faces :=
λ ⟨s, hs⟩, S.down_closed hs (empty_subset s)

lemma space_empty.empty :
  ((∅ : simplicial_complex.empty 𝕜 E) : set E) = ∅ :=
begin
  unfold simplicial_complex.empty simplicial_complex.space,
  simp,
end

lemma convex_hull_face_subset_space (hs : s ∈ S.faces) :
  convex_hull 𝕜 ↑s ⊆ S :=
λ x hx, mem_bUnion hs hx

lemma face_subset (hs : s ∈ S.faces) :
  (s : set E) ⊆ S :=
set.subset.trans (subset_convex_hull 𝕜 _) (convex_hull_face_subset_space hs)

def simplicial_complex.points (S : simplicial_complex 𝕜 E) :
  set E :=
⋃ k ∈ S.faces, (k : set E)

lemma points_subset :
  S.points ⊆ S :=
bUnion_subset_bUnion_right (λ x hx, subset_convex_hull 𝕜 x)

--noncomputable def simplicial_complex.dim (S : simplicial_complex 𝕜 E) :
--  ℕ :=

--Refinement of `size_bound`
lemma face_dimension_le_space_dimension [finite_dimensional 𝕜 E] (hs : s ∈ S.faces) :
  finset.card s ≤ finite_dimensional.finrank 𝕜 E + 1 :=
size_bound (S.indep hs)

def simplicial_complex.facets (S : simplicial_complex 𝕜 E) :
  set (finset E) :=
{s | s ∈ S.faces ∧ (∀ {t}, t ∈ S.faces → s ⊆ t → s = t)}

lemma facets_subset : S.facets ⊆ S.faces := λ s hs, hs.1

lemma not_facet_iff_subface : s ∈ S.faces → (s ∉ S.facets ↔ ∃ {t}, t ∈ S.faces ∧ s ⊂ t) :=
begin
  rintro hs,
  split,
  { rintro (hs' : ¬(s ∈ S.faces ∧ (∀ {t}, t ∈ S.faces → s ⊆ t → s = t))),
    push_neg at hs',
    obtain ⟨t, ht⟩ := hs' hs,
    exact ⟨t, ht.1, ⟨ht.2.1, (λ hts, ht.2.2 (finset.subset.antisymm ht.2.1 hts))⟩⟩, },
  rintro ⟨t, ht⟩ ⟨hs, hs'⟩,
  have := hs' ht.1 ht.2.1,
  rw this at ht,
  exact ht.2.2 (subset.refl t),
end

lemma subfacet [finite_dimensional 𝕜 E] (hs : s ∈ S.faces) :
  ∃ {t}, t ∈ S.facets ∧ s ⊆ t :=
begin
  have := id hs,
  revert this,
  apply finset.strong_downward_induction_on s,
  { rintro t h htcard ht,
    by_cases htfacet : t ∈ S.facets,
    { exact ⟨t, htfacet, finset.subset.refl _⟩, },
    obtain ⟨u, hu, htu⟩ := (not_facet_iff_subface ht).mp htfacet,
    obtain ⟨u, hu⟩ := h (face_dimension_le_space_dimension hu) htu hu,
    exact ⟨u, hu.1, finset.subset.trans htu.1 hu.2⟩ },
  exact face_dimension_le_space_dimension hs,
end

lemma facets_empty (hS : S.faces = ∅) :
  S.facets = ∅ :=
begin
  rw [←subset_empty_iff, ←hS],
  exact facets_subset,
end

lemma facets_empty_iff_faces_empty [finite_dimensional 𝕜 E] :
  S.facets = ∅ ↔ S.faces = ∅ :=
begin
  classical,
  split,
  { intro h,
    by_contra h',
    rw [←ne.def, set.ne_empty_iff_nonempty] at h',
    obtain ⟨s, hs⟩ := h',
    obtain ⟨t, ht, hu⟩ := subfacet hs,
    rw h at ht,
    apply ht },
  exact facets_empty,
end

lemma facets_singleton (hS : S.faces = {s}) :
  S.facets = {s} :=
begin
  ext s,
  unfold simplicial_complex.facets,
  rw hS,
  simp,
  exact λ hs _, hs,
end

lemma facets_singleton_empty (hS : S.faces = {∅}) :
  S.facets = {∅} :=
facets_singleton hS

/--
The cells of a simplicial complex are its simplices whose dimension matches the one of the space.
-/
def simplicial_complex.cells (S : simplicial_complex 𝕜 E) :
  set (finset E) :=
{s | s ∈ S.faces ∧ s.card = finite_dimensional.finrank 𝕜 E + 1}

lemma cells_subset_facets [finite_dimensional 𝕜 E] :
  S.cells ⊆ S.facets :=
begin
  rintro s ⟨hs, hscard⟩,
  by_contra,
  obtain ⟨t, ht, hst⟩ := (not_facet_iff_subface hs).mp h,
  have := finset.card_lt_card hst,
  have := face_dimension_le_space_dimension ht,
  linarith,
end

/--
The subcells of a simplicial complex are its simplices whose cardinality matches the dimension of
the space. They are thus one smaller than cells.
-/
def simplicial_complex.subcells (S : simplicial_complex 𝕜 E) :
  set (finset E) :=
{s | s ∈ S.faces ∧ s.card = finite_dimensional.finrank 𝕜 E}

def simplicial_complex.vertices (S : simplicial_complex 𝕜 E) :
  set E :=
{x | {x} ∈ S.faces}

lemma mem_of_mem_convex_hull (hx : {x} ∈ S.faces) (hs : s ∈ S.faces)
  (hxs : x ∈ convex_hull 𝕜 (s : set E)) :
  x ∈ s :=
begin
  have h := S.disjoint hx hs ⟨by simp, hxs⟩,
  by_contra H,
  norm_cast at h,
  rw [finset.inter_comm, finset.disjoint_iff_inter_eq_empty.1 (finset.disjoint_singleton.2 H)] at h,
  simp at h,
  exact h,
end

/-- A face is a subset of another one iff its vertices are.  -/
lemma face_subset_face_iff (hs : s ∈ S.faces) (ht : t ∈ S.faces) :
  convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t ↔ s ⊆ t :=
⟨λ x hxs, mem_of_mem_convex_hull (S.down_closed hs (finset.singleton_subset_iff.2 hxs)) ht
  (hst (subset_convex_hull 𝕜 ↑s hxs)), convex_hull_mono⟩
