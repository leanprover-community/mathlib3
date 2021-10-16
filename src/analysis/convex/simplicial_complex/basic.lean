/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.topology

/-!
# Simplicial complexes

In this file, we define simplicial complexes in `𝕜`-modules. A simplicial complex is a collection
of simplices closed by inclusion (of vertices) and intersection (of underlying sets).

We model them by a downward-closed set of affine independent finite sets whose convex hulls "glue
nicely", each finite set and its convex hull corresponding respectively to the vertices and the
underlying set of a simplex.

## Main declarations

* `simplicial_complex 𝕜 E`: A simplicial complex in the `𝕜`-module `E`.
* `simplicial_complex.vertices`: The zero dimensional faces of a simplicial complex.
* `simplicial_complex.facets`: The maximal faces of a simplicial complex.

## TODO

Simplicial complexes can be generalized to affine spaces once `convex_hull` has been ported.
-/

open finset set

variables {𝕜 E ι : Type*} [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]

variables (𝕜 E)

/-- A simplicial complex in a `𝕜`-module is a collection of simplices which glue nicely together. -/
@[ext] structure simplicial_complex :=
(faces : set (finset E))
(empty_mem : ∅ ∈ faces)
(indep : ∀ {s}, s ∈ faces → affine_independent 𝕜 (λ p, p : (s : set E) → E))
(down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces)
(disjoint : ∀ {s t}, s ∈ faces → t ∈ faces →
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E))

namespace simplicial_complex
variables {𝕜 E} {S : simplicial_complex 𝕜 E} {s t : finset E} {x : E}

/-- The underlying space of a simplicial complex is the union of its faces. -/
def space (S : simplicial_complex 𝕜 E) : set E := ⋃ s ∈ S.faces, convex_hull 𝕜 (s : set E)

instance : has_coe (simplicial_complex 𝕜 E) (set E) := ⟨simplicial_complex.space⟩

lemma mem_iff : x ∈ (S : set E) ↔ ∃ s ∈ S.faces, x ∈ convex_hull 𝕜 (s : set E) := mem_bUnion_iff

/-- A constructor for simplicial complexes by giving a bigger simplicial complex. -/
@[simps] def of_subset (S : simplicial_complex 𝕜 E)
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

variables {𝕜 E}

lemma convex_hull_face_subset (hs : s ∈ S.faces) : convex_hull 𝕜 ↑s ⊆ (S : set E) :=
subset_bUnion_of_mem hs

protected lemma subset (hs : s ∈ S.faces) : (s : set E) ⊆ S :=
(subset_convex_hull 𝕜 _).trans (convex_hull_face_subset hs)

lemma mem_of_mem_convex_hull (hx : {x} ∈ S.faces) (hs : s ∈ S.faces)
  (hxs : x ∈ convex_hull 𝕜 (s : set E)) :
  x ∈ s :=
begin
  classical,
  have h := S.disjoint hx hs ⟨by simp, hxs⟩,
  by_contra H,
  rwa [←coe_inter, finset.disjoint_iff_inter_eq_empty.1 (disjoint_singleton.2 H).symm, coe_empty,
    convex_hull_empty] at h,
end

/-- A face is a subset of another one iff its vertices are.  -/
lemma face_subset_face_iff (hs : s ∈ S.faces) (ht : t ∈ S.faces) :
  convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t ↔ s ⊆ t :=
⟨λ h x hxs, mem_of_mem_convex_hull (S.down_closed hs (finset.singleton_subset_iff.2 hxs)) ht
  (h (subset_convex_hull 𝕜 ↑s hxs)), convex_hull_mono⟩

/-! ### Vertices -/

/-- The vertices of a simplicial complex are its zero dimensional faces. -/
def vertices (S : simplicial_complex 𝕜 E) : set E := {x | {x} ∈ S.faces}

lemma vertices_eq : S.vertices = ⋃ k ∈ S.faces, (k : set E) :=
begin
  ext x,
  refine ⟨λ h, mem_bUnion h $ mem_coe.2 $ mem_singleton_self x, λ h, _⟩,
  obtain ⟨s, hs, hx⟩ := mem_bUnion_iff.1 h,
  exact S.down_closed hs (finset.singleton_subset_iff.2 $ mem_coe.1 hx),
end

lemma vertices_subset : S.vertices ⊆ S :=
vertices_eq.subset.trans $ bUnion_subset_bUnion_right $ λ x hx, subset_convex_hull 𝕜 x

/-! ### Facets -/

/-- A facet of a simplicial complex is a maximal face. -/
def facets (S : simplicial_complex 𝕜 E) : set (finset E) :=
{s ∈ S.faces | ∀ ⦃t⦄, t ∈ S.faces → s ⊆ t → s = t}

lemma facets_subset : S.facets ⊆ S.faces := λ s hs, hs.1

lemma not_facet_iff_subface (hs : s ∈ S.faces) : (s ∉ S.facets ↔ ∃ t, t ∈ S.faces ∧ s ⊂ t) :=
begin
  refine ⟨λ (hs' : ¬ (_ ∧ _)), _, _⟩,
  { push_neg at hs',
    obtain ⟨t, ht⟩ := hs' hs,
    exact ⟨t, ht.1, ⟨ht.2.1, (λ hts, ht.2.2 (subset.antisymm ht.2.1 hts))⟩⟩ },
  { rintro ⟨t, ht⟩ ⟨hs, hs'⟩,
    have := hs' ht.1 ht.2.1,
    rw this at ht,
    exact ht.2.2 (subset.refl t) } -- `has_ssubset.ssubset.ne` would be handy here
end

/-! ### The empty simplicial complex -/

variables (𝕜 E)

/-- The empty simplicial complex has only an empty face. -/
def empty : simplicial_complex 𝕜 E :=
{ faces := {∅},
  empty_mem := mem_singleton ∅,
  indep :=
    begin
      rintro _ (rfl : _ = ∅),
      apply affine_independent_of_subsingleton 𝕜 _,
      rw [coe_empty, subsingleton_coe],
      exact subsingleton_empty,
    end,
  down_closed := λ s t hs, hs.symm ▸ subset_empty.1,
  disjoint :=
    begin
      rintro _ _ (rfl : _ = ∅) (rfl : _ = ∅),
      simp_rw [coe_empty, set.empty_inter, convex_hull_empty, set.empty_inter],
    end }

instance : has_emptyc (simplicial_complex 𝕜 E) := ⟨empty 𝕜 E⟩

instance : inhabited (simplicial_complex 𝕜 E) := ⟨∅⟩

variables {𝕜 E}

lemma coe_empty : ((∅ : simplicial_complex 𝕜 E) : set E) = ∅ :=
begin
  rw ←@convex_hull_empty 𝕜,
  exact bUnion_singleton _ _,
end

lemma facets_empty : (∅ : simplicial_complex 𝕜 E).facets = {∅} :=
set.eq_singleton_iff_unique_mem.2 ⟨⟨mem_singleton _, λ s hs _, (eq_of_mem_singleton hs).symm⟩,
  λ s hs, eq_of_mem_singleton $ facets_subset hs⟩

end simplicial_complex
