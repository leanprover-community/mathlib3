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
(not_empty_mem : ∅ ∉ faces)
(indep : ∀ {s}, s ∈ faces → affine_independent 𝕜 (coe : (s : set E) → E))
(down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces)
(inter_subset_convex_hull : ∀ {s t}, s ∈ faces → t ∈ faces →
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E))

namespace simplicial_complex
variables {𝕜 E} {K : simplicial_complex 𝕜 E} {s t : finset E} {x : E}

/-- The underlying space of a simplicial complex is the union of its faces. -/
def space (K : simplicial_complex 𝕜 E) : set E := ⋃ s ∈ K.faces, convex_hull 𝕜 (s : set E)

instance : has_coe (simplicial_complex 𝕜 E) (set E) := ⟨simplicial_complex.space⟩

lemma mem_iff : x ∈ (K : set E) ↔ ∃ s ∈ K.faces, x ∈ convex_hull 𝕜 (s : set E) := mem_bUnion_iff

/-- Construct a simplicial complex by removing the empty face for you. -/
@[simps] def of_erase
  (faces : set (finset E))
  (indep : ∀ s ∈ faces, affine_independent 𝕜 (coe : (s : set E) → E))
  (down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces)
  (inter_subset_convex_hull : ∀ s t ∈ faces,
    convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E)) :
  simplicial_complex 𝕜 E :=
{ faces := faces \ {∅},
  not_empty_mem := λ h, h.2 (mem_singleton _),
  indep := λ s hs, indep _ hs.1,
  down_closed := λ s t hs hts ht, ⟨down_closed _ hs.1 _ hts, ht⟩,
  inter_subset_convex_hull := λ s t hs ht, inter_subset_convex_hull _ _ hs.1 ht.1 }

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps] def of_subcomplex (K : simplicial_complex 𝕜 E)
  (faces : set (finset E))
  (subset : faces ⊆ K.faces)
  (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces) :
  simplicial_complex 𝕜 E :=
{ faces := faces,
  not_empty_mem := λ h, K.not_empty_mem (subset h),
  indep := λ s hs, K.indep (subset hs),
  down_closed := λ s t hs hts _, down_closed hs hts,
  inter_subset_convex_hull := λ s t hs ht, K.inter_subset_convex_hull (subset hs) (subset ht) }

variables {𝕜 E}

lemma convex_hull_face_subset (hs : s ∈ K.faces) : convex_hull 𝕜 ↑s ⊆ (K : set E) :=
subset_bUnion_of_mem hs

protected lemma subset (hs : s ∈ K.faces) : (s : set E) ⊆ K :=
(subset_convex_hull 𝕜 _).trans (convex_hull_face_subset hs)

lemma convex_hull_inter_convex_hull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t = convex_hull 𝕜 (s ∩ t : set E) :=
(K.inter_subset_convex_hull hs ht).antisymm $ subset_inter
  (convex_hull_mono $ set.inter_subset_left _ _) $ convex_hull_mono $ set.inter_subset_right _ _

/-! ### Vertices -/

/-- The vertices of a simplicial complex are its zero dimensional faces. -/
def vertices (K : simplicial_complex 𝕜 E) : set E := {x | {x} ∈ K.faces}

lemma mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := by refl

lemma vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : set E) :=
begin
  ext x,
  refine ⟨λ h, mem_bUnion h $ mem_coe.2 $ mem_singleton_self x, λ h, _⟩,
  obtain ⟨s, hs, hx⟩ := mem_bUnion_iff.1 h,
  exact K.down_closed hs (finset.singleton_subset_iff.2 $ mem_coe.1 hx) (singleton_ne_empty _),
end

lemma vertices_subset : K.vertices ⊆ K :=
vertices_eq.subset.trans $ set.bUnion_mono $ λ x hx, subset_convex_hull 𝕜 x

lemma vertex_mem_convex_hull_iff (hx : x ∈ K.vertices) (hs : s ∈ K.faces) :
  x ∈ convex_hull 𝕜 (s : set E) ↔ x ∈ s :=
begin
  refine ⟨λ h, _, λ h, subset_convex_hull _ _ h⟩,
  classical,
  have h := K.inter_subset_convex_hull hx hs ⟨by simp, h⟩,
  by_contra H,
  rwa [←coe_inter, finset.disjoint_iff_inter_eq_empty.1
    (finset.disjoint_singleton_right.2 H).symm, coe_empty, convex_hull_empty] at h,
end

/-- A face is a subset of another one iff its vertices are.  -/
lemma face_subset_face_iff (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
  convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t ↔ s ⊆ t :=
⟨λ h x hxs, (vertex_mem_convex_hull_iff (K.down_closed hs (finset.singleton_subset_iff.2 hxs) $
  singleton_ne_empty _) ht).1 (h (subset_convex_hull 𝕜 ↑s hxs)), convex_hull_mono⟩

/-! ### Facets -/

/-- A facet of a simplicial complex is a maximal face. -/
def facets (K : simplicial_complex 𝕜 E) : set (finset E) :=
{s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t}

lemma mem_facets : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t := mem_sep_iff

lemma facets_subset : K.facets ⊆ K.faces := λ s hs, hs.1

lemma not_facet_iff_subface (hs : s ∈ K.faces) : (s ∉ K.facets ↔ ∃ t, t ∈ K.faces ∧ s ⊂ t) :=
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

/-! ### The semilattice of simplicial complexes -/

variables (𝕜 E)

instance : has_bot (simplicial_complex 𝕜 E) :=
⟨{ faces := ∅,
  not_empty_mem := set.not_mem_empty ∅,
  indep := λ s hs, (set.not_mem_empty _ hs).elim,
  down_closed := λ s _ hs, (set.not_mem_empty _ hs).elim,
  inter_subset_convex_hull := λ s _ hs, (set.not_mem_empty _ hs).elim }⟩

instance : inhabited (simplicial_complex 𝕜 E) := ⟨⊥⟩

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : has_inf (simplicial_complex 𝕜 E) :=
⟨λ K L, { faces := K.faces ∩ L.faces,
  not_empty_mem := λ h, K.not_empty_mem (set.inter_subset_left _ _ h),
  indep := λ s hs, K.indep hs.1,
  down_closed := λ s t hs hst ht, ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩,
  inter_subset_convex_hull := λ s t hs ht, K.inter_subset_convex_hull hs.1 ht.1 }⟩

instance : semilattice_inf_bot (simplicial_complex 𝕜 E) :=
{ inf := (⊓),
  inf_le_left := λ K L s hs, hs.1,
  inf_le_right := λ K L s hs, hs.2,
  le_inf := λ K L M hKL hKM s hs, ⟨hKL hs, hKM hs⟩,
  bot := ⊥,
  bot_le := λ K, set.empty_subset _,
  .. (partial_order.lift faces $ λ x y, ext _ _) }

variables {𝕜 E}

lemma faces_bot : (⊥ : simplicial_complex 𝕜 E).faces = ∅ := rfl

lemma coe_bot : ((⊥ : simplicial_complex 𝕜 E) : set E) = ∅ := set.bUnion_empty _

lemma facets_bot : (⊥ : simplicial_complex 𝕜 E).facets = ∅ := eq_empty_of_subset_empty facets_subset

end simplicial_complex
