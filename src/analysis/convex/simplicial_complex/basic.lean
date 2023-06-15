/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.hull
import linear_algebra.affine_space.independent

/-!
# Simplicial complexes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define simplicial complexes in `𝕜`-modules. A simplicial complex is a collection
of simplices closed by inclusion (of vertices) and intersection (of underlying sets).

We model them by a downward-closed set of affine independent finite sets whose convex hulls "glue
nicely", each finite set and its convex hull corresponding respectively to the vertices and the
underlying set of a simplex.

## Main declarations

* `simplicial_complex 𝕜 E`: A simplicial complex in the `𝕜`-module `E`.
* `simplicial_complex.vertices`: The zero dimensional faces of a simplicial complex.
* `simplicial_complex.facets`: The maximal faces of a simplicial complex.

## Notation

`s ∈ K` means that `s` is a face of `K`.

`K ≤ L` means that the faces of `K` are faces of `L`.

## Implementation notes

"glue nicely" usually means that the intersection of two faces (as sets in the ambient space) is a
face. Given that we store the vertices, not the faces, this would be a bit awkward to spell.
Instead, `simplicial_complex.inter_subset_convex_hull` is an equivalent condition which works on the
vertices.

## TODO

Simplicial complexes can be generalized to affine spaces once `convex_hull` has been ported.
-/

open finset set

variables (𝕜 E : Type*) {ι : Type*} [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]

namespace geometry

/-- A simplicial complex in a `𝕜`-module is a collection of simplices which glue nicely together.
Note that the textbook meaning of "glue nicely" is given in
`geometry.simplicial_complex.disjoint_or_exists_inter_eq_convex_hull`. It is mostly useless, as
`geometry.simplicial_complex.convex_hull_inter_convex_hull` is enough for all purposes. -/
-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
@[ext] structure simplicial_complex :=
(faces : set (finset E))
(not_empty_mem : ∅ ∉ faces)
(indep : ∀ {s}, s ∈ faces → affine_independent 𝕜 (coe : (s : set E) → E))
(down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces)
(inter_subset_convex_hull : ∀ {s t}, s ∈ faces → t ∈ faces →
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E))

namespace simplicial_complex
variables {𝕜 E} {K : simplicial_complex 𝕜 E} {s t : finset E} {x : E}

/-- A `finset` belongs to a `simplicial_complex` if it's a face of it. -/
instance : has_mem (finset E) (simplicial_complex 𝕜 E) := ⟨λ s K, s ∈ K.faces⟩

/-- The underlying space of a simplicial complex is the union of its faces. -/
def space (K : simplicial_complex 𝕜 E) : set E := ⋃ s ∈ K.faces, convex_hull 𝕜 (s : set E)

lemma mem_space_iff : x ∈ K.space ↔ ∃ s ∈ K.faces, x ∈ convex_hull 𝕜 (s : set E) := mem_Union₂

lemma convex_hull_subset_space (hs : s ∈ K.faces) : convex_hull 𝕜 ↑s ⊆ K.space :=
subset_bUnion_of_mem hs

protected lemma subset_space (hs : s ∈ K.faces) : (s : set E) ⊆ K.space :=
(subset_convex_hull 𝕜 _).trans $ convex_hull_subset_space hs

lemma convex_hull_inter_convex_hull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t = convex_hull 𝕜 (s ∩ t : set E) :=
(K.inter_subset_convex_hull hs ht).antisymm $ subset_inter
  (convex_hull_mono $ set.inter_subset_left _ _) $ convex_hull_mono $ set.inter_subset_right _ _

/-- The conclusion is the usual meaning of "glue nicely" in textbooks. It turns out to be quite
unusable, as it's about faces as sets in space rather than simplices. Further,  additional structure
on `𝕜` means the only choice of `u` is `s ∩ t` (but it's hard to prove). -/
lemma disjoint_or_exists_inter_eq_convex_hull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
  disjoint (convex_hull 𝕜 (s : set E)) (convex_hull 𝕜 ↑t) ∨
  ∃ u ∈ K.faces, convex_hull 𝕜 (s : set E) ∩ convex_hull 𝕜 ↑t = convex_hull 𝕜 ↑u :=
begin
  classical,
  by_contra' h,
  refine h.2 (s ∩ t) (K.down_closed hs (inter_subset_left _ _) $ λ hst, h.1 $
    disjoint_iff_inf_le.mpr $ (K.inter_subset_convex_hull hs ht).trans _) _,
  { rw [←coe_inter, hst, coe_empty, convex_hull_empty],
    refl },
  { rw [coe_inter, convex_hull_inter_convex_hull hs ht] }
end

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
  inter_subset_convex_hull := λ s t hs ht, inter_subset_convex_hull _ hs.1 _ ht.1 }

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

/-! ### Vertices -/

/-- The vertices of a simplicial complex are its zero dimensional faces. -/
def vertices (K : simplicial_complex 𝕜 E) : set E := {x | {x} ∈ K.faces}

lemma mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := iff.rfl

lemma vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : set E) :=
begin
  ext x,
  refine ⟨λ h, mem_bUnion h $ mem_coe.2 $ mem_singleton_self x, λ h, _⟩,
  obtain ⟨s, hs, hx⟩ := mem_Union₂.1 h,
  exact K.down_closed hs (finset.singleton_subset_iff.2 $ mem_coe.1 hx) (singleton_ne_empty _),
end

lemma vertices_subset_space : K.vertices ⊆ K.space :=
vertices_eq.subset.trans $ Union₂_mono $ λ x hx, subset_convex_hull 𝕜 x

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

/-!
### The semilattice of simplicial complexes

`K ≤ L` means that `K.faces ⊆ L.faces`.
-/

variables (𝕜 E)

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : has_inf (simplicial_complex 𝕜 E) :=
⟨λ K L, { faces := K.faces ∩ L.faces,
  not_empty_mem := λ h, K.not_empty_mem (set.inter_subset_left _ _ h),
  indep := λ s hs, K.indep hs.1,
  down_closed := λ s t hs hst ht, ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩,
  inter_subset_convex_hull := λ s t hs ht, K.inter_subset_convex_hull hs.1 ht.1 }⟩

instance : semilattice_inf (simplicial_complex 𝕜 E) :=
{ inf := (⊓),
  inf_le_left := λ K L s hs, hs.1,
  inf_le_right := λ K L s hs, hs.2,
  le_inf := λ K L M hKL hKM s hs, ⟨hKL hs, hKM hs⟩,
  .. (partial_order.lift faces $ λ x y, ext _ _) }

instance : has_bot (simplicial_complex 𝕜 E) :=
⟨{ faces := ∅,
  not_empty_mem := set.not_mem_empty ∅,
  indep := λ s hs, (set.not_mem_empty _ hs).elim,
  down_closed := λ s _ hs, (set.not_mem_empty _ hs).elim,
  inter_subset_convex_hull := λ s _ hs, (set.not_mem_empty _ hs).elim }⟩

instance : order_bot (simplicial_complex 𝕜 E) :=
{ bot_le := λ K, set.empty_subset _, .. simplicial_complex.has_bot 𝕜 E }

instance : inhabited (simplicial_complex 𝕜 E) := ⟨⊥⟩

variables {𝕜 E}

lemma faces_bot : (⊥ : simplicial_complex 𝕜 E).faces = ∅ := rfl

lemma space_bot : (⊥ : simplicial_complex 𝕜 E).space = ∅ := set.bUnion_empty _

lemma facets_bot : (⊥ : simplicial_complex 𝕜 E).facets = ∅ := eq_empty_of_subset_empty facets_subset

end simplicial_complex
end geometry
