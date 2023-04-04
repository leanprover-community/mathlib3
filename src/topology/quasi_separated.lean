/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.subset_properties
import topology.separation
import topology.noetherian_space

/-!
# Quasi-separated spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological space is quasi-separated if the intersections of any pairs of compact open subsets
are still compact.
Notable examples include spectral spaces, Noetherian spaces, and Hausdorff spaces.

A non-example is the interval `[0, 1]` with doubled origin: the two copies of `[0, 1]` are compact
open subsets, but their intersection `(0, 1]` is not.

## Main results

- `is_quasi_separated`: A subset `s` of a topological space is quasi-separated if the intersections
of any pairs of compact open subsets of `s` are still compact.
- `quasi_separated_space`: A topological space is quasi-separated if the intersections of any pairs
of compact open subsets are still compact.
- `quasi_separated_space.of_open_embedding`: If `f : α → β` is an open embedding, and `β` is
  a quasi-separated space, then so is `α`.
-/

open topological_space

variables {α β : Type*} [topological_space α] [topological_space β] {f : α → β}

/-- A subset `s` of a topological space is quasi-separated if the intersections of any pairs of
compact open subsets of `s` are still compact.

Note that this is equivalent to `s` being a `quasi_separated_space` only when `s` is open. -/
def is_quasi_separated (s : set α) : Prop :=
∀ (U V : set α), U ⊆ s → is_open U → is_compact U → V ⊆ s →
  is_open V → is_compact V → is_compact (U ∩ V)

/-- A topological space is quasi-separated if the intersections of any pairs of compact open
subsets are still compact. -/
@[mk_iff]
class quasi_separated_space (α : Type*) [topological_space α] : Prop :=
(inter_is_compact : ∀ (U V : set α),
  is_open U → is_compact U → is_open V → is_compact V → is_compact (U ∩ V))

lemma is_quasi_separated_univ_iff {α : Type*} [topological_space α] :
  is_quasi_separated (set.univ : set α) ↔ quasi_separated_space α :=
begin
  rw quasi_separated_space_iff,
  simp [is_quasi_separated],
end

lemma is_quasi_separated_univ {α : Type*} [topological_space α] [quasi_separated_space α] :
  is_quasi_separated (set.univ : set α) :=
is_quasi_separated_univ_iff.mpr infer_instance

lemma is_quasi_separated.image_of_embedding {s : set α}
  (H : is_quasi_separated s) (h : embedding f) : is_quasi_separated (f '' s) :=
begin
  intros U V hU hU' hU'' hV hV' hV'',
  convert (H (f ⁻¹' U) (f ⁻¹' V) _ (h.continuous.1 _ hU') _ _ (h.continuous.1 _ hV') _).image
    h.continuous,
  { symmetry,
    rw [← set.preimage_inter, set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset],
    exact (set.inter_subset_left _ _).trans (hU.trans (set.image_subset_range _ _)) },
  { intros x hx, rw ← (h.inj.inj_on _).mem_image_iff (set.subset_univ _) trivial, exact hU hx },
  { rw h.is_compact_iff_is_compact_image,
    convert hU'',
    rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset],
    exact hU.trans (set.image_subset_range _ _) },
  { intros x hx, rw ← (h.inj.inj_on _).mem_image_iff (set.subset_univ _) trivial, exact hV hx },
  { rw h.is_compact_iff_is_compact_image,
    convert hV'',
    rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset],
    exact hV.trans (set.image_subset_range _ _) }
end

lemma open_embedding.is_quasi_separated_iff (h : open_embedding f) {s : set α} :
  is_quasi_separated s ↔ is_quasi_separated (f '' s) :=
begin
  refine ⟨λ hs, hs.image_of_embedding h.to_embedding, _⟩,
  intros H U V hU hU' hU'' hV hV' hV'',
  rw [h.to_embedding.is_compact_iff_is_compact_image, set.image_inter h.inj],
  exact H (f '' U) (f '' V)
    (set.image_subset _ hU) (h.is_open_map _ hU') (hU''.image h.continuous)
    (set.image_subset _ hV) (h.is_open_map _ hV') (hV''.image h.continuous)
end

lemma is_quasi_separated_iff_quasi_separated_space (s : set α) (hs : is_open s) :
  is_quasi_separated s ↔ quasi_separated_space s :=
begin
  rw ← is_quasi_separated_univ_iff,
  convert hs.open_embedding_subtype_coe.is_quasi_separated_iff.symm; simp
end

lemma is_quasi_separated.of_subset {s t : set α} (ht : is_quasi_separated t) (h : s ⊆ t) :
  is_quasi_separated s :=
begin
  intros U V hU hU' hU'' hV hV' hV'',
  exact ht U V (hU.trans h) hU' hU'' (hV.trans h) hV' hV'',
end

@[priority 100]
instance t2_space.to_quasi_separated_space [t2_space α] : quasi_separated_space α :=
⟨λ U V hU hU' hV hV', hU'.inter hV'⟩

@[priority 100]
instance noetherian_space.to_quasi_separated_space [noetherian_space α] :
  quasi_separated_space α :=
⟨λ _ _ _ _ _ _, noetherian_space.is_compact _⟩

lemma is_quasi_separated.of_quasi_separated_space (s : set α) [quasi_separated_space α] :
  is_quasi_separated s :=
is_quasi_separated_univ.of_subset (set.subset_univ _)

lemma quasi_separated_space.of_open_embedding (h : open_embedding f) [quasi_separated_space β] :
  quasi_separated_space α :=
is_quasi_separated_univ_iff.mp
  (h.is_quasi_separated_iff.mpr $ is_quasi_separated.of_quasi_separated_space _)
