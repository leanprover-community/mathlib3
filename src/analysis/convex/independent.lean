/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.caratheodory
import analysis.convex.extreme
import linear_algebra.affine_space.independent

/-!
# Convex independence

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `convex_independent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convex_independent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `convex.extreme_points_convex_independent`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `affine_independent.convex_independent`. This requires some glue between `affine_combination`
and `finset.center_mass`.

## Tags

independence, convex position
-/

open_locale affine big_operators classical
open finset function
variables {𝕜 E ι : Type*}

section ordered_semiring
variables (𝕜) [ordered_semiring 𝕜] [add_comm_group E] [module 𝕜 E] {s t : set E}

/-- An indexed family is said to be convex independent if every point only belongs to convex hulls
of sets containing it. -/
def convex_independent (p : ι → E) : Prop :=
∀ (s : set ι) (x : ι), p x ∈ convex_hull 𝕜 (p '' s) → x ∈ s

variables {𝕜}

/-- A family with at most one point is convex independent. -/
lemma subsingleton.convex_independent [subsingleton ι] (p : ι → E) :
  convex_independent 𝕜 p :=
λ s x hx, begin
  have : (convex_hull 𝕜 (p '' s)).nonempty := ⟨p x, hx⟩,
  rw [convex_hull_nonempty_iff, set.nonempty_image_iff] at this,
  rwa subsingleton.mem_iff_nonempty,
end

/-- A convex independent family is injective. -/
protected lemma convex_independent.injective {p : ι → E} (hc : convex_independent 𝕜 p) :
  function.injective p :=
begin
  refine λ i j hij, hc {j} i _,
  rw [hij, set.image_singleton, convex_hull_singleton],
  exact set.mem_singleton _,
end

/-- If a family is convex independent, so is any subfamily given by composition of an embedding into
index type with the original family. -/
lemma convex_independent.comp_embedding {ι' : Type*} (f : ι' ↪ ι) {p : ι → E}
  (hc : convex_independent 𝕜 p) :
  convex_independent 𝕜 (p ∘ f) :=
begin
  intros s x hx,
  rw ←f.injective.mem_set_image,
  exact hc _ _ (by rwa set.image_image),
end

/-- If a family is convex independent, so is any subfamily indexed by a subtype of the index type.
-/
protected lemma convex_independent.subtype {p : ι → E} (hc : convex_independent 𝕜 p) (s : set ι) :
  convex_independent 𝕜 (λ i : s, p i) :=
hc.comp_embedding (embedding.subtype _)

/-- If an indexed family of points is convex independent, so is the corresponding set of points. -/
protected lemma convex_independent.range {p : ι → E} (hc : convex_independent 𝕜 p) :
  convex_independent 𝕜 (λ x, x : set.range p → E) :=
begin
  let f : set.range p → ι := λ x, x.property.some,
  have hf : ∀ x, p (f x) = x := λ x, x.property.some_spec,
  let fe : set.range p ↪ ι := ⟨f, λ x₁ x₂ he, subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩,
  convert hc.comp_embedding fe,
  ext,
  rw [embedding.coe_fn_mk, comp_app, hf],
end

/-- A subset of a convex independent set of points is convex independent as well. -/
protected lemma convex_independent.mono {s t : set E} (hc : convex_independent 𝕜 (λ x, x : t → E))
  (hs : s ⊆ t) :
  convex_independent 𝕜 (λ x, x : s → E) :=
hc.comp_embedding (s.embedding_of_subset t hs)

/-- The range of an injective indexed family of points is convex independent iff that family is. -/
lemma function.injective.convex_independent_iff_set {p : ι → E}
  (hi : function.injective p) :
  convex_independent 𝕜 (λ x, x : set.range p → E) ↔ convex_independent 𝕜 p :=
⟨λ hc, hc.comp_embedding
  (⟨λ i, ⟨p i, set.mem_range_self _⟩, λ x y h, hi (subtype.mk_eq_mk.1 h)⟩ : ι ↪ set.range p),
  convex_independent.range⟩

/-- If a family is convex independent, a point in the family is in the convex hull of some of the
points given by a subset of the index type if and only if the point's index is in this subset. -/
@[simp] protected lemma convex_independent.mem_convex_hull_iff {p : ι → E}
    (hc : convex_independent 𝕜 p) (s : set ι) (i : ι) :
  p i ∈ convex_hull 𝕜 (p '' s) ↔ i ∈ s :=
⟨hc _ _, λ hi, subset_convex_hull 𝕜 _ (set.mem_image_of_mem p hi)⟩

/-- If a family is convex independent, a point in the family is not in the convex hull of the other
points. See `convex_independent_set_iff_not_mem_convex_hull_diff` for the `set` version.  -/
lemma convex_independent_iff_not_mem_convex_hull_diff {p : ι → E} :
  convex_independent 𝕜 p ↔ ∀ i s, p i ∉ convex_hull 𝕜 (p '' (s \ {i})) :=
begin
  refine ⟨λ hc i s h, _, λ h s i hi, _⟩,
  { rw hc.mem_convex_hull_iff at h,
    exact h.2 (set.mem_singleton _) },
  { by_contra H,
    refine h i s _,
    rw set.diff_singleton_eq_self H,
    exact hi }
end

lemma convex_independent_set_iff_inter_convex_hull_subset {s : set E} :
  convex_independent 𝕜 (λ x, x : s → E) ↔ ∀ t, t ⊆ s → s ∩ convex_hull 𝕜 t ⊆ t :=
begin
  split,
  { rintro hc t h x ⟨hxs, hxt⟩,
    refine hc {x | ↑x ∈ t} ⟨x, hxs⟩ _,
    rw subtype.coe_image_of_subset h,
    exact hxt },
  { intros hc t x h,
    rw ←subtype.coe_injective.mem_set_image,
    exact hc (t.image coe) (subtype.coe_image_subset s t) ⟨x.prop, h⟩ }
end

/-- If a set is convex independent, a point in the set is not in the convex hull of the other
points. See `convex_independent_iff_not_mem_convex_hull_diff` for the indexed family version.  -/
lemma convex_independent_set_iff_not_mem_convex_hull_diff {s : set E} :
  convex_independent 𝕜 (λ x, x : s → E) ↔ ∀ x ∈ s, x ∉ convex_hull 𝕜 (s \ {x}) :=
begin
  rw convex_independent_set_iff_inter_convex_hull_subset,
  split,
  { rintro hs x hxs hx,
    exact (hs _ (set.diff_subset _ _) ⟨hxs, hx⟩).2 (set.mem_singleton _) },
  { rintro hs t ht x ⟨hxs, hxt⟩,
    by_contra h,
    exact hs _ hxs (convex_hull_mono (set.subset_diff_singleton ht h) hxt) }
end

end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {s : set E}

/-- To check convex independence, one only has to check finsets thanks to Carathéodory's theorem. -/
lemma convex_independent_iff_finset {p : ι → E} :
  convex_independent 𝕜 p
  ↔ ∀ (s : finset ι) (x : ι), p x ∈ convex_hull 𝕜 (s.image p : set E) → x ∈ s :=
begin
  refine ⟨λ hc s x hx, hc s x _, λ h s x hx, _⟩,
  { rwa finset.coe_image at hx },
  have hp : injective p,
  { rintro a b hab,
    rw ←mem_singleton,
    refine h {b} a _,
    rw [hab, image_singleton, coe_singleton, convex_hull_singleton],
    exact set.mem_singleton _ },
  let s' : finset ι :=
    (caratheodory.min_card_finset_of_mem_convex_hull hx).preimage p (hp.inj_on _),
  suffices hs' : x ∈ s',
  { rw ←hp.mem_set_image,
    rw [finset.mem_preimage, ←mem_coe] at hs',
    exact caratheodory.min_card_finset_of_mem_convex_hull_subseteq hx hs' },
  refine h s' x _,
  have : s'.image p = caratheodory.min_card_finset_of_mem_convex_hull hx,
  { rw [image_preimage, filter_true_of_mem],
    exact λ y hy, set.image_subset_range _ s
      (caratheodory.min_card_finset_of_mem_convex_hull_subseteq hx $ mem_coe.2 hy) },
  rw this,
  exact caratheodory.mem_min_card_finset_of_mem_convex_hull hx,
end

/-! ### Extreme points -/

lemma convex.convex_independent_extreme_points (hs : convex 𝕜 s) :
  convex_independent 𝕜 (λ p, p : s.extreme_points 𝕜 → E) :=
convex_independent_set_iff_not_mem_convex_hull_diff.2 $ λ x hx h,
  (extreme_points_convex_hull_subset
  (inter_extreme_points_subset_extreme_points_of_subset (convex_hull_min
  ((set.diff_subset _ _).trans extreme_points_subset) hs) ⟨h, hx⟩)).2 (set.mem_singleton _)

end linear_ordered_field
