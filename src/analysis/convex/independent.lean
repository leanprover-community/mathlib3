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

## Main declarations

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Once convexity is generalised to affine spaces, `convex_independent` will take as first parameter
the ring of scalars, so that `convex_independent p` becomes `convex_independent k p`, mimicking
`affine_independent k p`. Our current definition would then correspond to `convex_independent ℝ p`.

## Tags

independence, convex position
-/

open_locale affine big_operators classical
open finset function

@[simp] lemma set.mem_iff_nonempty_of_subsingleton {α : Type*} [subsingleton α] {s : set α}
  {x : α} :
  x ∈ s ↔ s.nonempty :=
begin
  refine ⟨λ hx, ⟨x, hx⟩, _⟩,
  rintro ⟨y, hy⟩,
  rwa subsingleton.elim x y,
end

lemma subtype.coe_subset_eq {α : Type*} {s t : set α} (h : t ⊆ s) : coe '' {x : ↥s | ↑x ∈ t} = t :=
begin
  ext x,
  rw set.mem_image,
  exact ⟨λ ⟨x', hx', hx⟩, hx ▸ hx', λ hx, ⟨⟨x, h hx⟩, hx, rfl⟩⟩,
end

lemma function.injective.mem_finset_image_iff {α β : Type*} {f : α → β} (hf : function.injective f)
  {s : finset α} {x : α} :
  f x ∈ s.image f ↔ x ∈ s :=
begin
  refine ⟨λ h, _, finset.mem_image_of_mem f⟩,
  rw mem_image at h,
  obtain ⟨y, hy, h⟩ := h,
  exact hf h ▸ hy,
end

section
variables {k : Type*} {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space V P] {ι : Type*}
include V

lemma affine_independent.indicator_eq_of_affine_combination_eq {p : ι → P}
  (ha : affine_independent k p) (s₁ s₂ : finset ι) (w₁ w₂ : ι → k) (hw₁ : ∑ i in s₁, w₁ i = 1)
  (hw₂ : ∑ i in s₂, w₂ i = 1) (h : s₁.affine_combination p w₁ = s₂.affine_combination p w₂) :
  set.indicator ↑s₁ w₁ = set.indicator ↑s₂ w₂ :=
(affine_independent_iff_indicator_eq_of_affine_combination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

end


variables {V : Type*} [add_comm_group V] [module ℝ V]
          {ι : Type*} {s t : set V}

/-- An indexed family is said to be convex independent if every point only belongs to convex hulls
of sets containing it. -/
def convex_independent (p : ι → V) : Prop :=
∀ (s : set ι) (x : ι), p x ∈ convex_hull (p '' s) → x ∈ s

/-- A family with at most one point is affinely independent. -/
lemma convex_independent_of_subsingleton [subsingleton ι] (p : ι → V) :
  convex_independent p :=
λ s x hx, begin
  have : (convex_hull (p '' s)).nonempty := ⟨p x, hx⟩,
  rw [convex_hull_nonempty_iff, set.nonempty_image_iff] at this,
  rwa set.mem_iff_nonempty_of_subsingleton,
end

lemma convex_independent_iff_finset (p : ι → V) :
  convex_independent p ↔ ∀ (s : finset ι) (x : ι), p x ∈ convex_hull (s.image p : set V) → x ∈ s :=
begin
  split,
  { refine λ hc s x hx, hc s x _,
    rwa finset.coe_image at hx },
  refine λ h s x hx,  _,
  sorry --use Carathéodory
  --have := convex_hull_subset_union _ hx,
end

--variables {k}

/-- A convex independent family is injective. -/
--[nontrivial k]
protected lemma convex_independent.injective {p : ι → V} (hc : convex_independent p) :
  function.injective p :=
begin
  refine λ i j hij, hc {j} i _,
  rw [hij, set.image_singleton, convex_hull_singleton],
  exact set.mem_singleton _,
end

/-- If a family is convex independent, so is any subfamily given by composition of an embedding into
index type with the original family. -/
lemma convex_independent.comp_embedding {ι' : Type*} (f : ι' ↪ ι) {p : ι → V}
    (hc : convex_independent p) : convex_independent (p ∘ f) :=
begin
  intros s x hx,
  rw ←set.mem_image_of_injective f.injective,
  exact hc _ _ (by rwa set.image_image),
end

/-- If a family is convex independent, so is any subfamily indexed by a subtype of the index type.
-/
protected lemma convex_independent.subtype {p : ι → V} (hc : convex_independent p) (s : set ι) :
  convex_independent (λ i : s, p i) :=
hc.comp_embedding (embedding.subtype _)

/-- If an indexed family of points is convex independent, so is the corresponding set of points. -/
protected lemma convex_independent.range {p : ι → V} (hc : convex_independent p) :
  convex_independent (λ x, x : set.range p → V) :=
begin
  let f : set.range p → ι := λ x, x.property.some,
  have hf : ∀ x, p (f x) = x := λ x, x.property.some_spec,
  let fe : set.range p ↪ ι := ⟨f, λ x₁ x₂ he, subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩,
  convert hc.comp_embedding fe,
  ext,
  rw [embedding.coe_fn_mk, comp_app, hf],
end

/-- A subset of a convex independent set of points is convex independent as well, so is any subset. -/
protected lemma convex_independent.mono {s t : set V} (hc : convex_independent (λ x, x : t → V))
  (hs : s ⊆ t) :
  convex_independent (λ x, x : s → V) :=
hc.comp_embedding (s.embedding_of_subset t hs)

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
lemma function.injective.convex_independent_iff_set {p : ι → V}
  (hi : function.injective p) :
  convex_independent (λ x, x : set.range p → V) ↔ convex_independent p :=
⟨λ hc, hc.comp_embedding
  (⟨λ i, ⟨p i, set.mem_range_self _⟩, λ x y h, hi (subtype.mk_eq_mk.1 h)⟩ : ι ↪ set.range p),
  convex_independent.range⟩

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp] protected lemma convex_independent.mem_convex_hull_iff {p : ι → V}
    (hc : convex_independent p) (s : set ι) (i : ι) :
  p i ∈ convex_hull (p '' s) ↔ i ∈ s :=
⟨hc _ _, λ hi, subset_convex_hull  _ (set.mem_image_of_mem p hi)⟩

/-- If a family is affinely independent, a point in the family is not
in the convex hull of the other points -/
lemma convex_independent.not_mem_convex_hull_diff {p : ι → V}
    (hc : convex_independent p) (i : ι) (s : set ι) :
  p i ∉ convex_hull (p '' (s \ {i})) :=
begin
  rw hc.mem_convex_hull_iff,
  exact λ h, h.2 (set.mem_singleton _),
end

lemma convex_independent_set_iff_inter_convex_hull_subset (s : set V) :
  convex_independent (λ x, x : s → V) ↔ ∀ t, t ⊆ s → s ∩ convex_hull t ⊆ t :=
begin
  split,
  { rintro hc t h x ⟨hxs, hxt⟩,
    refine hc {x | ↑x ∈ t} ⟨x, hxs⟩ _,
    rw subtype.coe_subset_eq h,
    exact hxt },
  { intros hc t x h,
    rw ←set.mem_image_of_injective subtype.coe_injective,
    exact hc (t.image coe) (subtype.coe_image_subset s t) ⟨x.prop, h⟩ }
end

lemma convex_independent_set_iff_not_mem_convex_hull_erase (s : set V) :
  convex_independent (λ x, x : s → V) ↔ ∀ x ∈ s, x ∉ convex_hull (s \ {x}) :=
begin
  rw convex_independent_set_iff_inter_convex_hull_subset,
  split,
  { rintro hs x hxs hx,
    exact (hs _ (set.diff_subset _ _) ⟨hxs, hx⟩).2 (set.mem_singleton _) },
  { rintro hs t ht x ⟨hxs, hxt⟩,
    by_contra h,
    exact hs _ hxs (convex_hull_mono (set.subset_diff_singleton ht h) hxt) }
end

lemma affine_independent.convex_independent {p : ι → V} (ha : affine_independent ℝ p) :
  convex_independent p :=
begin
  rw convex_independent_iff_finset,
  intros s x hx,
  rw finset.convex_hull_eq at hx,
  obtain ⟨w, _, hw, hx⟩ := hx,
  rw ←finset.mem_coe,
  suffices h : (s : set ι).indicator (w ∘ p) x ≠ 0,
  { exact set.mem_of_indicator_ne_zero h },
  --rw ←ha.injective.mem_finset_image_iff,
  rw finset.sum_image (ha.injective.inj_on _) at hw,
  rw [ha.indicator_eq_of_affine_combination_eq s {x} (w ∘ p) 1 hw finset.sum_singleton _,
    finset.coe_singleton, set.indicator_of_mem (set.mem_singleton _)],
  exact one_ne_zero,
  sorry,
end

/-- Two different points are convex independent. -/
lemma convex_independent_of_ne {p₁ p₂ : V} (h : p₁ ≠ p₂) : convex_independent ![p₁, p₂] :=
(affine_independent_of_ne ℝ h).convex_independent

/-! ### Extreme points -/

lemma convex.extreme_points_convex_independent (hs : convex s) :
  convex_independent (λ p, p : s.extreme_points → V) :=
(convex_independent_set_iff_not_mem_convex_hull_erase _).2 $ λ x hx h,
  (extreme_points_convex_hull_subset
  (inter_extreme_points_subset_extreme_points_of_subset (convex_hull_min
  ((set.diff_subset _ _).trans extreme_points_subset) hs) ⟨h, hx⟩)).2 (set.mem_singleton _)
