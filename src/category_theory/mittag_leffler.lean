/-
Copyright (c) 2022 Rémi Bottinelli, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu
-/
import category_theory.filtered
import data.set.finite

/-!
# The Mittag-Leffler condition

This files defines the Mittag-Leffler condition for cofiltered systems and (TODO) other properties
of such systems and their sections.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventual_range j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.is_mittag_leffler` states that the functor `F` satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.to_eventual_ranges` is the subfunctor of `F` obtained by restriction
  to `F.eventual_range`.
* `F.to_preimages` restricts a functor to preimages of a given set in some `F.obj i`. If `J` is
  cofiltered, then it is Mittag-Leffler if `F` is, see `is_mittag_leffler.to_preimages`.

## Main statements

* `is_mittag_leffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `to_eventual_ranges_surjective` shows that if `F` is Mittag-Leffler, then `F.to_eventual_ranges`
  has all morphisms `F.map f` surjective.

## Todo

* Specialize to inverse systems and fintype systems.
* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/

universes u v

namespace category_theory
namespace functor

open is_cofiltered set functor_to_types

variables {J : Type u} [category J] (F : J ⥤ Type v) {i j k : J} (s : set (F.obj i))

/--
The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventual_range (j : J) := ⋂ i (f : i ⟶ j), range (F.map f)

lemma mem_eventual_range_iff {x : F.obj j} :
  x ∈ F.eventual_range j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) := mem_Inter₂

/--
The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `is_mittag_leffler_iff_eventual_range`), the eventual range at `j` is attained
by some `f : i ⟶ j`.
-/
def is_mittag_leffler : Prop :=
∀ j : J, ∃ i (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)

lemma is_mittag_leffler_iff_eventual_range : F.is_mittag_leffler ↔
  ∀ j : J, ∃ i (f : i ⟶ j), F.eventual_range j = range (F.map f) :=
forall_congr $ λ j, exists₂_congr $ λ i f,
  ⟨λ h, (Inter₂_subset _ _).antisymm $ subset_Inter₂ h, λ h, h ▸ Inter₂_subset⟩

lemma is_mittag_leffler.subset_image_eventual_range (h : F.is_mittag_leffler) (f : j ⟶ i) :
  F.eventual_range i ⊆ F.map f '' (F.eventual_range j) :=
begin
  obtain ⟨k, g, hg⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j,
  rw hg, intros x hx,
  obtain ⟨x, rfl⟩ := F.mem_eventual_range_iff.1 hx (g ≫ f),
  refine ⟨_, ⟨x, rfl⟩, by simpa only [F.map_comp]⟩,
end

lemma eventual_range_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
  (h : F.eventual_range k = range (F.map g)) :
  F.eventual_range k = range (F.map $ f ≫ g) :=
begin
  apply subset_antisymm,
  { apply Inter₂_subset, },
  { rw [h, F.map_comp], apply range_comp_subset_range, }
end

lemma is_mittag_leffler_of_surjective
  (h : ∀ (i j : J) (f : i ⟶ j), (F.map f).surjective) : F.is_mittag_leffler :=
λ j, ⟨j, 𝟙 j, λ k g, by rw [map_id, types_id, range_id, (h k j g).range_eq]⟩

/-- The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.obj i`. -/
@[simps] def to_preimages : J ⥤ Type v :=
{ obj := λ j, ⋂ f : j ⟶ i, F.map f ⁻¹' s,
  map := λ j k g, maps_to.restrict (F.map g) _ _ $ λ x h, begin
    rw [mem_Inter] at h ⊢, intro f,
    rw [← mem_preimage, preimage_preimage],
    convert h (g ≫ f), rw F.map_comp, refl,
  end,
  map_id' := λ j, by { simp_rw F.map_id, ext, refl },
  map_comp' := λ j k l f g, by { simp_rw F.map_comp, refl } }

variable [is_cofiltered_or_empty J]

lemma eventual_range_maps_to (f : j ⟶ i) :
  (F.eventual_range j).maps_to (F.map f) (F.eventual_range i) :=
λ x hx, begin
  rw mem_eventual_range_iff at hx ⊢,
  intros k f',
  obtain ⟨l, g, g', he⟩ := cospan f f',
  obtain ⟨x, rfl⟩ := hx g,
  rw [← map_comp_apply, he, F.map_comp],
  exact ⟨_, rfl⟩,
end

lemma is_mittag_leffler.eq_image_eventual_range (h : F.is_mittag_leffler) (f : j ⟶ i) :
  F.eventual_range i = F.map f '' (F.eventual_range j) :=
(h.subset_image_eventual_range F f).antisymm $ maps_to'.1 (F.eventual_range_maps_to f)

lemma eventual_range_eq_iff {f : i ⟶ j} :
  F.eventual_range j = range (F.map f) ↔
  ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map $ g ≫ f) :=
begin
  rw [subset_antisymm_iff, eventual_range, and_iff_right (Inter₂_subset _ _), subset_Inter₂_iff],
  refine ⟨λ h k g, h _ _, λ h j' f', _⟩,
  obtain ⟨k, g, g', he⟩ := cospan f f',
  refine (h g).trans _,
  rw [he, F.map_comp],
  apply range_comp_subset_range,
end

lemma is_mittag_leffler_iff_subset_range_comp : F.is_mittag_leffler ↔
  ∀ j : J, ∃ i (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map $ g ≫ f) :=
by simp_rw [is_mittag_leffler_iff_eventual_range, eventual_range_eq_iff]

lemma is_mittag_leffler.to_preimages (h : F.is_mittag_leffler) :
  (F.to_preimages s).is_mittag_leffler :=
(is_mittag_leffler_iff_subset_range_comp _).2 $ λ j, begin
  obtain ⟨j₁, g₁, f₁, -⟩ := cone_objs i j,
  obtain ⟨j₂, f₂, h₂⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j₁,
  refine ⟨j₂, f₂ ≫ f₁, λ j₃ f₃, _⟩,
  rintro _ ⟨⟨x, hx⟩, rfl⟩,
  have : F.map f₂ x ∈ F.eventual_range j₁, { rw h₂, exact ⟨_, rfl⟩ },
  obtain ⟨y, hy, h₃⟩ := h.subset_image_eventual_range F (f₃ ≫ f₂) this,
  refine ⟨⟨y, mem_Inter.2 $ λ g₂, _⟩, subtype.ext _⟩,
  { obtain ⟨j₄, f₄, h₄⟩ := cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁),
    obtain ⟨y, rfl⟩ := F.mem_eventual_range_iff.1 hy f₄,
    rw ← map_comp_apply at h₃,
    rw [mem_preimage, ← map_comp_apply, h₄, ← category.assoc, map_comp_apply, h₃, ← map_comp_apply],
    apply mem_Inter.1 hx },
  { simp_rw [to_preimages_map, maps_to.coe_restrict_apply, subtype.coe_mk],
    rw [← category.assoc, map_comp_apply, h₃, map_comp_apply] },
end

lemma is_mittag_leffler_of_exists_finite_range
  (h : ∀ (j : J), ∃ i (f : i ⟶ j), (range $ F.map f).finite) :
  F.is_mittag_leffler :=
λ j, begin
  obtain ⟨i, hi, hf⟩ := h j,
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := finset.is_well_founded_lt.wf.has_min
    {s : finset (F.obj j) | ∃ i (f : i ⟶ j), ↑s = range (F.map f)} ⟨_, i, hi, hf.coe_to_finset⟩,
  refine ⟨i, f, λ k g,
    (directed_on_range.mp $ F.ranges_directed j).is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ _ _ ⟨⟨k, g⟩, rfl⟩⟩,
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl,
  refine (eq_of_le_of_not_lt hl _).ge,
  have := hmin _ ⟨k', g', (m.finite_to_set.subset $ hm.substr hl).coe_to_finset⟩,
  rwa [finset.lt_iff_ssubset, ← finset.coe_ssubset, set.finite.coe_to_finset, hm] at this,
end

/--
The subfunctor of `F` obtained by restricting to the eventual range at each index.
-/
@[simps] def to_eventual_ranges : J ⥤ Type v :=
{ obj := λ j, F.eventual_range j,
  map := λ i j f, (F.eventual_range_maps_to f).restrict _ _ _,
  map_id' := λ i, by { simp_rw F.map_id, ext, refl },
  map_comp' := λ _ _ _ _ _, by { simp_rw F.map_comp, refl } }

/--
The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.eventual_ranges`.
-/
def to_eventual_ranges_sections_equiv : F.to_eventual_ranges.sections ≃ F.sections :=
{ to_fun := λ s, ⟨_, λ i j f, subtype.coe_inj.2 $ s.prop f⟩,
  inv_fun := λ s, ⟨λ j, ⟨_, mem_Inter₂.2 $ λ i f, ⟨_, s.prop f⟩⟩, λ i j f, subtype.ext $ s.prop f⟩,
  left_inv := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl } }

/--
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a surjective
functor.
-/
lemma surjective_to_eventual_ranges (h : F.is_mittag_leffler) (f : i ⟶ j) :
  (F.to_eventual_ranges.map f).surjective :=
λ ⟨x, hx⟩, by { obtain ⟨y, hy, rfl⟩ := h.subset_image_eventual_range F f hx, exact ⟨⟨y, hy⟩, rfl⟩ }

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.to_eventual_ranges`. -/
lemma to_eventual_ranges_nonempty (h : F.is_mittag_leffler) [∀ (j : J), nonempty (F.obj j)]
  (j : J) : nonempty (F.to_eventual_ranges.obj j) :=
let ⟨i, f, h⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j in
by { rw [to_eventual_ranges_obj, h], apply_instance }

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
lemma thin_diagram_of_surjective (Fsur : ∀ (i j : J) (f : i ⟶ j), (F.map f).surjective)
  (i j) (f g : i ⟶ j) : F.map f = F.map g :=
let ⟨k, φ, hφ⟩ := cone_maps f g in
(Fsur k i φ).injective_comp_right $ by simp_rw [← types_comp, ← F.map_comp, hφ]

end functor
end category_theory
