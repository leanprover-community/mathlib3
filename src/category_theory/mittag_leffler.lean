/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.filtered
import data.set.finite

/-!
# Mittag Leffler

This files defines the Mittag-Leffler condition for cofiltered systems and (TODO) other properties
of such systems and their sections.

## Main definitions

Given the functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventual_range j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `is_mittag_leffler` states that the functor `F : J → Type v`, satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.to_eventual_ranges` is the subfunctor of `F` obtained by restriction
  to `F.eventual_range`.


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

universes u v w

namespace category_theory
namespace functor

variables {J : Type u} [category J] (F : J ⥤ Type v)

/--
The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventual_range (j : J) := ⋂ (i : J) (f : i ⟶ j), set.range (F.map f)

/--
The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `is_mittag_leffler_iff_eventual_range`), the eventual range at `j` is attained
by some `f : i ⟶ j`.
-/
def is_mittag_leffler :=
∀ (j : J), ∃ (i) (f : i ⟶ j), ∀ (k) (g : k ⟶ j), set.range (F.map f) ⊆ set.range (F.map g)

lemma is_mittag_leffler_iff_eventual_range :
  F.is_mittag_leffler ↔ ∀ (j : J), ∃ (i) (f : i ⟶ j), F.eventual_range j = set.range (F.map f) :=
begin
  refine forall_congr (λ j, exists_congr $ λ i, exists_congr $ λ f, _),
  split,
  { rintro h, apply subset_antisymm,
    { apply set.Inter₂_subset, },
    { apply set.subset_Inter₂,
      exact λ k g, h k g, }, },
  { rintro h k g, rw h.symm,
    apply set.Inter₂_subset, },
end

lemma eventual_range_eq_range_precomp
  {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (h : F.eventual_range k = set.range (F.map g)) :
  F.eventual_range k = (set.range (F.map $ f ≫ g)) :=
begin
  apply subset_antisymm,
  { apply set.Inter₂_subset, },
  { simp only [h, types_comp, functor.map_comp], apply set.range_comp_subset_range, }
end

lemma is_mittag_leffler_of_surjective
  (h : (∀ (i j : J) (f : i ⟶ j), (F.map f).surjective)) : F.is_mittag_leffler :=
begin
  refine λ j, ⟨j, 𝟙 j, λ k g, subset_of_eq _⟩,
  simp only [map_id, types_id, set.range_id],
  exact (set.range_iff_surjective.mpr $ h k j g).symm,
end

variables [is_cofiltered J]

lemma is_mittag_leffler_of_exists_finite_range
  (h : ∀ (j : J), ∃ i (f : i ⟶ j), (set.range (F.map f)).finite ) :
  F.is_mittag_leffler :=
begin
  rintro j,
  suffices : ∃ (f : Σ' i, i ⟶ j), ∀ (f' : Σ' i, i ⟶ j),
               set.range (F.map f'.2) ≤ set.range (F.map f.2) →
                 set.range (F.map f'.2) = set.range (F.map f.2),
  { obtain ⟨⟨i, f⟩, fmin⟩ := this,
    refine ⟨i, f, λ i' f', _⟩,
    refine min_of_ge_directed_on (is_cofiltered.ranges_directed F j)
                                          _ ⟨⟨i, f⟩, rfl⟩ _ _ ⟨⟨i', f'⟩, rfl⟩,
    simp only [set.mem_range, psigma.exists, forall_exists_index],
    rintro _ k g rfl gf,
    exact fmin ⟨k, g⟩ gf, },

  let fins := subtype { f : Σ' i, i ⟶ j | (set.range (F.map f.2)).finite },
  haveI : nonempty fins := by { obtain ⟨i, f, fin⟩ := h j, exact ⟨⟨⟨i, f⟩, fin⟩⟩, },
  let fmin := function.argmin (λ (f : fins), f.prop.to_finset.card) nat.lt_wf,
  use fmin.val,
  rintro g gf,
  cases lt_or_eq_of_le gf with h',
  { have gfin : (set.range (F.map g.2)).finite := fmin.prop.subset gf,
    refine ((λ (f : fins), f.prop.to_finset.card).not_lt_argmin nat.lt_wf ⟨g, gfin⟩ _).elim,
    exact finset.card_lt_card (set.finite.to_finset_ssubset.mpr h'), },
  { assumption, },
end

/--
The subfunctor of `F` obtained by restricting to the eventual range at each index.
-/
def to_eventual_ranges : J ⥤ Type v :=
{ obj := λ j, F.eventual_range j,
  map := λ i j f, set.maps_to.restrict (F.map f) _ _ (
    begin
      rintro x h,
      simp only [eventual_range, set.mem_Inter, set.mem_range] at h ⊢,
      rintro i' f',
      obtain ⟨l, g, g', e⟩ := category_theory.is_cofiltered.cone_over_cospan f f',
      obtain ⟨z, rfl⟩ := h l g,
      use F.map g' z,
      replace e := congr_fun (congr_arg F.map e) z,
      simp_rw functor_to_types.map_comp_apply at e,
      exact e.symm,
    end ),
 map_id' := λ i, by {simp only [map_id], apply subtype.map_id, },
 map_comp' := λ _ _ _ _ _, by {funext, simp only [map_comp], symmetry, apply subtype.map_comp, } }


/--
The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.eventual_ranges`.
-/
def to_eventual_ranges_sections_equiv :
  F.to_eventual_ranges.sections ≃ F.sections :=
{ to_fun := λ ss,
    ⟨ λ j, (ss.val j).val,
      λ i j f, by simpa only [←subtype.coe_inj, subtype.coe_mk] using ss.prop f ⟩,
  inv_fun := λ s,
    ⟨ λ j,
      ⟨ s.val j, by
        { dsimp [eventual_range],
          simp only [set.mem_Inter, set.mem_range],
          exact λ i f, ⟨s.val i, s.prop f⟩, } ⟩,
      λ i j ij, subtype.mk_eq_mk.mpr (s.prop ij)⟩,
  left_inv := by
    simp only [function.right_inverse, function.left_inverse, subtype.val_eq_coe, set_coe.forall,
               subtype.coe_mk, subtype.coe_eta, eq_self_iff_true, implies_true_iff],
  right_inv := by
    simp only [function.left_inverse, function.right_inverse, eq_self_iff_true, set_coe.forall,
               implies_true_iff, subtype.coe_mk] }

/--
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a surjective
functor.
-/
lemma to_eventual_ranges_surjective (ml : F.is_mittag_leffler) :
  ∀ (i j : J) (f : i ⟶ j), (F.to_eventual_ranges.map f).surjective :=
begin
  rintros i j f ⟨x, hx⟩,
  rw is_mittag_leffler_iff_eventual_range at ml,
  dsimp only [to_eventual_ranges],
  simp only [set_coe.exists],
  obtain ⟨i₀, ii₀, ei₀⟩ := ml i,
  obtain ⟨j₀, jj₀, ej₀⟩ := ml j,
  obtain ⟨k, ki₀, kj₀, e⟩ := category_theory.is_cofiltered.cone_over_cospan (ii₀ ≫ f) jj₀,
  let ei := F.eventual_range_eq_range_precomp ki₀ ii₀ ei₀,
  let ej := F.eventual_range_eq_range_precomp kj₀ jj₀ ej₀,
  obtain ⟨z, rfl⟩ := ej.rec_on hx,
  use F.map (ki₀ ≫ ii₀) z,
  simp_rw [ei, set.mem_range_self, exists_true_left, ←e, functor_to_types.map_comp_apply],
  refl,
end

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
lemma thin_diagram_of_surjective (Fsur : ∀ (i j : J) (f : i ⟶ j), (F.map f).surjective) :
  ∀ i j (f g : i ⟶ j), F.map f = F.map g :=
begin
  rintro i j f g,
  let φ := is_cofiltered.eq_hom f g,
  suffices : F.map φ ≫ F.map f = F.map φ ≫ F.map g,
  { let φs := Fsur _ _ φ,
    rw ←category_theory.epi_iff_surjective at φs,
    exact φs.left_cancellation _ _ this, },
  simp_rw [←map_comp, is_cofiltered.eq_condition],
end

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.to_eventual_ranges`. -/
lemma to_eventual_ranges_nonempty (ml : F.is_mittag_leffler) [∀ (j : J), nonempty (F.obj j)] :
  ∀ (j : J), nonempty (F.to_eventual_ranges.obj j) :=
begin
  intro j,
  rw is_mittag_leffler_iff_eventual_range at ml,
  obtain ⟨i,f,h⟩ := ml j,
  dsimp [to_eventual_ranges], rw h,
  apply set.nonempty.to_subtype,
  apply set.range_nonempty,
end

end functor
end category_theory
