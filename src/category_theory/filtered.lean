/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import category_theory.fin_category
import category_theory.limits.cones
import category_theory.adjunction.basic
import category_theory.category.preorder
import category_theory.category.ulift

/-!
# Filtered categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

Filtered colimits are often better behaved than arbitrary colimits.
See `category_theory/limits/types` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and more often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [fin_category J] [is_filtered C] (F : J ⥤ C) : nonempty (cocone F)`
More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice and is available via `sup_exists`,
which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

Furthermore, we give special support for two diagram categories: The `bowtie` and the `tulip`.
This is because these shapes show up in the proofs that forgetful functors of algebraic categories
(e.g. `Mon`, `CommRing`, ...) preserve filtered colimits.

All of the above API, except for the `bowtie` and the `tulip`, is also provided for cofiltered
categories.

## See also
In `category_theory.limits.filtered_colimit_commutes_finite_limit` we show that filtered colimits
commute with finite limits.

-/

open function

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes w v v₁ u u₁ u₂

namespace category_theory

variables (C : Type u) [category.{v} C]

/--
A category `is_filtered_or_empty` if
1. for every pair of objects there exists another object "to the right", and
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal.
-/
class is_filtered_or_empty : Prop :=
(cocone_objs : ∀ (X Y : C), ∃ Z (f : X ⟶ Z) (g : Y ⟶ Z), true)
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ Z (h : Y ⟶ Z), f ≫ h = g ≫ h)

/--
A category `is_filtered` if
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

See <https://stacks.math.columbia.edu/tag/002V>. (They also define a diagram being filtered.)
-/
class is_filtered extends is_filtered_or_empty C : Prop :=
[nonempty : nonempty C]

@[priority 100]
instance is_filtered_or_empty_of_semilattice_sup
  (α : Type u) [semilattice_sup α] : is_filtered_or_empty α :=
{ cocone_objs := λ X Y, ⟨X ⊔ Y, hom_of_le le_sup_left, hom_of_le le_sup_right, trivial⟩,
  cocone_maps := λ X Y f g, ⟨Y, 𝟙 _, (by ext)⟩, }

@[priority 100]
instance is_filtered_of_semilattice_sup_nonempty
  (α : Type u) [semilattice_sup α] [nonempty α] : is_filtered α := {}

@[priority 100]
instance is_filtered_or_empty_of_directed_le (α : Type u) [preorder α] [is_directed α (≤)] :
  is_filtered_or_empty α :=
{ cocone_objs := λ X Y, let ⟨Z, h1, h2⟩ := exists_ge_ge X Y in
    ⟨Z, hom_of_le h1, hom_of_le h2, trivial⟩,
  cocone_maps := λ X Y f g, ⟨Y, 𝟙 _, by simp⟩ }

@[priority 100]
instance is_filtered_of_directed_le_nonempty (α : Type u) [preorder α] [is_directed α (≤)]
  [nonempty α] :
  is_filtered α := {}

-- Sanity checks
example (α : Type u) [semilattice_sup α] [order_bot α] : is_filtered α := by apply_instance
example (α : Type u) [semilattice_sup α] [order_top α] : is_filtered α := by apply_instance

instance : is_filtered (discrete punit) :=
{ cocone_objs := λ X Y, ⟨⟨punit.star⟩, ⟨⟨dec_trivial⟩⟩, ⟨⟨dec_trivial⟩⟩, trivial⟩,
  cocone_maps := λ X Y f g, ⟨⟨punit.star⟩, ⟨⟨dec_trivial⟩⟩, dec_trivial⟩,
  nonempty := ⟨⟨punit.star⟩⟩ }

namespace is_filtered

section allow_empty

variables {C} [is_filtered_or_empty C]

lemma cocone_objs : ∀ (X Y : C), ∃ Z (f : X ⟶ Z) (g : Y ⟶ Z), true :=
is_filtered_or_empty.cocone_objs
lemma cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ Z (h : Y ⟶ Z), f ≫ h = g ≫ h :=
is_filtered_or_empty.cocone_maps

/--
`max j j'` is an arbitrary choice of object to the right of both `j` and `j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def max (j j' : C) : C :=
(cocone_objs j j').some

/--
`left_to_max j j'` is an arbitrary choice of morphism from `j` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def left_to_max (j j' : C) : j ⟶ max j j' :=
(cocone_objs j j').some_spec.some

/--
`right_to_max j j'` is an arbitrary choice of morphism from `j'` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def right_to_max (j j' : C) : j' ⟶ max j j' :=
(cocone_objs j j').some_spec.some_spec.some

/--
`coeq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
(cocone_maps f f').some

/--
`coeq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq_hom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
(cocone_maps f f').some_spec.some

/--
`coeq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
-/
@[simp, reassoc]
lemma coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f' :=
(cocone_maps f f').some_spec.some_spec

end allow_empty

section nonempty

open category_theory.limits

variables {C} [is_filtered C]

/--
Any finite collection of objects in a filtered category has an object "to the right".
-/
lemma sup_objs_exists (O : finset C) : ∃ (S : C), ∀ {X}, X ∈ O → _root_.nonempty (X ⟶ S) :=
begin
  classical,
  apply finset.induction_on O,
  { exact ⟨is_filtered.nonempty.some, (by rintros - ⟨⟩)⟩, },
  { rintros X O' nm ⟨S', w'⟩,
    use max X S',
    rintros Y mY,
    obtain rfl|h := eq_or_ne Y X,
    { exact ⟨left_to_max _ _⟩, },
    { exact ⟨(w' (finset.mem_of_mem_insert_of_ne mY h)).some ≫ right_to_max _ _⟩, }, }
end

variables (O : finset C) (H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y))

/--
Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : X ⟶ S` from each `X`,
such that the triangles commute: `f ≫ T Y = T X`, for `f : X ⟶ Y` in the `finset`.
-/
lemma sup_exists :
  ∃ (S : C) (T : Π {X : C}, X ∈ O → (X ⟶ S)), ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
    (⟨X, Y, mX, mY, f⟩ : (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y)) ∈ H → f ≫ T mY = T mX :=
begin
  classical,
  apply finset.induction_on H,
  { obtain ⟨S, f⟩ := sup_objs_exists O,
    refine ⟨S, λ X mX, (f mX).some, _⟩,
    rintros - - - - - ⟨⟩, },
  { rintros ⟨X, Y, mX, mY, f⟩ H' nmf ⟨S', T', w'⟩,
    refine ⟨coeq (f ≫ T' mY) (T' mX), λ Z mZ, T' mZ ≫ coeq_hom (f ≫ T' mY) (T' mX), _⟩,
    intros X' Y' mX' mY' f' mf',
    rw [←category.assoc],
    by_cases h : X = X' ∧ Y = Y',
    { rcases h with ⟨rfl, rfl⟩,
      by_cases hf : f = f',
      { subst hf,
        apply coeq_condition, },
      { rw @w' _ _ mX mY f' (by simpa [hf ∘ eq.symm] using mf') }, },
    { rw @w' _ _ mX' mY' f' _,
      apply finset.mem_of_mem_insert_of_ne mf',
      contrapose! h,
      obtain ⟨rfl, h⟩ := h,
      rw [heq_iff_eq, psigma.mk.inj_iff] at h,
      exact ⟨rfl, h.1.symm⟩ }, },
end

/--
An arbitrary choice of object "to the right"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
noncomputable
def sup : C :=
(sup_exists O H).some

/--
The morphisms to `sup O H`.
-/
noncomputable
def to_sup {X : C} (m : X ∈ O) :
  X ⟶ sup O H :=
(sup_exists O H).some_spec.some m

/--
The triangles of consisting of a morphism in `H` and the maps to `sup O H` commute.
-/
lemma to_sup_commutes
  {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
  (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H) :
  f ≫ to_sup O H mY = to_sup O H mX :=
(sup_exists O H).some_spec.some_spec mX mY mf

variables {J : Type v} [small_category J] [fin_category J]

/--
If we have `is_filtered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cocone over `F`.
-/
lemma cocone_nonempty (F : J ⥤ C) : _root_.nonempty (cocone F) :=
begin
  classical,
  let O := (finset.univ.image F.obj),
  let H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bUnion (λ X : J, finset.univ.bUnion (λ Y : J, finset.univ.image (λ f : X ⟶ Y,
      ⟨F.obj X, F.obj Y, by simp, by simp, F.map f⟩))),
  obtain ⟨Z, f, w⟩ := sup_exists O H,
  refine ⟨⟨Z, ⟨λ X, f (by simp), _⟩⟩⟩,
  intros j j' g,
  dsimp,
  simp only [category.comp_id],
  apply w,
  simp only [finset.mem_univ, finset.mem_bUnion, exists_and_distrib_left,
    exists_prop_of_true, finset.mem_image],
  exact ⟨j, rfl, j', g, (by simp)⟩,
end

/--
An arbitrary choice of cocone over `F : J ⥤ C`, for `fin_category J` and `is_filtered C`.
-/
noncomputable def cocone (F : J ⥤ C) : cocone F :=
(cocone_nonempty F).some

variables {D : Type u₁} [category.{v₁} D]

/--
If `C` is filtered, and we have a functor `R : C ⥤ D` with a left adjoint, then `D` is filtered.
-/
lemma of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : is_filtered D :=
{ cocone_objs := λ X Y,
    ⟨_, h.hom_equiv _ _ (left_to_max _ _), h.hom_equiv _ _ (right_to_max _ _), ⟨⟩⟩,
  cocone_maps := λ X Y f g,
    ⟨_, h.hom_equiv _ _ (coeq_hom _ _),
     by rw [← h.hom_equiv_naturality_left, ← h.hom_equiv_naturality_left, coeq_condition]⟩,
  nonempty := is_filtered.nonempty.map R.obj }

/-- If `C` is filtered, and we have a right adjoint functor `R : C ⥤ D`, then `D` is filtered. -/
lemma of_is_right_adjoint (R : C ⥤ D) [is_right_adjoint R] : is_filtered D :=
of_right_adjoint (adjunction.of_right_adjoint R)

/-- Being filtered is preserved by equivalence of categories. -/
lemma of_equivalence (h : C ≌ D) : is_filtered D :=
of_right_adjoint h.symm.to_adjunction

end nonempty

section special_shapes

variables {C} [is_filtered_or_empty C]

/--
`max₃ j₁ j₂ j₃` is an arbitrary choice of object to the right of `j₁`, `j₂` and `j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def max₃ (j₁ j₂ j₃ : C) : C := max (max j₁ j₂) j₃

/--
`first_to_max₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₁` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def first_to_max₃ (j₁ j₂ j₃ : C) : j₁ ⟶ max₃ j₁ j₂ j₃ :=
left_to_max j₁ j₂ ≫ left_to_max (max j₁ j₂) j₃

/--
`second_to_max₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₂` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def second_to_max₃ (j₁ j₂ j₃ : C) : j₂ ⟶ max₃ j₁ j₂ j₃ :=
right_to_max j₁ j₂ ≫ left_to_max (max j₁ j₂) j₃

/--
`third_to_max₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₃` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def third_to_max₃ (j₁ j₂ j₃ : C) : j₃ ⟶ max₃ j₁ j₂ j₃ :=
right_to_max (max j₁ j₂) j₃

/--
`coeq₃ f g h`, for morphisms `f g h : j₁ ⟶ j₂`, is an arbitrary choice of object
which admits a morphism `coeq₃_hom f g h : j₂ ⟶ coeq₃ f g h` such that
`coeq₃_condition₁`, `coeq₃_condition₂` and `coeq₃_condition₃` are satisfied.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : C :=
coeq (coeq_hom f g ≫ left_to_max (coeq f g) (coeq g h))
  (coeq_hom g h ≫ right_to_max (coeq f g) (coeq g h))

/--
`coeq₃_hom f g h`, for morphisms `f g h : j₁ ⟶ j₂`, is an arbitrary choice of morphism
`j₂ ⟶ coeq₃ f g h` such that `coeq₃_condition₁`, `coeq₃_condition₂` and `coeq₃_condition₃`
are satisfied. Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq₃_hom {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : j₂ ⟶ coeq₃ f g h :=
coeq_hom f g ≫ left_to_max (coeq f g) (coeq g h) ≫
coeq_hom (coeq_hom f g ≫ left_to_max (coeq f g) (coeq g h))
  (coeq_hom g h ≫ right_to_max (coeq f g) (coeq g h))

lemma coeq₃_condition₁ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
  f ≫ coeq₃_hom f g h = g ≫ coeq₃_hom f g h :=
by rw [coeq₃_hom, reassoc_of (coeq_condition f g)]

lemma coeq₃_condition₂ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
  g ≫ coeq₃_hom f g h = h ≫ coeq₃_hom f g h :=
begin
  dsimp [coeq₃_hom],
  slice_lhs 2 4 { rw [← category.assoc, coeq_condition _ _] },
  slice_rhs 2 4 { rw [← category.assoc, coeq_condition _ _] },
  slice_lhs 1 3 { rw [← category.assoc, coeq_condition _ _] },
  simp only [category.assoc],
end

lemma coeq₃_condition₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
  f ≫ coeq₃_hom f g h = h ≫ coeq₃_hom f g h :=
eq.trans (coeq₃_condition₁ f g h) (coeq₃_condition₂ f g h)

/-- For every span `j ⟵ i ⟶ j'`, there
   exists a cocone `j ⟶ k ⟵ j'` such that the square commutes. -/
lemma span {i j j' : C} (f : i ⟶ j) (f' : i ⟶ j') :
  ∃ (k : C) (g : j ⟶ k) (g' : j' ⟶ k), f ≫ g = f' ≫ g' :=
let ⟨K, G, G', _⟩ := cocone_objs j j', ⟨k, e, he⟩ := cocone_maps (f ≫ G) (f' ≫ G') in
⟨k, G ≫ e, G' ≫ e, by simpa only [← category.assoc]⟩

/--
Given a "bowtie" of morphisms
```
 j₁   j₂
 |\  /|
 | \/ |
 | /\ |
 |/  \∣
 vv  vv
 k₁  k₂
```
in a filtered category, we can construct an object `s` and two morphisms from `k₁` and `k₂` to `s`,
making the resulting squares commute.
-/
lemma bowtie {j₁ j₂ k₁ k₂ : C}
  (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁) (g₂ : j₂ ⟶ k₂) :
  ∃ (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s), f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β :=
begin
  obtain ⟨t, k₁t, k₂t, ht⟩ := span f₁ g₁,
  obtain ⟨s, ts, hs⟩ := cocone_maps (f₂ ≫ k₁t) (g₂ ≫ k₂t),
  simp_rw category.assoc at hs,
  exact ⟨s, k₁t ≫ ts, k₂t ≫ ts, by rw reassoc_of ht, hs⟩,
end

/--
Given a "tulip" of morphisms
```
 j₁    j₂    j₃
 |\   / \   / |
 | \ /   \ /  |
 |  vv    vv  |
 \  k₁    k₂ /
  \         /
   \       /
    \     /
     \   /
      v v
       l
```
in a filtered category, we can construct an object `s` and three morphisms from `k₁`, `k₂` and `l`
to `s`, making the resulting squares commute.
-/
lemma tulip {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : j₁ ⟶ k₁) (f₂ : j₂ ⟶ k₁) (f₃ : j₂ ⟶ k₂) (f₄ : j₃ ⟶ k₂)
  (g₁ : j₁ ⟶ l) (g₂ : j₃ ⟶ l) :
  ∃ (s : C) (α : k₁ ⟶ s) (β : l ⟶ s) (γ : k₂ ⟶ s),
    f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = f₃ ≫ γ ∧ f₄ ≫ γ = g₂ ≫ β :=
begin
  obtain ⟨l', k₁l, k₂l, hl⟩ := span f₂ f₃,
  obtain ⟨s, ls, l's, hs₁, hs₂⟩ := bowtie g₁ (f₁ ≫ k₁l) g₂ (f₄ ≫ k₂l),
  refine ⟨s, k₁l ≫ l's, ls, k₂l ≫ l's, _, by rw reassoc_of hl, _⟩;
  simp only [hs₁, hs₂, category.assoc],
end

end special_shapes

end is_filtered

/--
A category `is_cofiltered_or_empty` if
1. for every pair of objects there exists another object "to the left", and
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal.
-/
class is_cofiltered_or_empty : Prop :=
(cone_objs : ∀ (X Y : C), ∃ W (f : W ⟶ X) (g : W ⟶ Y), true)
(cone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ W (h : W ⟶ X), h ≫ f = h ≫ g)

/--
A category `is_cofiltered` if
1. for every pair of objects there exists another object "to the left",
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal, and
3. there exists some object.

See <https://stacks.math.columbia.edu/tag/04AZ>.
-/
class is_cofiltered extends is_cofiltered_or_empty C : Prop :=
[nonempty : nonempty C]

@[priority 100]
instance is_cofiltered_or_empty_of_semilattice_inf
  (α : Type u) [semilattice_inf α] : is_cofiltered_or_empty α :=
{ cone_objs := λ X Y, ⟨X ⊓ Y, hom_of_le inf_le_left, hom_of_le inf_le_right, trivial⟩,
  cone_maps := λ X Y f g, ⟨X, 𝟙 _, (by ext)⟩, }

@[priority 100]
instance is_cofiltered_of_semilattice_inf_nonempty
  (α : Type u) [semilattice_inf α] [nonempty α] : is_cofiltered α := {}

@[priority 100]
instance is_cofiltered_or_empty_of_directed_ge (α : Type u) [preorder α]
  [is_directed α (≥)] :
  is_cofiltered_or_empty α :=
{ cone_objs := λ X Y, let ⟨Z, hX, hY⟩ := exists_le_le X Y in
    ⟨Z, hom_of_le hX, hom_of_le hY, trivial⟩,
  cone_maps := λ X Y f g, ⟨X, 𝟙 _, by simp⟩ }

@[priority 100]
instance is_cofiltered_of_directed_ge_nonempty (α : Type u) [preorder α] [is_directed α (≥)]
  [nonempty α] :
  is_cofiltered α := {}

-- Sanity checks
example (α : Type u) [semilattice_inf α] [order_bot α] : is_cofiltered α := by apply_instance
example (α : Type u) [semilattice_inf α] [order_top α] : is_cofiltered α := by apply_instance

instance : is_cofiltered (discrete punit) :=
{ cone_objs := λ X Y, ⟨⟨punit.star⟩, ⟨⟨dec_trivial⟩⟩, ⟨⟨dec_trivial⟩⟩, trivial⟩,
  cone_maps := λ X Y f g, ⟨⟨punit.star⟩, ⟨⟨dec_trivial⟩⟩, dec_trivial⟩,
  nonempty := ⟨⟨punit.star⟩⟩ }

namespace is_cofiltered

section allow_empty

variables {C} [is_cofiltered_or_empty C]

lemma cone_objs : ∀ (X Y : C), ∃ W (f : W ⟶ X) (g : W ⟶ Y), true := is_cofiltered_or_empty.cone_objs
lemma cone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ W (h : W ⟶ X), h ≫ f = h ≫ g :=
is_cofiltered_or_empty.cone_maps

/--
`min j j'` is an arbitrary choice of object to the left of both `j` and `j'`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def min (j j' : C) : C :=
(cone_objs j j').some

/--
`min_to_left j j'` is an arbitrary choice of morphism from `min j j'` to `j`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def min_to_left (j j' : C) : min j j' ⟶ j :=
(cone_objs j j').some_spec.some

/--
`min_to_right j j'` is an arbitrary choice of morphism from `min j j'` to `j'`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def min_to_right (j j' : C) : min j j' ⟶ j' :=
(cone_objs j j').some_spec.some_spec.some

/--
`eq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `eq_hom f f' : eq f f' ⟶ j` such that
`eq_condition : eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
Its existence is ensured by `is_cofiltered`.
-/
noncomputable def eq {j j' : C} (f f' : j ⟶ j') : C :=
(cone_maps f f').some

/--
`eq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`eq_hom f f' : eq f f' ⟶ j` such that
`eq_condition : eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
Its existence is ensured by `is_cofiltered`.
-/
noncomputable def eq_hom {j j' : C} (f f' : j ⟶ j') : eq f f' ⟶ j :=
(cone_maps f f').some_spec.some

/--
`eq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
-/
@[simp, reassoc]
lemma eq_condition {j j' : C} (f f' : j ⟶ j') : eq_hom f f' ≫ f = eq_hom f f' ≫ f' :=
(cone_maps f f').some_spec.some_spec

/-- For every cospan `j ⟶ i ⟵ j'`,
 there exists a cone `j ⟵ k ⟶ j'` such that the square commutes. -/
lemma cospan {i j j' : C} (f : j ⟶ i) (f' : j' ⟶ i) :
  ∃ (k : C) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
let ⟨K, G, G', _⟩ := cone_objs j j', ⟨k, e, he⟩ := cone_maps (G ≫ f) (G' ≫ f') in
⟨k, e ≫ G, e ≫ G', by simpa only [category.assoc] using he⟩

lemma _root_.category_theory.functor.ranges_directed (F : C ⥤ Type*) (j : C) :
  directed (⊇) (λ (f : Σ' i, i ⟶ j), set.range (F.map f.2)) :=
λ ⟨i, ij⟩ ⟨k, kj⟩, let ⟨l, li, lk, e⟩ := cospan ij kj in
by refine ⟨⟨l, lk ≫ kj⟩, e ▸ _, _⟩; simp_rw F.map_comp; apply set.range_comp_subset_range

end allow_empty

section nonempty

open category_theory.limits

variables {C} [is_cofiltered C]

/--
Any finite collection of objects in a cofiltered category has an object "to the left".
-/
lemma inf_objs_exists (O : finset C) : ∃ (S : C), ∀ {X}, X ∈ O → _root_.nonempty (S ⟶ X) :=
begin
  classical,
  apply finset.induction_on O,
  { exact ⟨is_cofiltered.nonempty.some, (by rintros - ⟨⟩)⟩, },
  { rintros X O' nm ⟨S', w'⟩,
    use min X S',
    rintros Y mY,
    obtain rfl|h := eq_or_ne Y X,
    { exact ⟨min_to_left _ _⟩, },
    { exact ⟨min_to_right _ _ ≫ (w' (finset.mem_of_mem_insert_of_ne mY h)).some⟩, }, }
end

variables (O : finset C) (H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y))

/--
Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : S ⟶ X` from each `X`,
such that the triangles commute: `T X ≫ f = T Y`, for `f : X ⟶ Y` in the `finset`.
-/
lemma inf_exists :
  ∃ (S : C) (T : Π {X : C}, X ∈ O → (S ⟶ X)), ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
    (⟨X, Y, mX, mY, f⟩ : (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y)) ∈ H → T mX ≫ f = T mY :=
begin
  classical,
  apply finset.induction_on H,
  { obtain ⟨S, f⟩ := inf_objs_exists O,
    refine ⟨S, λ X mX, (f mX).some, _⟩,
    rintros - - - - - ⟨⟩, },
  { rintros ⟨X, Y, mX, mY, f⟩ H' nmf ⟨S', T', w'⟩,
    refine ⟨eq (T' mX ≫ f) (T' mY), λ Z mZ, eq_hom (T' mX ≫ f) (T' mY) ≫ T' mZ, _⟩,
    intros X' Y' mX' mY' f' mf',
    rw [category.assoc],
    by_cases h : X = X' ∧ Y = Y',
    { rcases h with ⟨rfl, rfl⟩,
      by_cases hf : f = f',
      { subst hf,
        apply eq_condition, },
      { rw @w' _ _ mX mY f' (by simpa [hf ∘ eq.symm] using mf') }, },
    { rw @w' _ _ mX' mY' f' _,
      apply finset.mem_of_mem_insert_of_ne mf',
      contrapose! h,
      obtain ⟨rfl, h⟩ := h,
      rw [heq_iff_eq, psigma.mk.inj_iff] at h,
      exact ⟨rfl, h.1.symm⟩ }, },
end

/--
An arbitrary choice of object "to the left"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
noncomputable
def inf : C :=
(inf_exists O H).some

/--
The morphisms from `inf O H`.
-/
noncomputable
def inf_to {X : C} (m : X ∈ O) :
  inf O H ⟶ X :=
(inf_exists O H).some_spec.some m

/--
The triangles consisting of a morphism in `H` and the maps from `inf O H` commute.
-/
lemma inf_to_commutes
  {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
  (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H) :
  inf_to O H mX ≫ f = inf_to O H mY :=
(inf_exists O H).some_spec.some_spec mX mY mf

variables {J : Type w} [small_category J] [fin_category J]

/--
If we have `is_cofiltered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cone over `F`.
-/
lemma cone_nonempty (F : J ⥤ C) : _root_.nonempty (cone F) :=
begin
  classical,
  let O := (finset.univ.image F.obj),
  let H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bUnion (λ X : J, finset.univ.bUnion (λ Y : J, finset.univ.image (λ f : X ⟶ Y,
      ⟨F.obj X, F.obj Y, by simp, by simp, F.map f⟩))),
  obtain ⟨Z, f, w⟩ := inf_exists O H,
  refine ⟨⟨Z, ⟨λ X, f (by simp), _⟩⟩⟩,
  intros j j' g,
  dsimp,
  simp only [category.id_comp],
  symmetry,
  apply w,
  simp only [finset.mem_univ, finset.mem_bUnion, exists_and_distrib_left,
    exists_prop_of_true, finset.mem_image],
  exact ⟨j, rfl, j', g, (by simp)⟩,
end

/--
An arbitrary choice of cone over `F : J ⥤ C`, for `fin_category J` and `is_cofiltered C`.
-/
noncomputable def cone (F : J ⥤ C) : cone F :=
(cone_nonempty F).some

variables {D : Type u₁} [category.{v₁} D]

/--
If `C` is cofiltered, and we have a functor `L : C ⥤ D` with a right adjoint,
then `D` is cofiltered.
-/
lemma of_left_adjoint {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : is_cofiltered D :=
{ cone_objs := λ X Y,
    ⟨L.obj (min (R.obj X) (R.obj Y)),
      (h.hom_equiv _ X).symm (min_to_left _ _), (h.hom_equiv _ Y).symm (min_to_right _ _), ⟨⟩⟩,
  cone_maps := λ X Y f g,
    ⟨L.obj (eq (R.map f) (R.map g)), (h.hom_equiv _ _).symm (eq_hom _ _),
     by rw [← h.hom_equiv_naturality_right_symm, ← h.hom_equiv_naturality_right_symm,
       eq_condition]⟩,
  nonempty := is_cofiltered.nonempty.map L.obj }

/-- If `C` is cofiltered, and we have a left adjoint functor `L : C ⥤ D`, then `D` is cofiltered. -/
lemma of_is_left_adjoint (L : C ⥤ D) [is_left_adjoint L] : is_cofiltered D :=
of_left_adjoint (adjunction.of_left_adjoint L)

/-- Being cofiltered is preserved by equivalence of categories. -/
lemma of_equivalence (h : C ≌ D) : is_cofiltered D :=
of_left_adjoint h.to_adjunction

end nonempty

end is_cofiltered

section opposite
open opposite

instance is_cofiltered_op_of_is_filtered [is_filtered C] : is_cofiltered Cᵒᵖ :=
{ cone_objs := λ X Y, ⟨op (is_filtered.max X.unop Y.unop),
    (is_filtered.left_to_max _ _).op, (is_filtered.right_to_max _ _).op, trivial⟩,
  cone_maps := λ X Y f g, ⟨op (is_filtered.coeq f.unop g.unop),
    (is_filtered.coeq_hom _ _).op, begin
      rw [(show f = f.unop.op, by simp), (show g = g.unop.op, by simp),
        ← op_comp, ← op_comp],
      congr' 1,
      exact is_filtered.coeq_condition f.unop g.unop,
    end⟩,
  nonempty := ⟨op is_filtered.nonempty.some⟩ }

instance is_filtered_op_of_is_cofiltered [is_cofiltered C] : is_filtered Cᵒᵖ :=
{ cocone_objs := λ X Y, ⟨op (is_cofiltered.min X.unop Y.unop),
    (is_cofiltered.min_to_left X.unop Y.unop).op,
    (is_cofiltered.min_to_right X.unop Y.unop).op, trivial⟩,
  cocone_maps := λ X Y f g, ⟨op (is_cofiltered.eq f.unop g.unop),
    (is_cofiltered.eq_hom f.unop g.unop).op, begin
      rw [(show f = f.unop.op, by simp), (show g = g.unop.op, by simp),
        ← op_comp, ← op_comp],
      congr' 1,
      exact is_cofiltered.eq_condition f.unop g.unop,
    end⟩,
  nonempty := ⟨op is_cofiltered.nonempty.some⟩ }

end opposite

section ulift

instance [is_filtered C] : is_filtered (ulift.{u₂} C) :=
is_filtered.of_equivalence ulift.equivalence

instance [is_cofiltered C] : is_cofiltered (ulift.{u₂} C) :=
is_cofiltered.of_equivalence ulift.equivalence

instance [is_filtered C] : is_filtered (ulift_hom C) :=
is_filtered.of_equivalence ulift_hom.equiv

instance [is_cofiltered C] : is_cofiltered (ulift_hom C) :=
is_cofiltered.of_equivalence ulift_hom.equiv

instance [is_filtered C] : is_filtered (as_small C) :=
is_filtered.of_equivalence as_small.equiv

instance [is_cofiltered C] : is_cofiltered (as_small C) :=
is_cofiltered.of_equivalence as_small.equiv

end ulift

end category_theory
