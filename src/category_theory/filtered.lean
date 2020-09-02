-- Copyright (c) 2019 Reid Barton. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Reid Barton
import category_theory.fin_category
import category_theory.limits.cones
import tactic.slice

/-!
# Filtered categories

A filtered category is a category for which
* for each pair of objects `X Y : C`, there exists some `Z` with morphisms `X ⟶ Z` and `Y ⟶ Z`,
* for each pair of morphisms `f g : X ⟶ Y`, there exists some `k : Y ⟶ Z` for some `Z`,
  so `f ≫ k = g ≫ k`
* and the category is nonempty.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and often often preserved by functors).

In this file we show that any functor out of a filtered category admits a cocone,
and more generally, for any finite collection of objects and morphisms between them in a category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
-/

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

variables (C : Type u) [category.{v} C]

class is_filtered_or_empty : Prop :=
(cocone_objs : ∀ (X Y : C), ∃ Z (f : X ⟶ Z) (g : Y ⟶ Z), true)
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ Z (h : Y ⟶ Z), f ≫ h = g ≫ h)

class is_filtered extends is_filtered_or_empty C : Prop :=
(nonempty : nonempty C)

namespace is_filtered

variables {C} [is_filtered C]

/--
`max j j'` is an arbitrary choice of object to the right of both `j` and `j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def max (j j' : C) : C :=
(is_filtered_or_empty.cocone_objs j j').some

/--
`left_to_max j j'` is an arbitrarily choice of morphism from `j` to `sup j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def left_to_max (j j' : C) : j ⟶ max j j' :=
(is_filtered_or_empty.cocone_objs j j').some_spec.some

/--
`right_to_max j j'` is an arbitrarily choice of morphism from `j'` to `sup j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def right_to_max (j j' : C) : j' ⟶ max j j' :=
(is_filtered_or_empty.cocone_objs j j').some_spec.some_spec.some

/--
`coeq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
(is_filtered_or_empty.cocone_maps f f').some

/--
`coeq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq_hom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
(is_filtered_or_empty.cocone_maps f f').some_spec.some

/--
`coeq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
-/
lemma coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f' :=
(is_filtered_or_empty.cocone_maps f f').some_spec.some_spec

open category_theory.limits

variables {J : Type v} [small_category J] [fin_category J]

lemma sup_objs_exists (O : finset C) : ∃ (S : C), ∀ {X}, X ∈ O → _root_.nonempty (X ⟶ S) :=
begin
  classical,
  apply finset.induction_on O,
  { exact ⟨is_filtered.nonempty.some, (by rintros - ⟨⟩)⟩, },
  { rintros X O' nm ⟨S', w'⟩,
    use max X S',
    rintros Y mY,
    by_cases h : X = Y,
    { subst h, exact ⟨left_to_max _ _⟩, },
    { exact ⟨(w' (by finish)).some ≫ right_to_max _ _⟩, }, }
end

lemma sup_exists' (O : finset C) (H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y)) :
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
      { rw w' _ _ (by finish), }, },
    { rw w' _ _ (by finish), }, },
end

lemma sup_exists (O : finset C) (H : Π X Y, X ∈ O → Y ∈ O → finset (X ⟶ Y)) :
  ∃ (S : C) (T : Π {X : C}, X ∈ O → (X ⟶ S)), ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
    f ∈ H _ _ mX mY → f ≫ T mY = T mX :=
begin
  classical,
  let H' : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    O.attach.bind (λ X : { X // X ∈ O }, O.attach.bind (λ Y : { Y // Y ∈ O },
      (H X.1 Y.1 X.2 Y.2).image (λ f, ⟨X.1, Y.1, X.2, Y.2, f⟩))),
  obtain ⟨S, T, w⟩ := sup_exists' O H',
  refine ⟨S, @T, _⟩,
  intros X Y mX mY f mf,
  apply w,
  simp only [finset.mem_attach, exists_prop, finset.mem_bind, exists_prop_of_true, finset.mem_image,
    subtype.exists, subtype.coe_mk, subtype.val_eq_coe],
  refine ⟨X, mX, Y, mY, f, mf, rfl, (by simp)⟩,
end

noncomputable
def sup (O : finset C) (H : Π X Y, X ∈ O → Y ∈ O → finset (X ⟶ Y)) : C :=
(sup_exists O H).some

noncomputable
def to_sup (O : finset C) (H : Π X Y, X ∈ O → Y ∈ O → finset (X ⟶ Y)) {X : C} (m : X ∈ O) :
  X ⟶ sup O H :=
(sup_exists O H).some_spec.some m

lemma to_sup_commutes (O : finset C) (H : Π X Y, X ∈ O → Y ∈ O → finset (X ⟶ Y))
  {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y} (mf : f ∈ H _ _ mX mY) : f ≫ to_sup O H mY = to_sup O H mX :=
(sup_exists O H).some_spec.some_spec mX mY mf

@[simp] lemma exists_apply_eq_apply {α β : Type*} (f : α → β) (a : α) : ∃ a', f a = f a' :=
⟨a, rfl⟩

@[simp] lemma exists_apply_eq_apply' {α β : Type*} (f : α → β) (a : α) : ∃ a', f a' = f a :=
⟨a, rfl⟩

/--
If we have `is_filtered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cocone over `F`.
-/
lemma cocone_nonempty (F : J ⥤ C) : _root_.nonempty (cocone F):=
begin
  classical,
  let O := (finset.univ.image F.obj),
  let H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bind (λ X : J, finset.univ.bind (λ Y : J, finset.univ.image (λ f : X ⟶ Y,
      ⟨F.obj X, F.obj Y, by simp, by simp, F.map f⟩))),
  obtain ⟨Z, f, w⟩ := sup_exists' O H,
  refine ⟨⟨Z, ⟨λ X, f (by simp), _⟩⟩⟩,
  intros j j' g,
  dsimp,
  simp,
  apply w,
  simp,
  exact ⟨j, rfl, j', g, (by simp)⟩,
end

/--
An arbitrarily chosen cocone over `F : J ⥤ C`, for `fin_category J` and `is_filtered C`.
-/
noncomputable def cocone (F : J ⥤ C) : cocone F :=
(cocone_nonempty F).some

/--
Given a "bowtie" of morphisms
```
jx -> j₁
  \  ^
   \/
   /\
  /  v
jy -> j₂
```
in a filtered category, construct a morphism `j` sitting to the right of `j₁` and `j₂`,
making both of the resulting squares commute.
-/
noncomputable lemma bowtie {jx jy j₁ j₂ : C}
  (ix₁ : jx ⟶ j₁) (ix₂ : jx ⟶ j₂) (iy₁ : jy ⟶ j₁) (iy₂ : jy ⟶ j₂) :
  Σ' (j : C) (i₁ : j₁ ⟶ j) (i₂ : j₂ ⟶ j), ix₁ ≫ i₁ = ix₂ ≫ i₂ ∧ iy₁ ≫ i₁ = iy₂ ≫ i₂ :=
begin
  let ja := max j₁ j₂,
  let jb := coeq (ix₁ ≫ left_to_max _ _) (ix₂ ≫ right_to_max _ _),
  let jc := coeq (iy₁ ≫ left_to_max _ _) (iy₂ ≫ right_to_max _ _),
  let jd := max jb jc,
  let j := coeq ((coeq_hom _ _ : ja ⟶ jb) ≫ left_to_max _ _) ((coeq_hom _ _ : ja ⟶ jc) ≫ right_to_max _ _),
  use j,
  fsplit,
  exact left_to_max j₁ j₂ ≫ coeq_hom _ _ ≫ left_to_max jb jc ≫ coeq_hom _ _,
  fsplit,
  exact right_to_max j₁ j₂ ≫ coeq_hom _ _ ≫ right_to_max jb jc ≫ coeq_hom _ _,
  fsplit,
  { slice_lhs 1 3 { rw [←category.assoc, coeq_condition], },
    slice_lhs 3 5 { rw [←category.assoc, coeq_condition], },
    simp only [category.assoc], },
  { slice_lhs 3 5 { rw [←category.assoc, coeq_condition], },
    slice_lhs 1 3 { rw [←category.assoc, coeq_condition], },
    simp only [category.assoc], }
end

end is_filtered

end category_theory
