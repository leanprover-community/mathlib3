/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import category_theory.fin_category
import category_theory.limits.cones
import order.bounded_lattice
import tactic.slice

/-!
# Filtered categories

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

Filtered colimits are often better behaved than arbitrary colimits.
See `category_theory/limits/types` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and often often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [fin_category J] [is_filtered C] (F : J ⥤ C) : nonempty (cocone F)`
More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice. We give two variants,
`sup_exists'`, which takes a single finset of objects, and a finset of morphisms
(bundled with their sources and targets), and
`sup_exists`, which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

## Future work
* Finite limits commute with filtered colimits
* Forgetful functors for algebraic categories typically preserve filtered colimits.
-/

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

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

See https://stacks.math.columbia.edu/tag/002V. (They also define a diagram being filtered.)
-/
class is_filtered extends is_filtered_or_empty C : Prop :=
[nonempty : nonempty C]

@[priority 100]
instance is_filtered_or_empty_of_semilattice_sup
  (α : Type u) [semilattice_sup α] : is_filtered_or_empty α :=
{ cocone_objs := λ X Y, ⟨X ⊔ Y, hom_of_le le_sup_left, hom_of_le le_sup_right, trivial⟩,
  cocone_maps := λ X Y f g, ⟨Y, 𝟙 _, (by ext)⟩, }

@[priority 100]
instance is_filtered_of_semilattice_sup_top
  (α : Type u) [semilattice_sup_top α] : is_filtered α :=
{ nonempty := ⟨⊤⟩,
  ..category_theory.is_filtered_or_empty_of_semilattice_sup α }

namespace is_filtered

variables {C} [is_filtered C]

/--
`max j j'` is an arbitrary choice of object to the right of both `j` and `j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def max (j j' : C) : C :=
(is_filtered_or_empty.cocone_objs j j').some

/--
`left_to_max j j'` is an arbitrarily choice of morphism from `j` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def left_to_max (j j' : C) : j ⟶ max j j' :=
(is_filtered_or_empty.cocone_objs j j').some_spec.some

/--
`right_to_max j j'` is an arbitrarily choice of morphism from `j'` to `max j j'`,
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
    by_cases h : X = Y,
    { subst h, exact ⟨left_to_max _ _⟩, },
    { exact ⟨(w' (by finish)).some ≫ right_to_max _ _⟩, }, }
end

variables (O : finset C) (H : finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y))

/--
Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : X ⟶ S` from each `X`,
such that the triangles commute: `f ≫ T X = T Y`, for `f : X ⟶ Y` in the `finset`.
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
      { rw w' _ _ (by finish), }, },
    { rw w' _ _ (by finish), }, },
end

/--
An arbitrary choice of object "to the right" of a finite collection of objects `O` and morphisms `H`,
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
    finset.univ.bind (λ X : J, finset.univ.bind (λ Y : J, finset.univ.image (λ f : X ⟶ Y,
      ⟨F.obj X, F.obj Y, by simp, by simp, F.map f⟩))),
  obtain ⟨Z, f, w⟩ := sup_exists O H,
  refine ⟨⟨Z, ⟨λ X, f (by simp), _⟩⟩⟩,
  intros j j' g,
  dsimp,
  simp only [category.comp_id],
  apply w,
  simp only [finset.mem_univ, finset.mem_bind, exists_and_distrib_left,
    exists_prop_of_true, finset.mem_image],
  exact ⟨j, rfl, j', g, (by simp)⟩,
end

/--
An arbitrary choice of cocone over `F : J ⥤ C`, for `fin_category J` and `is_filtered C`.
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
