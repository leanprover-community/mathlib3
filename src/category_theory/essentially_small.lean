/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import logic.small
import category_theory.skeletal

/-!
# Essentially small categories.

A category given by `(C : Type u) [category.{v} C]` is `w`-essentially small
if there exists a `small_model C : Type w` equipped with `[small_category (small_model C)]`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `skeleton C` is `w`-small, and `C` is `w`-locally small.
-/

universes w v v' u u'

open category_theory

variables (C : Type u) [category.{v} C]

namespace category_theory

/-- A category is `essentially_small.{w}` if there exists
an equivalence to some `S : Type w` with `[small_category S]`. -/
class essentially_small (C : Type u) [category.{v} C] : Prop :=
(equiv_small_category : ∃ (S : Type w) (_ : small_category S), by exactI nonempty (C ≌ S))

/-- Constructor for `essentially_small C` from an explicit small category witness. -/
lemma essentially_small.mk' {C : Type u} [category.{v} C] {S : Type w} [small_category S]
  (e : C ≌ S) : essentially_small.{w} C :=
⟨⟨S, _, ⟨e⟩⟩⟩

/--
An arbitrarily chosen small model for an essentially small category.
-/
@[nolint has_inhabited_instance]
def small_model (C : Type u) [category.{v} C] [essentially_small.{w} C] : Type w :=
classical.some (@essentially_small.equiv_small_category C _ _)

noncomputable
instance small_category_small_model
  (C : Type u) [category.{v} C] [essentially_small.{w} C] : small_category (small_model C) :=
classical.some (classical.some_spec (@essentially_small.equiv_small_category C _ _))

/--
The (noncomputable) categorical equivalence between
an essentially small category and its small model.
-/
noncomputable
def equiv_small_model (C : Type u) [category.{v} C] [essentially_small.{w} C] : C ≌ small_model C :=
nonempty.some (classical.some_spec (classical.some_spec
  (@essentially_small.equiv_small_category C _ _)))

lemma essentially_small_congr {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D]
  (e : C ≌ D) : essentially_small.{w} C ↔ essentially_small.{w} D :=
begin
  fsplit,
  { rintro ⟨S, 𝒮, ⟨f⟩⟩,
    resetI,
    exact essentially_small.mk' (e.symm.trans f), },
  { rintro ⟨S, 𝒮, ⟨f⟩⟩,
    resetI,
    exact essentially_small.mk' (e.trans f), },
end

/--
A category is `w`-locally small if every hom set is `w`-small.

See `shrink_homs C` for a category instance where every hom set has been replaced by a small model.
-/
class locally_small (C : Type u) [category.{v} C] : Prop :=
(hom_small : ∀ X Y : C, small.{w} (X ⟶ Y) . tactic.apply_instance)

instance (C : Type u) [category.{v} C] [locally_small.{w} C] (X Y : C) :
  small (X ⟶ Y) :=
locally_small.hom_small X Y

lemma locally_small_congr {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D]
  (e : C ≌ D) : locally_small.{w} C ↔ locally_small.{w} D :=
begin
  fsplit,
  { rintro ⟨L⟩,
    fsplit,
    intros X Y,
    specialize L (e.inverse.obj X) (e.inverse.obj Y),
    refine (small_congr _).mpr L,
    exact equiv_of_fully_faithful e.inverse, },
  { rintro ⟨L⟩,
    fsplit,
    intros X Y,
    specialize L (e.functor.obj X) (e.functor.obj Y),
    refine (small_congr _).mpr L,
    exact equiv_of_fully_faithful e.functor, },
end

@[priority 100]
instance locally_small_self (C : Type u) [category.{v} C] : locally_small.{v} C := {}

@[priority 100]
instance locally_small_of_essentially_small
  (C : Type u) [category.{v} C] [essentially_small.{w} C] : locally_small.{w} C :=
(locally_small_congr (equiv_small_model C)).mpr (category_theory.locally_small_self _)

/--
We define a type alias `shrink_homs C` for `C`. When we have `locally_small.{w} C`,
we'll put a `category.{w}` instance on `shrink_homs C`.
-/
@[nolint has_inhabited_instance]
def shrink_homs (C : Type u) := C

namespace shrink_homs

section
variables {C' : Type*} -- a fresh variable with no category instance attached

/-- Help the typechecker by explicitly translating from `C` to `shrink_homs C`. -/
def to_shrink_homs {C' : Type*} (X : C') : shrink_homs C' := X
/-- Help the typechecker by explicitly translating from `shrink_homs C` to `C`. -/
def from_shrink_homs {C' : Type*} (X : shrink_homs C') : C' := X

@[simp] lemma to_from (X : C') : from_shrink_homs (to_shrink_homs X) = X := rfl
@[simp] lemma from_to (X : shrink_homs C') : to_shrink_homs (from_shrink_homs X) = X := rfl

end

variables (C) [locally_small.{w} C]

@[simps]
noncomputable
instance : category.{w} (shrink_homs C) :=
{ hom := λ X Y, shrink (from_shrink_homs X ⟶ from_shrink_homs Y),
  id := λ X, equiv_shrink _ (𝟙 (from_shrink_homs X)),
  comp := λ X Y Z f g,
    equiv_shrink _ (((equiv_shrink _).symm f) ≫ ((equiv_shrink _).symm g)), }.

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable
def functor : C ⥤ shrink_homs C :=
{ obj := λ X, to_shrink_homs X,
  map := λ X Y f, equiv_shrink (X ⟶ Y) f, }

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable
def inverse : shrink_homs C ⥤ C :=
{ obj := λ X, from_shrink_homs X,
  map := λ X Y f, (equiv_shrink (from_shrink_homs X ⟶ from_shrink_homs Y)).symm f, }

/--
The categorical equivalence between `C` and `shrink_homs C`, when `C` is locally small.
-/
@[simps]
noncomputable
def equivalence : C ≌ shrink_homs C :=
equivalence.mk (functor C) (inverse C)
  (nat_iso.of_components (λ X, iso.refl X) (by tidy))
  (nat_iso.of_components (λ X, iso.refl X) (by tidy))

end shrink_homs

/--
A category is essentially small if and only if
the underlying type of its skeleton (i.e. the "set" of isomorphism classes) is small,
and it is locally small.
-/
theorem essentially_small_iff (C : Type u) [category.{v} C] :
  essentially_small.{w} C ↔ small.{w} (skeleton C) ∧ locally_small.{w} C :=
begin
  -- This theorem is the only bit of real work in this file.
  fsplit,
  { intro h,
    fsplit,
    { rcases h with ⟨S, 𝒮, ⟨e⟩⟩,
      resetI,
      refine ⟨⟨skeleton S, ⟨_⟩⟩⟩,
      exact e.skeleton_equiv, },
    { resetI, apply_instance, }, },
  { rintro ⟨⟨S, ⟨e⟩⟩, L⟩,
    resetI,
    let e' := (shrink_homs.equivalence C).skeleton_equiv.symm,
    refine ⟨⟨S, _, ⟨_⟩⟩⟩,
    apply induced_category.category (e'.trans e).symm,
    refine (shrink_homs.equivalence C).trans
      ((skeleton_equivalence _).symm.trans
      ((induced_functor (e'.trans e).symm).as_equivalence.symm)), },
end

/--
Any thin category is locally small.
-/
@[priority 100]
instance locally_small_of_thin {C : Type u} [category.{v} C] [∀ X Y : C, subsingleton (X ⟶ Y)] :
  locally_small.{w} C := {}

/--
A thin category is essentially small if and only if the underlying type of its skeleton is small.
-/
theorem essentially_small_iff_of_thin
  {C : Type u} [category.{v} C] [∀ X Y : C, subsingleton (X ⟶ Y)] :
  essentially_small.{w} C ↔ small.{w} (skeleton C) :=
by simp [essentially_small_iff, category_theory.locally_small_of_thin]

end category_theory
