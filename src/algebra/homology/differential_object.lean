/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homological_complex
import category_theory.differential_object

/-!
# Homological complexes are differential graded objects.

We verify that a `homological_complex` indexed by an `add_comm_group` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/

open category_theory
open category_theory.limits

open_locale classical
noncomputable theory

namespace homological_complex

variables {β γ : Type*} [add_right_cancel_monoid β] [has_one γ] [add_comm_monoid γ] {f : γ →+ β}
variables {V : Type*} [category V] [has_zero_morphisms V]

/-- Since `eq_to_hom` only preserves the fact that `X.X i = X.X j` but not `i = j`, this definition
is used to aid the simplifier. -/
abbreviation _root_.category_theory.differential_object.X_eq_to_hom
  (X : differential_object (graded_object_with_shift f V) γ)
  {i j : β} (h : i = j) : X.X i ⟶ X.X j := eq_to_hom (congr_arg X.X h)

@[simp] lemma _root_.category_theory.differential_object.X_eq_to_hom_refl
  (X : differential_object (graded_object_with_shift f V) γ) (i : β) :
    X.X_eq_to_hom (refl i) = 𝟙 _ := rfl

@[simp, reassoc] lemma eq_to_hom_d (X : differential_object (graded_object_with_shift f V) γ)
  {x y : β} (h : x = y) :
  X.X_eq_to_hom h ≫ X.d y = X.d x ≫ X.X_eq_to_hom (by simp [h]) :=
by { cases h, erw [category.comp_id, category.id_comp] }

@[simp, reassoc] lemma d_eq_to_hom (X : homological_complex V (complex_shape.up' (f 1)))
  {x y z : β} (h : y = z) :
  X.d x y ≫ eq_to_hom (congr_arg X.X h) = X.d x z :=
by { cases h, simp }

@[simp, reassoc] lemma eq_to_hom_f {X Y : differential_object (graded_object_with_shift f V) γ}
  (f : X ⟶ Y) {x y : β} (h : x = y) :
  X.X_eq_to_hom h ≫ f.f y = f.f x ≫ Y.X_eq_to_hom h :=
by { cases h, simp }

variables (f V)

local attribute [reducible] graded_object.has_shift_of_add_monoid_hom

/--
The functor from differential graded objects to homological complexes.
-/
@[simps]
def dgo_to_homological_complex :
  differential_object (graded_object_with_shift f V) γ ⥤
    homological_complex V (complex_shape.up' (f 1)) :=
{ obj := λ X,
  { X := λ i, X.X i,
    d := λ i j, if h : i + f 1 = j then X.d i ≫ X.X_eq_to_hom h else 0,
    shape' := λ i j w, by { dsimp at w, convert dif_neg w },
    d_comp_d' := λ i j k hij hjk, begin
      dsimp at hij hjk, substs hij hjk,
      have : X.d i ≫ X.d _ = _ := (congr_fun X.d_squared i : _),
      dsimp,
      simp only [if_true, eq_self_iff_true],
      erw [category.comp_id, category.comp_id, this],
      refl
    end },
  map := λ X Y g,
  { f := g.f,
    comm' := λ i j h, begin
      dsimp at h ⊢,
      subst h,
      have : g.f i ≫ Y.d i = X.d i ≫ g.f (i + f 1) := (congr_fun g.comm i).symm,
      reassoc! this,
      simp only [category.comp_id, eq_to_hom_refl, dif_pos rfl, this, category.assoc, eq_to_hom_f]
    end, } }

/--
The functor from homological complexes to differential graded objects.
-/
@[simps]
def homological_complex_to_dgo :
  homological_complex V (complex_shape.up' (f 1)) ⥤
    differential_object (graded_object_with_shift f V) γ :=
{ obj := λ X,
  { X := λ i, X.X i,
    d := λ i, X.d i (i + f 1),
    d_squared' := by { ext i, dsimp, simp } },
  map := λ X Y f,
  { f := f.f,
    comm' := by { ext i, dsimp, simp, }, } }

/--
The unit map for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_unit_iso_apply
  (X : differential_object (graded_object_with_shift f V) γ) :
  X ⟶ (homological_complex_to_dgo f V).obj ((dgo_to_homological_complex f V).obj X) :=
{ f := λ i, 𝟙 (X.X i) }

/--
The inverse unit map for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_unit_iso_inv_apply
  (X : differential_object (graded_object_with_shift f V) γ) :
  (homological_complex_to_dgo f V).obj ((dgo_to_homological_complex f V).obj X) ⟶ X :=
{ f := λ i, 𝟙 (X.X i) }

/--
The unit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_unit_iso :
  𝟭 (differential_object (graded_object_with_shift f V) γ) ≅
    dgo_to_homological_complex f V ⋙ homological_complex_to_dgo f V :=
nat_iso.of_components (λ X,
  { hom := dgo_equiv_homological_complex_unit_iso_apply f V X,
    inv := dgo_equiv_homological_complex_unit_iso_inv_apply f V X }) (by tidy)

/--
The counit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_counit_iso :
  homological_complex_to_dgo f V ⋙ dgo_to_homological_complex f V ≅
    𝟭 (homological_complex V (complex_shape.up' (f 1))) :=
nat_iso.of_components (λ X,
  { hom :=
    { f := λ i, 𝟙 (X.X i),
      comm' := λ i j h, begin
        dsimp at h ⊢, subst h,
        delta homological_complex_to_dgo,
        simp,
      end },
    inv :=
    { f := λ i, 𝟙 (X.X i),
      comm' := λ i j h, begin
        dsimp at h ⊢, subst h,
        delta homological_complex_to_dgo,
        simp,
      end }, }) (by tidy)

/--
The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
def dgo_equiv_homological_complex :
  differential_object (graded_object_with_shift f V) γ ≌
    homological_complex V (complex_shape.up' (f 1)) :=
{ functor := dgo_to_homological_complex f V,
  inverse := homological_complex_to_dgo f V,
  unit_iso := dgo_equiv_homological_complex_unit_iso f V,
  counit_iso := dgo_equiv_homological_complex_counit_iso f V, }

local attribute [instance] endofunctor_monoidal_category

instance : has_shift (homological_complex V (complex_shape.up' (f 1))) γ :=
⟨(shift_monoidal_functor _ _).comp (comp_equiv_monoidal (dgo_equiv_homological_complex f V))⟩

end homological_complex
