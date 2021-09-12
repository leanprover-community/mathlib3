/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homological_complex

/-!
# Flip a complex of complexes

For now we don't have double complexes as a distinct thing,
but we can model them as complexes of complexes.

Here we show how to flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.

-/

universes v u

open category_theory category_theory.limits

namespace homological_complex

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
variables {ι : Type*} {c : complex_shape ι} {ι' : Type*} {c' : complex_shape ι'}

/--
Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flip_obj (C : homological_complex (homological_complex V c) c') :
  homological_complex (homological_complex V c') c :=
{ X := λ i,
  { X := λ j, (C.X j).X i,
    d := λ j j', (C.d j j').f i,
    shape' := λ j j' w, by { rw C.shape j j' w, simp, },
    d_comp_d' := λ j₁ j₂ j₃ _ _, congr_hom (C.d_comp_d j₁ j₂ j₃) i, },
  d := λ i i',
  { f := λ j, (C.X j).d i i',
    comm' := λ j j' h, ((C.d j j').comm i i').symm, },
  shape' := λ i i' w, by { ext j, exact (C.X j).shape i i' w, } }.

variables V c c'

/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flip : homological_complex (homological_complex V c) c' ⥤
  homological_complex (homological_complex V c') c :=
{ obj := λ C, flip_obj C,
  map := λ C D f,
  { f := λ i,
    { f := λ j, (f.f j).f i,
      comm' := λ j j' h, congr_hom (f.comm j j') i, }, }, }.

/-- Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flip_equivalence_unit_iso :
  𝟭 (homological_complex (homological_complex V c) c') ≅ flip V c c' ⋙ flip V c' c :=
nat_iso.of_components
  (λ C,
  { hom :=
    { f := λ i, { f := λ j, 𝟙 ((C.X i).X j), },
      comm' := λ i j h, by { ext, dsimp, simp only [category.id_comp, category.comp_id] }, },
    inv :=
    { f := λ i, { f := λ j, 𝟙 ((C.X i).X j), },
      comm' := λ i j h, by { ext, dsimp, simp only [category.id_comp, category.comp_id] }, } })
  (λ X Y f, by { ext, dsimp, simp only [category.id_comp, category.comp_id], })

/-- Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flip_equivalence_counit_iso :
  flip V c' c ⋙ flip V c c' ≅ 𝟭 (homological_complex (homological_complex V c') c) :=
nat_iso.of_components
  (λ C,
  { hom :=
    { f := λ i, { f := λ j, 𝟙 ((C.X i).X j), },
      comm' := λ i j h, by { ext, dsimp, simp only [category.id_comp, category.comp_id] }, },
    inv :=
    { f := λ i, { f := λ j, 𝟙 ((C.X i).X j), },
      comm' := λ i j h, by { ext, dsimp, simp only [category.id_comp, category.comp_id] }, } })
  (λ X Y f, by { ext, dsimp, simp only [category.id_comp, category.comp_id], })

/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flip_equivalence :
  homological_complex (homological_complex V c) c' ≌
    homological_complex (homological_complex V c') c :=
{ functor := flip V c c',
  inverse := flip V c' c,
  unit_iso := flip_equivalence_unit_iso V c c',
  counit_iso := flip_equivalence_counit_iso V c c', }

end homological_complex
