/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.preserves.shapes.terminal
import category_theory.limits.shapes.zero

/-!
# Preservation of zero objects and zero morphisms
We define the class `preserves_zero_morphisms` and show basic properties.
## Main results
We provide the following results:
* Equivalences preserve zero morphisms;
* if both categories involved have a zero object, then a functor preserves zero morphisms if and
  only if it preserves the zero object;
* functors which preserve initial or terminal objects preserve zero morphisms.
-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory
open category_theory.limits

namespace category_theory.functor
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

section zero_morphisms
variables [has_zero_morphisms C] [has_zero_morphisms D]

/-- A functor preserves zero morphisms if it sends zero morphisms to zero morphisms. -/
class preserves_zero_morphisms (F : C ⥤ D) : Prop :=
(map_zero' : ∀ (X Y : C), F.map (0 : X ⟶ Y) = 0 . obviously)

@[simp]
protected lemma map_zero (F : C ⥤ D) [preserves_zero_morphisms F] (X Y : C) :
  F.map (0 : X ⟶ Y) = 0 :=
preserves_zero_morphisms.map_zero' _ _

lemma equivalence_preserves_zero_morphisms (F : C ≌ D) : preserves_zero_morphisms F.functor :=
begin
  refine ⟨λ X Y, eq.trans _ (@limits.comp_zero _ _ _ _ _ (F.functor.map (0 : X ⟶ Y)) _)⟩,
  refine faithful.map_injective (F.inverse) _,
  rw [functor.map_comp, equivalence.inv_fun_map, zero_comp, comp_zero, zero_comp]
end

@[priority 100]
instance is_equivalence_preserves_zero_morphisms (F : C ⥤ D) [is_equivalence F] :
  preserves_zero_morphisms F :=
equivalence_preserves_zero_morphisms F.as_equivalence

end zero_morphisms

section zero_object
variables [has_zero_object C] [has_zero_object D]

open_locale zero_object

variables [has_zero_morphisms C] [has_zero_morphisms D] (F : C ⥤ D)

/-- A functor that preserves zero morphisms also preserves the zero object. -/
@[simps] def map_zero_object [preserves_zero_morphisms F] : F.obj 0 ≅ 0 :=
{ hom := 0,
  inv := 0,
  hom_inv_id' := by rw [← F.map_id, id_zero, F.map_zero, zero_comp],
  inv_hom_id' := by rw [id_zero, comp_zero] }

variables {F}

lemma preserves_zero_morphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : preserves_zero_morphisms F :=
{ map_zero' := λ X Y, calc
  F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 : by rw [← functor.map_comp, comp_zero]
                ... = F.map 0 ≫ (i.hom ≫ i.inv) ≫ F.map 0
                        : by rw [iso.hom_inv_id, category.id_comp]
                ... = 0 : by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero] }

@[priority 100]
instance preserves_zero_morphisms_of_preserves_initial_object
  [preserves_colimit (functor.empty.{v₁} C) F] : preserves_zero_morphisms F :=
preserves_zero_morphisms_of_map_zero_object $ (F.map_iso has_zero_object.zero_iso_initial).trans $
  (preserves_initial.iso F).trans has_zero_object.zero_iso_initial.symm

@[priority 100]
instance preserves_zero_morphisms_of_preserves_terminal_object
  [preserves_limit (functor.empty.{v₁} C) F] : preserves_zero_morphisms F :=
preserves_zero_morphisms_of_map_zero_object $ (F.map_iso has_zero_object.zero_iso_terminal).trans $
    (preserves_terminal.iso F).trans has_zero_object.zero_iso_terminal.symm

end zero_object

end category_theory.functor
