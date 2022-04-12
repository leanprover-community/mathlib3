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
* Left adjoints and right adjoints preserve zero morphisms;
* full functors preserve zero morphisms;
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

lemma zero_of_map_zero (F : C ⥤ D) [preserves_zero_morphisms F] [faithful F] {X Y : C}
  (f : X ⟶ Y) (h : F.map f = 0) : f = 0 :=
F.map_injective $ h.trans $ eq.symm $ F.map_zero _ _

lemma map_eq_zero_iff (F : C ⥤ D) [preserves_zero_morphisms F] [faithful F] {X Y : C} {f : X ⟶ Y} :
  F.map f = 0 ↔ f = 0 :=
⟨F.zero_of_map_zero _, by { rintro rfl, exact F.map_zero _ _ }⟩

@[priority 100]
instance preserves_zero_morphisms_of_is_left_adjoint (F : C ⥤ D) [is_left_adjoint F] :
  preserves_zero_morphisms F :=
{ map_zero' := λ X Y, let adj := adjunction.of_left_adjoint F in
  begin
    calc F.map (0 : X ⟶ Y) = F.map 0 ≫ F.map (adj.unit.app Y) ≫ adj.counit.app (F.obj Y) : _
    ... = F.map 0 ≫ F.map ((right_adjoint F).map (0 : F.obj X ⟶ _)) ≫ adj.counit.app (F.obj Y) : _
    ... = 0 : _,
    { rw adjunction.left_triangle_components, exact (category.comp_id _).symm },
    { simp only [← category.assoc, ← F.map_comp, zero_comp] },
    { simp only [adjunction.counit_naturality, comp_zero] }
  end }

@[priority 100]
instance preserves_zero_morphisms_of_is_right_adjoint (G : C ⥤ D) [is_right_adjoint G] :
  preserves_zero_morphisms G :=
{ map_zero' := λ X Y, let adj := adjunction.of_right_adjoint G in
  begin
    calc G.map (0 : X ⟶ Y) = adj.unit.app (G.obj X) ≫ G.map (adj.counit.app X) ≫ G.map 0 : _
    ... = adj.unit.app (G.obj X) ≫ G.map ((left_adjoint G).map (0 : _ ⟶ G.obj X)) ≫ G.map 0 : _
    ... = 0 : _,
    { rw adjunction.right_triangle_components_assoc },
    { simp only [← G.map_comp, comp_zero] },
    { simp only [adjunction.unit_naturality_assoc, zero_comp] }
  end }

@[priority 100]
instance preserves_zero_morphisms_of_full (F : C ⥤ D) [full F] : preserves_zero_morphisms F :=
{ map_zero' := λ X Y, calc
  F.map (0 : X ⟶ Y) = F.map (0 ≫ (F.preimage (0 : F.obj Y ⟶ F.obj Y))) : by rw zero_comp
                ... = 0 : by rw [F.map_comp, F.image_preimage, comp_zero] }

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
