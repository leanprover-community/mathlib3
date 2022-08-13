/-
Copyright (c) 2022 Markus Himmel All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.preserves.filtered
import category_theory.limits.unit

universes v u

open category_theory category_theory.limits category_theory.functor

namespace category_theory
variables {C : Type u} [category.{v} C]

/-- An ind object presentation is a witness that a presheaf `X` is a filtered colimit of
    representables. -/
structure ind_object_presentation (X : Cᵒᵖ ⥤ Type v) :=
(J : Type v)
[J_category : small_category J]
[J_filtered : is_filtered J]
(F : J ⥤ C)
(ι : F ⋙ yoneda ⟶ (const J).obj X)
(is_colimit : is_colimit (cocone.mk X ι))

instance ind_object_presentation_J_category {X : Cᵒᵖ ⥤ Type v} (h : ind_object_presentation X) :
  small_category h.J :=
h.J_category

instance ind_object_presentation_J_filtered {X : Cᵒᵖ ⥤ Type v} (h : ind_object_presentation X) :
  is_filtered h.J :=
h.J_filtered

/-- A presheaf is an ind object if it is a filtered colimit of representables. -/
def is_ind_object (X : Cᵒᵖ ⥤ Type v) : Prop :=
nonempty (ind_object_presentation X)

def ind_object_presentation_of_representable (X : C) : ind_object_presentation (yoneda.obj X) :=
{ J := discrete punit,
  J_category := infer_instance,
  J_filtered := infer_instance,
  F := functor.from_punit X,
  ι := (punit_cocone' _).ι,
  is_colimit := punit_cocone'_is_colimit _ }

lemma is_ind_object_of_representable (X : C) : is_ind_object (yoneda.obj X) :=
⟨ind_object_presentation_of_representable X⟩

def ind_object_presentation_of_iso (X Y : Cᵒᵖ ⥤ Type v) (i : X ≅ Y) (h : ind_object_presentation X) :
  ind_object_presentation Y :=
{ J := h.J,
  J_category := infer_instance,
  J_filtered := infer_instance,
  F := h.F,
  ι := _,
  is_colimit := _ }

section
variables (C)

@[derive category]
def ind_category := full_subcategory (λ (X : Cᵒᵖ ⥤ Type v), is_ind_object X)

@[derive full, derive faithful]
def to_ind_category : C ⥤ ind_category C :=
full_subcategory.lift _ yoneda is_ind_object_of_representable

@[derive full, derive faithful]
def to_presheaf : ind_category C ⥤ Cᵒᵖ ⥤ Type v :=
full_subcategory_inclusion _

end

end category_theory
