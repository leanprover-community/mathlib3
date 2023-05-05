/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.adjunction.whiskering
import category_theory.sites.sheafification
import category_theory.sites.whiskering

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


In this file, we show that an adjunction `F ⊣ G` induces an adjunction between
categories of sheaves, under certain hypotheses on `F` and `G`.

-/

namespace category_theory

open category_theory.grothendieck_topology
open category_theory
open category_theory.limits
open opposite

universes w₁ w₂ v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w₁} [category.{max v u} D]
variables {E : Type w₂} [category.{max v u} E]
variables {F : D ⥤ E} {G : E ⥤ D}
variables [∀ (X : C) (S : J.cover X) (P : Cᵒᵖ ⥤ D),
  preserves_limit (S.index P).multicospan F]

variables
  [concrete_category.{max v u} D]
  [preserves_limits (forget D)]

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbreviation Sheaf_forget : Sheaf J D ⥤ SheafOfTypes J :=
Sheaf_compose J (forget D) ⋙ (Sheaf_equiv_SheafOfTypes J).functor

-- We need to sheafify...
variables
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
  [reflects_isomorphisms (forget D)]

namespace Sheaf
noncomputable theory

/-- This is the functor sending a sheaf `X : Sheaf J E` to the sheafification
of `X ⋙ G`. -/
abbreviation compose_and_sheafify (G : E ⥤ D) : Sheaf J E ⥤ Sheaf J D :=
Sheaf_to_presheaf J E ⋙ (whiskering_right _ _ _).obj G ⋙ presheaf_to_Sheaf J D

/-- An auxiliary definition to be used in defining `category_theory.Sheaf.adjunction` below. -/
@[simps]
def compose_equiv (adj : G ⊣ F) (X : Sheaf J E) (Y : Sheaf J D) :
((compose_and_sheafify J G).obj X ⟶ Y) ≃ (X ⟶ (Sheaf_compose J F).obj Y) :=
let A := adj.whisker_right Cᵒᵖ in
{ to_fun := λ η, ⟨A.hom_equiv _ _ (J.to_sheafify _  ≫ η.val)⟩,
  inv_fun := λ γ, ⟨J.sheafify_lift ((A.hom_equiv _ _).symm ((Sheaf_to_presheaf _ _).map γ)) Y.2⟩,
  left_inv := begin
    intros η,
    ext1,
    dsimp,
    symmetry,
    apply J.sheafify_lift_unique,
    rw equiv.symm_apply_apply,
  end,
  right_inv := begin
    intros γ,
    ext1,
    dsimp,
    rw [J.to_sheafify_sheafify_lift, equiv.apply_symm_apply],
  end }

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
@[simps unit_app_val counit_app_val]
def adjunction (adj : G ⊣ F) : compose_and_sheafify J G ⊣ Sheaf_compose J F :=
adjunction.mk_of_hom_equiv
{ hom_equiv := compose_equiv J adj,
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext1, dsimp, simp },
  hom_equiv_naturality_right' := λ X Y Y' f g, by { ext1, dsimp, simp } }

instance [is_right_adjoint F] : is_right_adjoint (Sheaf_compose J F) :=
⟨_, adjunction J (adjunction.of_right_adjoint F)⟩

section forget_to_type

/-- This is the functor sending a sheaf of types `X` to the sheafification of `X ⋙ G`. -/
abbreviation compose_and_sheafify_from_types (G : Type (max v u) ⥤ D) :
  SheafOfTypes J ⥤ Sheaf J D :=
(Sheaf_equiv_SheafOfTypes J).inverse ⋙ compose_and_sheafify _ G

/-- A variant of the adjunction between sheaf categories, in the case where the right adjoint
is the forgetful functor to sheaves of types. -/
def adjunction_to_types {G : Type (max v u) ⥤ D} (adj : G ⊣ forget D) :
  compose_and_sheafify_from_types J G ⊣ Sheaf_forget J :=
((Sheaf_equiv_SheafOfTypes J).symm.to_adjunction).comp (adjunction J adj)

@[simp]
lemma adjunction_to_types_unit_app_val {G : Type (max v u) ⥤ D} (adj : G ⊣ forget D)
  (Y : SheafOfTypes J) :
  ((adjunction_to_types J adj).unit.app Y).val =
  (adj.whisker_right _).unit.app ((SheafOfTypes_to_presheaf J).obj Y) ≫
  whisker_right (J.to_sheafify _) (forget D) :=
begin
  dsimp [adjunction_to_types, adjunction.comp],
  simpa,
end

@[simp]
lemma adjunction_to_types_counit_app_val {G : Type (max v u) ⥤ D} (adj : G ⊣ forget D)
  (X : Sheaf J D) :
  ((adjunction_to_types J adj).counit.app X).val =
  J.sheafify_lift ((functor.associator _ _ _).hom ≫ (adj.whisker_right _).counit.app _) X.2 :=
begin
  dsimp [adjunction_to_types, adjunction.comp, adjunction.whisker_right],
  rw category.id_comp,
  apply J.sheafify_lift_unique,
  rw [adjunction_counit_app_val, J.sheafify_map_sheafify_lift, J.to_sheafify_sheafify_lift],
  ext,
  dsimp [Sheaf_equiv_SheafOfTypes, equivalence.symm,
    equivalence.to_adjunction, nat_iso.of_components],
  simp,
end

instance [is_right_adjoint (forget D)] : is_right_adjoint (Sheaf_forget J) :=
⟨_, adjunction_to_types J (adjunction.of_right_adjoint (forget D))⟩

end forget_to_type

end Sheaf

end category_theory
