/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import category_theory.limits.preserves.shapes.terminal

/-!

# Limits and the category of (co)cones

A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
categories of cones preserves limiting properties. We also provide the dual.
-/

namespace category_theory.limits

open category_theory

universes v u

variables {J : Type v} [category.{v} J] {J' : Type v} [category.{v} J']
variables {C : Type u} [category.{v} C] {C' : Type u} [category.{v} C']

/-- A cone is a limit cone iff it is terminal. -/
def cone_limiting_iff_terminal {F : J ⥤ C} (c : cone F) : is_limit c ≃ is_terminal c :=
is_limit.iso_unique_cone_morphism.to_equiv.trans
({ to_fun  := λ h, by exactI is_terminal.of_unique _,
   inv_fun := λ h s, ⟨⟨is_terminal.from h s⟩, λ a, is_terminal.hom_ext h a _⟩,
   left_inv := by tidy,
   right_inv := by tidy } :
  (Π (s : limits.cone F), unique (s ⟶ c)) ≃ is_terminal c)

lemma limit_cone_lift_eq_terminal_from {F : J ⥤ C} (c : cone F) (hc : is_limit c) (s : cone F) :
  hc.lift_cone_morphism s =
    is_terminal.from (cone_limiting_iff_terminal _ hc) _ := rfl

lemma terminal_from_eq_limit_cone_lift {F : J ⥤ C} (c : cone F) (hc : is_terminal c) (s : cone F) :
  is_terminal.from hc s =
    ((cone_limiting_iff_terminal _).symm hc).lift_cone_morphism s :=
by convert (limit_cone_lift_eq_terminal_from c _ s).symm

/-- If `G : cone F ⥤ cone F'` preserves terminal objects, it preserves limit cones. -/
def is_limit_of_preserves_cone_terminal {F : J ⥤ C} {F' : J' ⥤ C'} (G : cone F ⥤ cone F')
  [preserves_limit (functor.empty _) G] (c : cone F) (hc : is_limit c) :
  is_limit (G.obj c) :=
(cone_limiting_iff_terminal _).symm $
  is_terminal_obj_of_is_terminal _ _ (cone_limiting_iff_terminal _ hc)

/-- If `G : cone F ⥤ cone F'` reflects terminal objects, it reflects limit cones. -/
def is_limit_of_reflects_cone_terminal {F : J ⥤ C} {F' : J' ⥤ C'} (G : cone F ⥤ cone F')
  [reflects_limit (functor.empty _) G] (c : cone F) (hc : is_limit (G.obj c)) :
  is_limit c :=
(cone_limiting_iff_terminal _).symm $
  is_terminal_of_is_terminal_obj _ _ (cone_limiting_iff_terminal _ hc)

/-- A cocone is a colimit cocone iff it is initial. -/
def cocone_colimiting_iff_initial {F : J ⥤ C} (c : cocone F) : is_colimit c ≃ is_initial c :=
is_colimit.iso_unique_cocone_morphism.to_equiv.trans
({ to_fun  := λ h, by exactI is_initial.of_unique _,
   inv_fun := λ h s, ⟨⟨is_initial.to h s⟩, λ a, is_initial.hom_ext h a _⟩,
   left_inv := by tidy,
   right_inv := by tidy } :
  (Π (s : limits.cocone F), unique (c ⟶ s)) ≃ is_initial c)

lemma colimit_cocone_desc_eq_initial_to {F : J ⥤ C} (c : colimit_cocone F) (s : cocone F) :
  c.is_colimit.desc_cocone_morphism s =
    is_initial.to (cocone_colimiting_iff_initial _ c.is_colimit) _ := rfl

lemma initial_to_eq_colimit_cocone_lift {F : J ⥤ C} (c : cocone F)
  (hc : is_initial c) (s : cocone F) :
  is_initial.to hc s = ((cocone_colimiting_iff_initial _).symm hc).desc_cocone_morphism s :=
by convert (colimit_cocone_desc_eq_initial_to ⟨c, _⟩ s).symm

/-- If `G : cocone F ⥤ cocone F'` preserves initial objects, it preserves colimit cocones. -/
def is_colimit_of_preserves_cocone_initial {F : J ⥤ C} {F' : J' ⥤ C'} (G : cocone F ⥤ cocone F')
  [preserves_colimit (functor.empty _) G] (c : cocone F) (hc : is_colimit c) :
  is_colimit (G.obj c) :=
(cocone_colimiting_iff_initial _).symm $
  is_initial_obj_of_is_initial _ _ (cocone_colimiting_iff_initial _ hc)

/-- If `G : cocone F ⥤ cocone F'` reflects initial objects, it reflects colimit cocones. -/
def is_colimit_of_reflects_cocone_initial {F : J ⥤ C} {F' : J' ⥤ C'} (G : cocone F ⥤ cocone F')
  [reflects_colimit (functor.empty _) G] (c : cocone F) (hc : is_colimit (G.obj c)) :
  is_colimit c :=
(cocone_colimiting_iff_initial _).symm $
  is_initial_of_is_initial_obj _ _ (cocone_colimiting_iff_initial _ hc)

end category_theory.limits
