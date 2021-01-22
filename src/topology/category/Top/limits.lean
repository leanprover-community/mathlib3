/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import topology.category.Top.basic
import category_theory.limits.types
import category_theory.limits.preserves.basic

open topological_space
open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace Top

variables {J : Type u} [small_category J]

local notation `forget` := forget Top

/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone (F : J ⥤ Top.{u}) : cone F :=
{ X := ⟨(types.limit_cone (F ⋙ forget)).X, ⨅j, (F.obj j).str.induced ((types.limit_cone (F ⋙ forget)).π.app j)⟩,
  π :=
  { app := λ j, ⟨(types.limit_cone (F ⋙ forget)).π.app j, continuous_iff_le_induced.mpr (infi_le _ _)⟩,
    naturality' := λ j j' f, continuous_map.coe_inj ((types.limit_cone (F ⋙ forget)).π.naturality f) } }

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone F) :=
by { refine is_limit.of_faithful forget (types.limit_cone_is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_coinduced_le.mpr (le_infi $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.π.app j).continuous : _) ) }

instance Top_has_limits : has_limits.{u} Top.{u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget)) } }

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone (F : J ⥤ Top.{u}) : cocone F :=
{ X := ⟨(types.colimit_cocone (F ⋙ forget)).X, ⨆ j, (F.obj j).str.coinduced ((types.colimit_cocone (F ⋙ forget)).ι.app j)⟩,
  ι :=
  { app := λ j, ⟨(types.colimit_cocone (F ⋙ forget)).ι.app j, continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
    naturality' := λ j j' f, continuous_map.coe_inj ((types.colimit_cocone (F ⋙ forget)).ι.naturality f) } }

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit_cocone F) :=
by { refine is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_le_induced.mpr (supr_le $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.ι.app j).continuous : _) ) }

instance Top_has_colimits : has_colimits.{u} Top.{u} :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk { cocone := colimit_cocone F, is_colimit := colimit_cocone_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

end Top
