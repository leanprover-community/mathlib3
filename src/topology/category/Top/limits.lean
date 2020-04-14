/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import topology.category.Top.basic
import category_theory.limits.types
import category_theory.limits.preserves

open topological_space
open category_theory
open category_theory.limits

universe u

namespace Top

variables {J : Type u} [small_category J]

local notation `forget` := forget Top

def limit (F : J ⥤ Top.{u}) : cone F :=
{ X := ⟨limit (F ⋙ forget), ⨅j, (F.obj j).str.induced (limit.π (F ⋙ forget) j)⟩,
  π :=
  { app := λ j, ⟨limit.π (F ⋙ forget) j, continuous_iff_le_induced.mpr (infi_le _ _)⟩,
    naturality' := λ j j' f, subtype.eq ((limit.cone (F ⋙ forget)).π.naturality f) } }

def limit_is_limit (F : J ⥤ Top.{u}) : is_limit (limit F) :=
by { refine is_limit.of_faithful forget (limit.is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_coinduced_le.mpr (le_infi $ λ j,
       coinduced_le_iff_le_induced.mp $ continuous_iff_coinduced_le.mp (s.π.app j).property) }

instance Top_has_limits : has_limits.{u} Top.{u} :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI { cone := limit F, is_limit := limit_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget)) } }

def colimit (F : J ⥤ Top.{u}) : cocone F :=
{ X := ⟨colimit (F ⋙ forget), ⨆ j, (F.obj j).str.coinduced (colimit.ι (F ⋙ forget) j)⟩,
  ι :=
  { app := λ j, ⟨colimit.ι (F ⋙ forget) j, continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
    naturality' := λ j j' f, subtype.eq ((colimit.cocone (F ⋙ forget)).ι.naturality f) } }

def colimit_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit F) :=
by { refine is_colimit.of_faithful forget (colimit.is_colimit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_le_induced.mpr (supr_le $ λ j,
       coinduced_le_iff_le_induced.mp $ continuous_iff_coinduced_le.mp (s.ι.app j).property) }

instance Top_has_colimits : has_colimits.{u} Top.{u} :=
{ has_colimits_of_shape := λ J 𝒥,
  { has_colimit := λ F, by exactI { cocone := colimit F, is_colimit := colimit_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit.is_colimit F) (colimit.is_colimit (F ⋙ forget)) } }

end Top
