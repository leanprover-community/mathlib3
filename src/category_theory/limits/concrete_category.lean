/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.has_limits
import category_theory.concrete_category.basic
import tactic.elementwise

/-!
# Facts about (co)limits of functors into concrete categories
-/

universes w v u

open category_theory

namespace category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C] [concrete_category.{v} C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

attribute [elementwise] cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w

-- namespace cone

-- @[simp]
-- lemma w_forget_apply (F : J ⥤ C) (s : cone (F ⋙ forget C)) {j j' : J} (f : j ⟶ j') (x : s.X) :
--   F.map f (s.π.app j x) = s.π.app j' x :=
-- congr_fun (s.w f : _) x

-- end cone

-- namespace cocone

-- @[simp]
-- lemma w_forget_apply (F : J ⥤ C) (s : cocone (F ⋙ forget C)) {j j' : J} (f : j ⟶ j') (x : F.obj j) :
--   s.ι.app j' (F.map f x) = (s.ι.app j x : s.X) :=
-- congr_fun (s.w f : _) x

-- end cocone

end category_theory.limits
