/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.has_limits
import category_theory.concrete_category.basic

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

-- We now prove a lemma about naturality of cones over functors into bundled categories.
namespace cone

/-- Naturality of a cone over functors to a concrete category. -/
@[simp] lemma w_apply {F : J ⥤ C} (s : cone F) {j j' : J} (f : j ⟶ j') (x : s.X) :
   F.map f (s.π.app j x) = s.π.app j' x :=
begin
  convert congr_fun (congr_arg (λ k : s.X ⟶ F.obj j', (k : s.X → F.obj j')) (s.w f)) x,
  simp only [coe_comp],
end

@[simp]
lemma w_forget_apply (F : J ⥤ C) (s : cone (F ⋙ forget C)) {j j' : J} (f : j ⟶ j') (x : s.X) :
  F.map f (s.π.app j x) = s.π.app j' x :=
congr_fun (s.w f : _) x

end cone

namespace cocone

/-- Naturality of a cocone over functors into a concrete category. -/
@[simp] lemma w_apply {F : J ⥤ C} (s : cocone F) {j j' : J} (f : j ⟶ j') (x : F.obj j) :
  s.ι.app j' (F.map f x) = s.ι.app j x :=
begin
  convert congr_fun (congr_arg (λ k : F.obj j ⟶ s.X, (k : F.obj j → s.X)) (s.w f)) x,
  simp only [coe_comp],
end

@[simp]
lemma w_forget_apply (F : J ⥤ C) (s : cocone (F ⋙ forget C)) {j j' : J} (f : j ⟶ j') (x : F.obj j) :
  s.ι.app j' (F.map f x) = (s.ι.app j x : s.X) :=
congr_fun (s.w f : _) x

end cocone

section has_limit

@[simp]
lemma limit.lift_π_apply (F : J ⥤ C) [has_limit F] (s : cone F) (j : J) (x : s.X) :
  limit.π F j (limit.lift F s x) = s.π.app j x :=
begin
  have w := congr_arg (λ f : s.X ⟶ F.obj j, (f : s.X → F.obj j) x) (limit.lift_π s j),
  dsimp at w,
  rwa coe_comp at w,
end

@[simp]
lemma limit.w_apply (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') (x : limit F) :
  F.map f (limit.π F j x) = limit.π F j' x :=
begin
  have w := congr_arg (λ f : limit F ⟶ F.obj j', (f : limit F → F.obj j') x) (limit.w F f),
  dsimp at w,
  rwa coe_comp at w,
end

end has_limit

section has_colimit

@[simp]
lemma colimit.ι_desc_apply (F : J ⥤ C) [has_colimit F] (s : cocone F) (j : J) (x : F.obj j) :
  colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
begin
  have w := congr_arg (λ f : F.obj j ⟶ s.X, (f : F.obj j → s.X) x) (colimit.ι_desc s j),
  dsimp at w,
  rwa coe_comp at w,
end

@[simp]
lemma colimit.w_apply (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') (x : F.obj j) :
  colimit.ι F j' (F.map f x) = colimit.ι F j x :=
begin
  have w := congr_arg (λ f : F.obj j ⟶ colimit F, (f : F.obj j → colimit F) x) (colimit.w F f),
  dsimp at w,
  rwa coe_comp at w,
end

end has_colimit

end category_theory.limits
