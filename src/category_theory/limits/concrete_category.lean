/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.cones
import category_theory.concrete_category.bundled_hom

/-!
# Facts about limits of functors into concrete categories
-/

universes u

open category_theory

namespace category_theory.limits

-- We now prove a lemma about naturality of cones over functors into bundled categories.
namespace cone

variables {J : Type u} [small_category J]
variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

/-- Naturality of a cone over functors to a concrete category. -/
@[simp] lemma naturality_concrete {G : J ⥤ C} (s : cone G) {j j' : J} (f : j ⟶ j') (x : s.X) :
   (G.map f) ((s.π.app j) x) = (s.π.app j') x :=
begin
  convert congr_fun (congr_arg (λ k : s.X ⟶ G.obj j', (k : s.X → G.obj j')) (s.π.naturality f).symm) x;
  { dsimp, simp [-cone.w] },
end

end cone

namespace cocone

variables {J : Type u} [small_category J]
variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

/-- Naturality of a cocone over functors into a concrete category. -/
@[simp] lemma naturality_concrete {G : J ⥤ C} (s : cocone G) {j j' : J} (f : j ⟶ j') (x : G.obj j) :
  (s.ι.app j') ((G.map f) x) = (s.ι.app j) x :=
begin
  convert congr_fun (congr_arg (λ k : G.obj j ⟶ s.X, (k : G.obj j → s.X)) (s.ι.naturality f)) x;
  { dsimp, simp [-nat_trans.naturality, -cocone.w] },
end

end cocone

end category_theory.limits
