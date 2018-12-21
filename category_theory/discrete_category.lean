-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import data.ulift
import category_theory.natural_transformation
import category_theory.isomorphism
import category_theory.functor_category

namespace category_theory

universes u₁ v₁ u₂ v₂

def discrete (α : Type u₁) := α

instance discrete_category (α : Type u₁) : small_category (discrete α) :=
{ hom  := λ X Y, ulift (plift (X = Y)),
  id   := by tidy,
  comp := by tidy }

variables {C : Type u₂} [𝒞 : category.{u₂ v₂} C]
include 𝒞

namespace functor

@[simp] def of_function {I : Type u₁} (F : I → C) : (discrete I) ⥤ C :=
{ obj := F,
  map := λ X Y f, begin cases f, cases f, cases f, exact 𝟙 (F X) end }

end functor

namespace nat_trans

@[simp] def of_function {I : Type u₁} {F G : I → C} (f : Π i : I, F i ⟶ G i) :
  (functor.of_function F) ⟹ (functor.of_function G) :=
{ app := λ i, f i,
  naturality' := λ X Y g,
  begin
    cases g, cases g, cases g,
    dsimp [functor.of_function],
    simp,
  end }

end nat_trans

namespace discrete
omit 𝒞
def lift {α : Type u₁} {β : Type u₂} (f : α → β) : (discrete α) ⥤ (discrete β) :=
functor.of_function f

include 𝒞
variables (J : Type v₂)

@[simp] lemma functor_map_id
  (F : discrete J ⥤ C) (j : discrete J) (f : j ⟶ j) : F.map f = 𝟙 (F.obj j) :=
begin
  have h : f = 𝟙 j, cases f, cases f, ext,
  rw h,
  simp,
end
end discrete

end category_theory
