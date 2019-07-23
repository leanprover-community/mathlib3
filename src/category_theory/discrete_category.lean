-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison, Floris van Doorn

import data.ulift
import category_theory.opposites category_theory.equivalence

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

-- We only work in `Type`, rather than `Sort`, as we need to use `ulift`.
def discrete (α : Type u₁) := α

instance discrete_category (α : Type u₁) : category (discrete α) :=
{ hom  := (=),
  id   := eq.refl,
  comp := λ X Y Z g f, by { rcases f with rfl, exact g } }

namespace discrete

variables {α : Type u₁}
@[simp] lemma id_def (X : discrete α) : eq.refl X = 𝟙 X := rfl

end discrete

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

namespace functor

@[simp] def of_function {I : Type u₁} (F : I → C) : (discrete I) ⥤ C :=
{ obj := F,
  map := λ X Y f, begin cases f, exact 𝟙 (F X) end }

end functor

namespace nat_trans

@[simp] def of_homs {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := f }

@[simp] def of_function {I : Type u₁} {F G : I → C} (f : Π i : I, F i ⟶ G i) :
  (functor.of_function F) ⟶ (functor.of_function G) :=
of_homs f

end nat_trans

namespace nat_iso

@[simp] def of_isos {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) : F ≅ G :=
of_components f (by tidy)

end nat_iso

namespace discrete
variables {J : Type v₁}

omit 𝒞

def lift {α : Type u₁} {β : Type u₂} (f : α → β) : (discrete α) ⥤ (discrete β) :=
functor.of_function f

open opposite

protected def opposite (α : Type u₁) : (discrete α)ᵒᵖ ≌ discrete α :=
let F : discrete α ⥤ (discrete α)ᵒᵖ := functor.of_function (λ x, op x) in
begin
  refine equivalence.mk (functor.left_op F) F _ (nat_iso.of_isos $ λ X, by simp [F]),
  refine nat_iso.of_components (λ X, by simp [F]) _,
  tidy
end
include 𝒞


@[simp] lemma functor_map_id
  (F : discrete J ⥤ C) {j : discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j) :=
by simp

end discrete

end category_theory
