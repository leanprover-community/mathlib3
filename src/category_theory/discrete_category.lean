/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import data.ulift
import data.fintype
import category_theory.opposites category_theory.equivalence

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

def discrete (α : Type u₁) := α

instance {α : Type u₁} [fintype α] : fintype (discrete α) :=
by { dsimp [discrete], apply_instance }

instance discrete_category (α : Type u₁) : small_category (discrete α) :=
{ hom  := λ X Y, ulift (plift (X = Y)),
  id   := λ X, ulift.up (plift.up rfl),
  comp := λ X Y Z g f, by { rcases f with ⟨⟨rfl⟩⟩, exact g } }

namespace discrete

variables {α : Type u₁}

instance [decidable_eq α] (X Y : discrete α) : fintype (X ⟶ Y) :=
by { apply ulift.fintype }

@[simp] lemma id_def (X : discrete α) : ulift.up (plift.up (eq.refl X)) = 𝟙 X := rfl

end discrete

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

namespace functor

def of_function {I : Type u₁} (F : I → C) : (discrete I) ⥤ C :=
{ obj := F,
  map := λ X Y f, begin cases f, cases f, cases f, exact 𝟙 (F X) end }

@[simp] lemma of_function_obj  {I : Type u₁} (F : I → C) (i : I) : (of_function F).obj i = F i := rfl
@[simp] lemma of_function_map  {I : Type u₁} (F : I → C) {i : discrete I} (f : i ⟶ i) :
  (of_function F).map f = 𝟙 (F i) :=
by { cases f, cases f, cases f, refl }

end functor

namespace nat_trans

def of_homs {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := f }

def of_function {I : Type u₁} {F G : I → C} (f : Π i : I, F i ⟶ G i) :
  (functor.of_function F) ⟶ (functor.of_function G) :=
of_homs f

@[simp] lemma of_function_app {I : Type u₁} {F G : I → C} (f : Π i : I, F i ⟶ G i) (i : I) :
  (of_function f).app i = f i := rfl

end nat_trans

namespace nat_iso

def of_isos {I : Type u₁} {F G : discrete I ⥤ C}
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
begin
  have h : f = 𝟙 j, cases f, cases f, ext,
  rw h,
  simp,
end

end discrete

end category_theory
