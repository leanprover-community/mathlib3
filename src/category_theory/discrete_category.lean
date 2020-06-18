/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import data.ulift
import data.fintype.basic
import category_theory.eq_to_hom

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

/--
A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
def discrete (α : Type u₁) := α

instance discrete_category (α : Type u₁) : small_category (discrete α) :=
{ hom  := λ X Y, ulift (plift (X = Y)),
  id   := λ X, ulift.up (plift.up rfl),
  comp := λ X Y Z g f, by { rcases f with ⟨⟨rfl⟩⟩, exact g } }

namespace discrete

variables {α : Type u₁}

instance [inhabited α] : inhabited (discrete α) :=
by unfold discrete; apply_instance

instance [fintype α] : fintype (discrete α) :=
by { dsimp [discrete], apply_instance }

instance fintype_fun [decidable_eq α] (X Y : discrete α) : fintype (X ⟶ Y) :=
by { apply ulift.fintype }

@[simp] lemma id_def (X : discrete α) : ulift.up (plift.up (eq.refl X)) = 𝟙 X := rfl

end discrete

variables {C : Type u₂} [category.{v₂} C]

namespace functor

/--
Any function `I → C` gives a functor `discrete I ⥤ C`.
-/
def of_function {I : Type u₁} (F : I → C) : discrete I ⥤ C :=
{ obj := F,
  map := λ X Y f, begin cases f, cases f, cases f, exact 𝟙 (F X) end }

@[simp] lemma of_function_obj  {I : Type u₁} (F : I → C) (i : I) :
  (of_function F).obj i = F i := rfl

lemma of_function_map  {I : Type u₁} (F : I → C) {i : discrete I} (f : i ⟶ i) :
  (of_function F).map f = 𝟙 (F i) :=
by { cases f, cases f, cases f, refl }

end functor

namespace nat_trans

/--
For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
def of_function {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := f }

@[simp] lemma of_function_app  {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ⟶ G.obj i) (i) : (of_function f).app i = f i :=
rfl

end nat_trans

namespace nat_iso

/--
For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
def of_function {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) : F ≅ G :=
of_components f (by tidy)

end nat_iso


namespace equivalence

/--
We can promote a type-level `equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
def of_equiv {I J : Type u₁} (e : I ≃ J) : discrete I ≌ discrete J :=
{ functor := functor.of_function (e : I → J),
  inverse := functor.of_function (e.symm : J → I),
  unit_iso := nat_iso.of_function (λ i, eq_to_iso (by simp)),
  counit_iso := nat_iso.of_function (λ j, eq_to_iso (by simp)), }

end equivalence

namespace discrete
variables {J : Type v₁}

open opposite

/-- A discrete category is equivalent to its opposite category. -/
protected def opposite (α : Type u₁) : (discrete α)ᵒᵖ ≌ discrete α :=
let F : discrete α ⥤ (discrete α)ᵒᵖ := functor.of_function (λ x, op x) in
begin
  refine equivalence.mk (functor.left_op F) F _ (nat_iso.of_function $ λ X, by simp [F]),
  refine nat_iso.of_components (λ X, by simp [F]) _,
  tidy
end

@[simp] lemma functor_map_id
  (F : discrete J ⥤ C) {j : discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j) :=
begin
  have h : f = 𝟙 j, { cases f, cases f, ext, },
  rw h,
  simp,
end

end discrete

end category_theory
