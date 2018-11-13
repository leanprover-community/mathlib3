-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.natural_transformation

namespace category_theory

universes u v u₁ v₁ u₂ v₂ u₃ v₃

open nat_trans

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (D : Type u₂) [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

/--
`functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance functor.category :
  category.{(max u₁ v₁ u₂ v₂) (max u₁ v₂)} (C ⥤ D) :=
{ hom     := λ F G, F ⟹ G,
  id      := λ F, nat_trans.id F,
  comp    := λ _ _ _ α β, α ⊟ β }

namespace functor.category

section
variables {C D}

@[simp] lemma id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟹ F).app X = 𝟙 (F.obj X) := rfl
@[simp] lemma comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
  ((α ≫ β) : F ⟹ H).app X = (α : F ⟹ G).app X ≫ (β : G ⟹ H).app X := rfl
end

namespace nat_trans
-- This section gives two lemmas about natural transformations
-- between functors into functor categories,
-- spelling them out in components.

variables {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include ℰ

lemma app_naturality {F G : C ⥤ (D ⥤ E)} (T : F ⟹ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
  ((F.obj X).map f) ≫ ((T.app X).app Z) = ((T.app X).app Y) ≫ ((G.obj X).map f) :=
(T.app X).naturality f

lemma naturality_app {F G : C ⥤ (D ⥤ E)} (T : F ⟹ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
  ((F.map f).app Z) ≫ ((T.app Y).app Z) = ((T.app X).app Z) ≫ ((G.map f).app Z) :=
congr_fun (congr_arg app (T.naturality f)) Z

end nat_trans

end functor.category

namespace functor

omit 𝒟
variables {C D} {J K : Type v} [small_category J] [small_category K]

protected def flip (F : J ⥤ (K ⥤ C)) : K ⥤ (J ⥤ C) :=
{ obj := λ k,
  { obj := λ j, (F.obj j).obj k,
    map := λ j j' f, (F.map f).app k,
    map_id' := λ X, begin rw category_theory.functor.map_id, refl end,
    map_comp' := λ X Y Z f g, by rw [functor.map_comp, ←functor.category.comp_app] },
  map := λ c c' f,
  { app := λ j, (F.obj j).map f,
    naturality' := λ X Y g, by dsimp; rw ←nat_trans.naturality } }.

@[simp] lemma flip_obj_map (F : J ⥤ (K ⥤ C)) {j j' : J} (f : j ⟶ j') (k : K) :
  ((F.flip).obj k).map f = (F.map f).app k := rfl

end functor

end category_theory
