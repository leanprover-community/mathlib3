-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn

import category_theory.natural_transformation

namespace category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

open nat_trans category category_theory.functor

variables (C : Sort u₁) [𝒞 : category.{v₁} C] (D : Sort u₂) [𝒟 : category.{v₂} D]
include 𝒞 𝒟

/--
`functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance functor.category : category.{(max u₁ v₂ 1)} (C ⥤ D) :=
{ hom     := λ F G, nat_trans F G,
  id      := λ F, nat_trans.id F,
  comp    := λ _ _ _ α β, vcomp α β }

variables {C D} {E : Sort u₃} [ℰ : category.{v₃} E]
variables {F G H I : C ⥤ D}

namespace nat_trans

@[simp] lemma vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β := rfl

lemma congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by rw h
@[simp] lemma id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl
@[simp] lemma comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
  (α ≫ β).app X = α.app X ≫ β.app X := rfl

include ℰ

lemma app_naturality {F G : C ⥤ (D ⥤ E)} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
  ((F.obj X).map f) ≫ ((T.app X).app Z) = ((T.app X).app Y) ≫ ((G.obj X).map f) :=
(T.app X).naturality f

lemma naturality_app {F G : C ⥤ (D ⥤ E)} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
  ((F.map f).app Z) ≫ ((T.app Y).app Z) = ((T.app X).app Z) ≫ ((G.map f).app Z) :=
congr_fun (congr_arg app (T.naturality f)) Z

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
def hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : (F ⋙ H) ⟶ (G ⋙ I) :=
{ app         := λ X : C, (β.app (F.obj X)) ≫ (I.map (α.app X)),
  naturality' := begin
                   intros, rw [functor.comp_map, functor.comp_map, assoc_symm, naturality, assoc],
                   rw [← map_comp I, naturality, map_comp, assoc]
                 end }

infix ` ◫ `:80 := hcomp

@[simp] lemma hcomp_app {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) (X : C) :
  (α ◫ β).app X = (β.app (F.obj X)) ≫ (I.map (α.app X)) := rfl

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we need to use associativity of functor composition

lemma exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H)
  (γ : I ⟶ J) (δ : J ⟶ K) : (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ (β ◫ δ) :=
by { ext, intros, dsimp, rw [assoc, assoc, map_comp, assoc_symm (δ.app _), ← naturality, assoc] }

end nat_trans
open nat_trans
namespace functor

include ℰ

protected def flip (F : C ⥤ (D ⥤ E)) : D ⥤ (C ⥤ E) :=
{ obj := λ k,
  { obj := λ j, (F.obj j).obj k,
    map := λ j j' f, (F.map f).app k,
    map_id' := λ X, begin rw category_theory.functor.map_id, refl end,
    map_comp' := λ X Y Z f g, by rw [map_comp, ←comp_app] },
  map := λ c c' f,
  { app := λ j, (F.obj j).map f,
    naturality' := λ X Y g, by dsimp; rw ←naturality } }.

@[simp] lemma flip_obj_map (F : C ⥤ (D ⥤ E)) {c c' : C} (f : c ⟶ c') (d : D) :
  ((F.flip).obj d).map f = (F.map f).app d := rfl

end functor

end category_theory
