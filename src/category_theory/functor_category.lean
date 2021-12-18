/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.natural_transformation
import category_theory.isomorphism

/-!
# The category of functors and natural transformations between two fixed categories.

We provide the category instance on `C ⥤ D`, with morphisms the natural transformations.

## Universes

If `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/

namespace category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ u₁ u₂ u₃

open nat_trans category category_theory.functor

variables (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D]

local attribute [simp] vcomp_app
/--
`functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance functor.category : category.{(max u₁ v₂)} (C ⥤ D) :=
{ hom     := λ F G, nat_trans F G,
  id      := λ F, nat_trans.id F,
  comp    := λ _ _ _ α β, vcomp α β }

variables {C D} {E : Type u₃} [category.{v₃} E]
variables {F G H I : C ⥤ D}

namespace nat_trans

@[simp] lemma vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β := rfl

lemma vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) :
  (α ≫ β).app X = (α.app X) ≫ (β.app X) := rfl

lemma congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by rw h
@[simp] lemma id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl
@[simp] lemma comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
  (α ≫ β).app X = α.app X ≫ β.app X := rfl

lemma app_naturality {F G : C ⥤ (D ⥤ E)} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
  ((F.obj X).map f) ≫ ((T.app X).app Z) = ((T.app X).app Y) ≫ ((G.obj X).map f) :=
(T.app X).naturality f

lemma naturality_app {F G : C ⥤ (D ⥤ E)} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
  ((F.map f).app Z) ≫ ((T.app Y).app Z) = ((T.app X).app Z) ≫ ((G.map f).app Z) :=
congr_fun (congr_arg app (T.naturality f)) Z

/-- A natural transformation is a monomorphism if each component is. -/
lemma mono_app_of_mono (α : F ⟶ G) [∀ (X : C), mono (α.app X)] : mono α :=
⟨λ H g h eq, by { ext X, rw [←cancel_mono (α.app X), ←comp_app, eq, comp_app] }⟩

/-- A natural transformation is an epimorphism if each component is. -/
lemma epi_app_of_epi (α : F ⟶ G) [∀ (X : C), epi (α.app X)] : epi α :=
⟨λ H g h eq, by { ext X, rw [←cancel_epi (α.app X), ←comp_app, eq, comp_app] }⟩

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
def hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : (F ⋙ H) ⟶ (G ⋙ I) :=
{ app         := λ X : C, (β.app (F.obj X)) ≫ (I.map (α.app X)),
  naturality' := λ X Y f,
  begin
    rw [functor.comp_map, functor.comp_map, ←assoc, naturality, assoc,
        ←map_comp I, naturality, map_comp, assoc]
  end }

infix ` ◫ `:80 := hcomp

@[simp] lemma hcomp_app {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) (X : C) :
  (α ◫ β).app X = (β.app (F.obj X)) ≫ (I.map (α.app X)) := rfl

@[simp] lemma hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.app X) :=
  by {dsimp, simp} -- See note [dsimp, simp].

lemma id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _ := by simp

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we
-- need to use associativity of functor composition. (It's true without the explicit associator,
-- because functor composition is definitionally associative,
-- but relying on the definitional equality causes bad problems with elaboration later.)

lemma exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H)
  (γ : I ⟶ J) (δ : J ⟶ K) : (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ (β ◫ δ) :=
by ext; simp

end nat_trans
open nat_trans
namespace functor

/-- Flip the arguments of a bifunctor. See also `currying.lean`. -/
protected def flip (F : C ⥤ (D ⥤ E)) : D ⥤ (C ⥤ E) :=
{ obj := λ k,
  { obj := λ j, (F.obj j).obj k,
    map := λ j j' f, (F.map f).app k,
    map_id' := λ X, begin rw category_theory.functor.map_id, refl end,
    map_comp' := λ X Y Z f g, by rw [map_comp, ←comp_app] },
  map := λ c c' f,
  { app := λ j, (F.obj j).map f } }.

@[simp] lemma flip_obj_obj (F : C ⥤ (D ⥤ E)) (c) (d) : (F.flip.obj d).obj c = (F.obj c).obj d := rfl
@[simp] lemma flip_obj_map (F : C ⥤ (D ⥤ E)) {c c' : C} (f : c ⟶ c') (d : D) :
  (F.flip.obj d).map f = (F.map f).app d := rfl
@[simp] lemma flip_map_app (F : C ⥤ (D ⥤ E)) {d d' : D} (f : d ⟶ d') (c : C) :
  (F.flip.map f).app c = (F.obj c).map f := rfl

end functor

@[simp, reassoc] lemma map_hom_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
  (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ :=
by simp [← nat_trans.comp_app, ← functor.map_comp]

@[simp, reassoc] lemma map_inv_hom_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
  (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ :=
by simp [← nat_trans.comp_app, ← functor.map_comp]

end category_theory
