/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.functor_category
import category_theory.isomorphism
import tactic.interactive

namespace category_theory

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ -- declare the `v`'s first; see `category_theory.category` for an explanation
-- An awkward note on universes:
-- we need to make sure we're in `Type`, not `Sort`
-- for both objects and morphisms when taking products.

open sum

section
variables (C : Type u₁) [𝒞 : category.{v₁+1} C] (D : Type u₁) [𝒟 : category.{v₁+1} D]
include 𝒞 𝒟

/--
`sum C D` gives the direct sum of two categories.
-/
instance sum : category.{v₁+1} (C ⊕ D) :=
{ hom     :=
    λ X Y, match X, Y with
    | inl X, inl Y := X ⟶ Y
    | inl X, inr Y := pempty
    | inr X, inl Y := pempty
    | inr X, inr Y := X ⟶ Y
    end,
  id      :=
    λ X, match X with
    | inl X := 𝟙 X
    | inr X := 𝟙 X
    end,
  comp    :=
    λ X Y Z f g, match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g := f ≫ g
    | inr X, inr Y, inr Z, f, g := f ≫ g
    end }

-- TODO the next two simp lemmas seem to cause problems
-- @[simp] lemma sum_id_inl (X : C) : (𝟙 (inl X : C ⊕ D)) = (𝟙 X : X ⟶ X) := rfl
-- @[simp] lemma sum_id_inr (X : D) : (𝟙 (inr X : C ⊕ D)) = (𝟙 X : X ⟶ X) := rfl
@[simp] lemma sum_comp_inl {P Q R : C} (f : (inl P : C ⊕ D) ⟶ inl Q) (g : inl Q ⟶ inl R) :
  f ≫ g = (f : P ⟶ Q) ≫ (g : Q ⟶ R) := rfl
@[simp] lemma sum_comp_inr {P Q R : D} (f : (inr P : C ⊕ D) ⟶ inr Q) (g : inr Q ⟶ inr R) :
  f ≫ g = (f : P ⟶ Q) ≫ (g : Q ⟶ R) := rfl
end

namespace sum

variables (C : Type u₁) [𝒞 : category.{v₁+1} C] (D : Type u₁) [𝒟 : category.{v₁+1} D]
include 𝒞 𝒟

/-- `inl` is the functor `X ↦ inl X`. -/
def inl_ : C ⥤ C ⊕ D :=
{ obj := λ X, inl X,
  map := λ X Y f, f }

@[simp] lemma inl_obj (X : C) : (inl_ C D).obj X = inl X := rfl
@[simp] lemma inl_map {X Y : C} {f : X ⟶ Y} : (inl_ C D).map f = f := rfl

/-- `inr` is the functor `X ↦ inr X`. -/
def inr_ : D ⥤ C ⊕ D :=
{ obj := λ X, inr X,
  map := λ X Y f, f }

@[simp] lemma inr_obj (X : D) : (inr_ C D).obj X = inr X := rfl
@[simp] lemma inr_map {X Y : D} {f : X ⟶ Y} : (inr_ C D).map f = f := rfl

def swap : C ⊕ D ⥤ D ⊕ C :=
{ obj :=
    λ X, match X with
    | inl X := inr X
    | inr X := inl X
    end,
  map :=
    λ X Y f, match X, Y, f with
    | inl X, inl Y, f := f
    | inr X, inr Y, f := f
    end }

@[simp] lemma swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X := rfl
@[simp] lemma swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X := rfl
@[simp] lemma swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f := rfl
@[simp] lemma swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f := rfl

def symmetry : swap C D ⋙ swap D C ≅ functor.id (C ⊕ D) :=
{ hom := { app := λ X, begin cases X; exact 𝟙 _ end },
  inv := { app := λ X, begin cases X; exact 𝟙 _ end } }

end sum

variables {A : Type u₁} [𝒜 : category.{v₁+1} A]
          {B : Type u₁} [ℬ : category.{v₁+1} B]
          {C : Type u₁} [𝒞 : category.{v₁+1} C]
          {D : Type u₁} [𝒟 : category.{v₁+1} D]
include 𝒜 ℬ 𝒞 𝒟

namespace functor

/-- The sum product of two functors. -/
def sum (F : A ⥤ B) (G : C ⥤ D) : A ⊕ C ⥤ B ⊕ D :=
{ obj :=
    λ X, match X with
    | inl X := inl (F.obj X)
    | inr X := inr (G.obj X)
    end,
  map :=
    λ X Y f, match X, Y, f with
    | inl X, inl Y, f := F.map f
    | inr X, inr Y, f := G.map f
    end,
  map_id' := λ X, begin cases X; unfold_aux, erw F.map_id, refl, erw G.map_id, refl end,
  map_comp' :=
    λ X Y Z f g, match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g := by { unfold_aux, erw F.map_comp, refl }
    | inr X, inr Y, inr Z, f, g := by { unfold_aux, erw G.map_comp, refl }
    end }

@[simp] lemma sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) :
  (F.sum G).obj (inl a) = inl (F.obj a) := rfl
@[simp] lemma sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) :
  (F.sum G).obj (inr c) = inr (G.obj c) := rfl
@[simp] lemma sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : inl a ⟶ inl a') :
  (F.sum G).map f = F.map f := rfl
@[simp] lemma sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : inr c ⟶ inr c') :
  (F.sum G).map f = G.map f := rfl
end functor

namespace nat_trans

/-- The sum of two natural transformations. -/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I :=
{ app         :=
    λ X, match X with
    | inl X := α.app X
    | inr X := β.app X
    end,
  naturality' :=
    λ X Y f, match X, Y, f with
    | inl X, inl Y, f := begin unfold_aux, erw α.naturality, refl, end
    | inr X, inr Y, f := begin unfold_aux, erw β.naturality, refl, end
    end }

@[simp] lemma sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
  (sum α β).app (inl a) = α.app a := rfl
@[simp] lemma sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
  (sum α β).app (inr c) = β.app c := rfl
end nat_trans

end category_theory
