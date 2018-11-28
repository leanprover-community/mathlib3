-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.types
import category_theory.isomorphism
import category_theory.whiskering

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃
variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A]
variables {B : Type u₂} [ℬ : category.{u₂ v₂} B]
variables {T : Type u₃} [𝒯 : category.{u₃ v₃} T]
include 𝒜 ℬ 𝒯

structure comma (L : A ⥤ T) (R : B ⥤ T) :=
(left : A . obviously)
(right : B . obviously)
(hom : L.obj left ⟶ R.obj right)

variables {L : A ⥤ T} {R : B ⥤ T}

structure comma_morphism (X Y : comma L R) :=
(left : X.left ⟶ Y.left . obviously)
(right : X.right ⟶ Y.right . obviously)
(w' : L.map left ≫ Y.hom = X.hom ≫ R.map right . obviously)

restate_axiom comma_morphism.w'
attribute [simp] comma_morphism.w

namespace comma_morphism
@[extensionality] lemma ext
  {X Y : comma L R} {f g : comma_morphism X Y}
  (l : f.left = g.left) (r : f.right = g.right) : f = g :=
begin
  cases f, cases g,
  congr; assumption
end
end comma_morphism

instance comma_category : category (comma L R) :=
{ hom := comma_morphism,
  id := λ X,
  { left := 𝟙 X.left,
    right := 𝟙 X.right },
  comp := λ X Y Z f g,
  { left := f.left ≫ g.left,
    right := f.right ≫ g.right,
    w' :=
    begin
      rw [functor.map_comp,
          category.assoc,
          g.w,
          ←category.assoc,
          f.w,
          functor.map_comp,
          category.assoc],
    end }}

namespace comma

section simp
variables {X Y Z : comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

@[simp] lemma comp_left  : (f ≫ g).left  = f.left ≫ g.left   := rfl
@[simp] lemma comp_right : (f ≫ g).right = f.right ≫ g.right := rfl

end simp

variables (L) (R)

def fst : comma L R ⥤ A :=
{ obj := λ X, X.left,
  map := λ _ _ f, f.left }

def snd : comma L R ⥤ B :=
{ obj := λ X, X.right,
  map := λ _ _ f, f.right }

@[simp] lemma fst_obj {X : comma L R} : (fst L R).obj X = X.left := rfl
@[simp] lemma snd_obj {X : comma L R} : (snd L R).obj X = X.right := rfl
@[simp] lemma fst_map {X Y : comma L R} {f : X ⟶ Y} : (fst L R).map f = f.left := rfl
@[simp] lemma snd_map {X Y : comma L R} {f : X ⟶ Y} : (snd L R).map f = f.right := rfl

def nat_trans : fst L R ⋙ L ⟹ snd L R ⋙ R :=
{ app := λ X, X.hom }

variables {L₁ : A ⥤ T} {L₂ : A ⥤ T}
variables {R₁ : B ⥤ T} {R₂ : B ⥤ T}

def map_left (l : L₁ ⟹ L₂) : comma L₂ R ⥤ comma L₁ R :=
{ obj := λ X,
  { left  := X.left,
    right := X.right,
    hom   := l.app X.left ≫ X.hom },
  map := λ X Y f,
  { left  := f.left,
    right := f.right,
    w' := by tidy; rw [←category.assoc, l.naturality f.left, category.assoc]; tidy } }

def map_right (r : R₁ ⟹ R₂) : comma L R₁ ⥤ comma L R₂ :=
{ obj := λ X,
  { left  := X.left,
    right := X.right,
    hom   := X.hom ≫ r.app X.right },
  map := λ X Y f,
  { left  := f.left,
    right := f.right,
    w' := by tidy; rw [←r.naturality f.right, ←category.assoc]; tidy } }

section simp

section
variables {X Y : comma L₂ R} {f : X ⟶ Y} {l : L₁ ⟹ L₂}
@[simp] lemma map_left_obj_left  : ((map_left R l).obj X).left  = X.left                := rfl
@[simp] lemma map_left_obj_right : ((map_left R l).obj X).right = X.right               := rfl
@[simp] lemma map_left_obj_hom   : ((map_left R l).obj X).hom   = l.app X.left ≫ X.hom := rfl
@[simp] lemma map_left_map_left  : ((map_left R l).map f).left  = f.left                := rfl
@[simp] lemma map_left_map_right : ((map_left R l).map f).right = f.right               := rfl

@[simp] lemma map_left_id : map_left R (nat_trans.id L) ≅ functor.id _ :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

variables {L₃ : A ⥤ T} {l' : L₂ ⟹ L₃}
@[simp] lemma map_left_comp : (map_left R (l ⊟ l')) ≅ (map_left R l') ⋙ (map_left R l) :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }
end

section
variables {X Y : comma L R₁} {f : X ⟶ Y} {r : R₁ ⟹ R₂}
@[simp] lemma map_right_obj_left  : ((map_right L r).obj X).left  = X.left                 := rfl
@[simp] lemma map_right_obj_right : ((map_right L r).obj X).right = X.right                := rfl
@[simp] lemma map_right_obj_hom   : ((map_right L r).obj X).hom   = X.hom ≫ r.app X.right := rfl
@[simp] lemma map_right_map_left  : ((map_right L r).map f).left  = f.left                 := rfl
@[simp] lemma map_right_map_right : ((map_right L r).map f).right = f.right                := rfl

@[simp] lemma map_right_id : map_right L (nat_trans.id R) ≅ functor.id _ :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }
@[simp] lemma map_right_id' : map_right L (𝟙 R) ≅ functor.id _ :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

variables {R₃ : B ⥤ T} {r' : R₂ ⟹ R₃}
@[simp] lemma map_right_comp : (map_right L (r ⊟ r')) ≅ (map_right L r) ⋙ (map_right L r') :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }
end

end simp

end comma

end category_theory
