-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.natural_isomorphism
import category_theory.whiskering
import category_theory.const
import category_theory.opposites
import category_theory.yoneda

universes v u u' -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

open category_theory
open category_theory.category
open category_theory.functor

namespace category_theory

namespace functor
variables {J C} (F : J ⥤ C)

/--
`F.cones` is the functor assigning to an object `X` the type of
natural transformations from the constant functor with value `X` to `F`.
An object representing this functor is a limit of `F`.
-/
def cones : Cᵒᵖ ⥤ Type v := (const Jᵒᵖ ⋙ op_inv J C) ⋙ (yoneda.obj F)

lemma cones_obj (X : C) : F.cones.obj X = ((const J).obj X ⟹ F) := rfl

/--
`F.cocones` is the functor assigning to an object `X` the type of
natural transformations from `F` to the constant functor with value `X`.
An object corepresenting this functor is a colimit of `F`.
-/
def cocones : C ⥤ Type v := (const J) ⋙ (coyoneda.obj F)

lemma cocones_obj (X : C) : F.cocones.obj X = (F ⟹ (const J).obj X) := rfl

end functor

section
variables (J C)

def cones : (J ⥤ C) ⥤ (Cᵒᵖ ⥤ Type v) :=
{ obj := functor.cones,
  map := λ F G f, whisker_left _ (yoneda.map f) }

def cocones : (J ⥤ C)ᵒᵖ ⥤ (C ⥤ Type v) :=
{ obj := functor.cocones,
  map := λ F G f, whisker_left _ (coyoneda.map f) }

variables {J C}

@[simp] lemma cones_obj (F : J ⥤ C) : (cones J C).obj F = F.cones := rfl
@[simp] lemma cones_map  {F G : J ⥤ C} {f : F ⟶ G} :
(cones J C).map f = (whisker_left _ (yoneda.map f)) := rfl

@[simp] lemma cocones_obj (F : J ⥤ C) : (cocones J C).obj F = F.cocones := rfl
@[simp] lemma cocones_map  {F G : J ⥤ C} {f : F ⟶ G} :
(cocones J C).map f = (whisker_left _ (coyoneda.map f)) := rfl

end

namespace limits

/--
A `c : cone F` is:
* an object `c.X` and
* a natural transformation `c.π : c.X ⟹ F` from the constant `c.X` functor to `F`.

`cone F` is equivalent, in the obvious way, to `Σ X, F.cones.obj X`.
-/
structure cone (F : J ⥤ C) :=
(X : C)
(π : (const J).obj X ⟹ F)

@[simp] lemma cone.w {F : J ⥤ C} (c : cone F) {j j' : J} (f : j ⟶ j') :
  c.π.app j ≫ F.map f = c.π.app j' :=
by convert ←(c.π.naturality f).symm; apply id_comp

/--
A `c : cocone F` is
* an object `c.X` and
* a natural transformation `c.ι : F ⟹ c.X` from `F` to the constant `c.X` functor.

`cocone F` is equivalent, in the obvious way, to `Σ X, F.cocones.obj X`.
-/
structure cocone (F : J ⥤ C) :=
(X : C)
(ι : F ⟹ (const J).obj X)

@[simp] lemma cocone.w {F : J ⥤ C} (c : cocone F) {j j' : J} (f : j ⟶ j') :
  F.map f ≫ c.ι.app j' = c.ι.app j :=
by convert ←(c.ι.naturality f); apply comp_id


variables {F : J ⥤ C}

namespace cone

@[simp] def extensions (c : cone F) : yoneda.obj c.X ⟶ F.cones :=
{ app := λ X f, ((const J).map f) ≫ c.π }

/-- A map to the vertex of a cone induces a cone by composition. -/
@[simp] def extend (c : cone F) {X : C} (f : X ⟶ c.X) : cone F :=
{ X := X,
  π := c.extensions.app X f }

def postcompose {G : J ⥤ C} (α : F ⟹ G) (c : cone F) : cone G :=
{ X := c.X,
  π := c.π ⊟ α }

def whisker {K : Type v} [small_category K] (E : K ⥤ J) (c : cone F) : cone (E ⋙ F) :=
{ X := c.X,
  π := whisker_left E c.π }

@[simp] lemma whisker_π_app (c : cone F) {K : Type v} [small_category K] (E : K ⥤ J) (k : K) :
  (c.whisker E).π.app k = (c.π).app (E.obj k) := rfl
end cone

namespace cocone
@[simp] def extensions (c : cocone F) : coyoneda.obj c.X ⟶ F.cocones :=
{ app := λ X f, c.ι ≫ ((const J).map f),
  naturality' := by intros X Y f; ext g j; dsimp; rw ←assoc; refl }

/-- A map from the vertex of a cocone induces a cocone by composition. -/
@[simp] def extend (c : cocone F) {X : C} (f : c.X ⟶ X) : cocone F :=
{ X := X,
  ι := c.extensions.app X f }

def precompose {G : J ⥤ C} (α : G ⟹ F) (c : cocone F) : cocone G :=
{ X := c.X,
  ι := α ⊟ c.ι }

def whisker {K : Type v} [small_category K] (E : K ⥤ J) (c : cocone F) : cocone (E ⋙ F) :=
{ X := c.X,
  ι := whisker_left E c.ι }

@[simp] lemma whisker_ι_app (c : cocone F) {K : Type v} [small_category K] (E : K ⥤ J) (k : K) :
  (c.whisker E).ι.app k = (c.ι).app (E.obj k) := rfl
end cocone

structure cone_morphism (A B : cone F) :=
(hom : A.X ⟶ B.X)
(w'  : ∀ j : J, hom ≫ B.π.app j = A.π.app j . obviously)

restate_axiom cone_morphism.w'
attribute [simp] cone_morphism.w

@[extensionality] lemma cone_morphism.ext {A B : cone F} {f g : cone_morphism A B}
  (w : f.hom = g.hom) : f = g :=
by cases f; cases g; simpa using w

instance cone.category : category.{v} (cone F) :=
{ hom  := λ A B, cone_morphism A B,
  comp := λ X Y Z f g,
  { hom := f.hom ≫ g.hom,
    w' := by intro j; rw [assoc, g.w, f.w] },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cones
@[simp] lemma id.hom   (c : cone F) : (𝟙 c : cone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {c d e : cone F} (f : c ⟶ d) (g : d ⟶ e) :
  (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- To give an isomorphism between cones, it suffices to give an
  isomorphism between their vertices which commutes with the cone
  maps. -/
@[extensionality] def ext {c c' : cone F}
  (φ : c.X ≅ c'.X) (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j) : c ≅ c' :=
{ hom := { hom := φ.hom },
  inv := { hom := φ.inv, w' := λ j, φ.inv_comp_eq.mpr (w j) } }

section
variables {D : Type u'} [𝒟 : category.{v} D]
include 𝒟

@[simp] def functoriality (G : C ⥤ D) : cone F ⥤ cone (F ⋙ G) :=
{ obj := λ A,
  { X := G.obj A.X,
    π := { app := λ j, G.map (A.π.app j), naturality' := by intros; erw ←G.map_comp; tidy } },
  map := λ X Y f,
  { hom := G.map f.hom,
    w'  := by intros; rw [←functor.map_comp, f.w] } }
end
end cones


structure cocone_morphism (A B : cocone F) :=
(hom : A.X ⟶ B.X)
(w'  : ∀ j : J, A.ι.app j ≫ hom = B.ι.app j . obviously)

restate_axiom cocone_morphism.w'
attribute [simp] cocone_morphism.w

@[extensionality] lemma cocone_morphism.ext
  {A B : cocone F} {f g : cocone_morphism A B} (w : f.hom = g.hom) : f = g :=
by cases f; cases g; simpa using w

instance cocone.category : category.{v} (cocone F) :=
{ hom  := λ A B, cocone_morphism A B,
  comp := λ _ _ _ f g,
  { hom := f.hom ≫ g.hom,
    w' := by intro j; rw [←assoc, f.w, g.w] },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cocones
@[simp] lemma id.hom   (c : cocone F) : (𝟙 c : cocone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {c d e : cocone F} (f : c ⟶ d) (g : d ⟶ e) :
  (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[extensionality] def ext {c c' : cocone F}
  (φ : c.X ≅ c'.X) (w : ∀ j, c.ι.app j ≫ φ.hom = c'.ι.app j) : c ≅ c' :=
{ hom := { hom := φ.hom },
  inv := { hom := φ.inv, w' := λ j, φ.comp_inv_eq.mpr (w j).symm } }

section
variables {D : Type u'} [𝒟 : category.{v} D]
include 𝒟

@[simp] def functoriality (G : C ⥤ D) : cocone F ⥤ cocone (F ⋙ G) :=
{ obj := λ A,
  { X := G.obj A.X,
    ι := { app := λ j, G.map (A.ι.app j), naturality' := by intros; erw ←G.map_comp; tidy } },
  map := λ _ _ f,
  { hom := G.map f.hom,
    w'  := by intros; rw [←functor.map_comp, cocone_morphism.w] } }
end
end cocones

end limits

namespace functor

variables {D : Type u'} [category.{v} D]
variables {F : J ⥤ C} {G : J ⥤ C} (H : C ⥤ D)

open category_theory.limits

/-- The image of a cone in C under a functor G : C ⥤ D is a cone in D. -/
def map_cone   (c : cone F)   : cone (F ⋙ H)   := (cones.functoriality H).obj c
/-- The image of a cocone in C under a functor G : C ⥤ D is a cocone in D. -/
def map_cocone (c : cocone F) : cocone (F ⋙ H) := (cocones.functoriality H).obj c

def map_cone_morphism   {c c' : cone F}   (f : cone_morphism c c')   :
  cone_morphism   (H.map_cone c)   (H.map_cone c')   := (cones.functoriality H).map f
def map_cocone_morphism {c c' : cocone F} (f : cocone_morphism c c') :
  cocone_morphism (H.map_cocone c) (H.map_cocone c') := (cocones.functoriality H).map f

@[simp] lemma map_cone_π (c : cone F) (j : J) :
  (map_cone H c).π.app j = H.map (c.π.app j) := rfl
@[simp] lemma map_cocone_ι (c : cocone F) (j : J) :
  (map_cocone H c).ι.app j = H.map (c.ι.app j) := rfl

end functor

end category_theory
