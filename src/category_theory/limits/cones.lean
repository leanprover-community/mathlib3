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

-- There is an awkward difficulty with universes here.
-- If we allowed `J` to be a small category in `Prop`, we'd run into trouble
-- because `yoneda.obj (F : (J ⥤ C)ᵒᵖ)` will be a functor into `Sort (max v 1)`,
-- not into `Sort v`.
-- So we don't allow this case; it's not particularly useful anyway.
variables {J : Type v} [small_category J]
variables {C : Sort u} [𝒞 : category.{v+1} C]
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
def cones : Cᵒᵖ ⥤ Type v := (const J).op ⋙ (yoneda.obj F)

lemma cones_obj (X : Cᵒᵖ) : F.cones.obj X = ((const J).obj (unop X) ⟶ F) := rfl

@[simp] lemma cones_map_app {X₁ X₂ : Cᵒᵖ} (f : X₁ ⟶ X₂) (t : F.cones.obj X₁) (j : J) :
  (F.cones.map f t).app j = f.unop ≫ t.app j := rfl

/--
`F.cocones` is the functor assigning to an object `X` the type of
natural transformations from `F` to the constant functor with value `X`.
An object corepresenting this functor is a colimit of `F`.
-/
def cocones : C ⥤ Type v := const J ⋙ coyoneda.obj (op F)

lemma cocones_obj (X : C) : F.cocones.obj X = (F ⟶ (const J).obj X) := rfl

@[simp] lemma cocones_map_app {X₁ X₂ : C} (f : X₁ ⟶ X₂) (t : F.cocones.obj X₁) (j : J) :
  (F.cocones.map f t).app j = t.app j ≫ f := rfl

end functor

section
variables (J C)

def cones : (J ⥤ C) ⥤ (Cᵒᵖ ⥤ Type v) :=
{ obj := functor.cones,
  map := λ F G f, whisker_left (const J).op (yoneda.map f) }

def cocones : (J ⥤ C)ᵒᵖ ⥤ (C ⥤ Type v) :=
{ obj := λ F, functor.cocones (unop F),
  map := λ F G f, whisker_left (const J) (coyoneda.map f) }

variables {J C}

@[simp] lemma cones_obj (F : J ⥤ C) : (cones J C).obj F = F.cones := rfl
@[simp] lemma cones_map  {F G : J ⥤ C} {f : F ⟶ G} :
(cones J C).map f = (whisker_left (const J).op (yoneda.map f)) := rfl

@[simp] lemma cocones_obj (F : (J ⥤ C)ᵒᵖ) : (cocones J C).obj F = (unop F).cocones := rfl
@[simp] lemma cocones_map  {F G : (J ⥤ C)ᵒᵖ} {f : F ⟶ G} :
(cocones J C).map f = (whisker_left (const J) (coyoneda.map f)) := rfl

end

namespace limits

/--
A `c : cone F` is:
* an object `c.X` and
* a natural transformation `c.π : c.X ⟶ F` from the constant `c.X` functor to `F`.

`cone F` is equivalent, in the obvious way, to `Σ X, F.cones.obj X`.
-/
structure cone (F : J ⥤ C) :=
(X : C)
(π : (const J).obj X ⟶ F)

@[simp] lemma cone.w {F : J ⥤ C} (c : cone F) {j j' : J} (f : j ⟶ j') :
  c.π.app j ≫ F.map f = c.π.app j' :=
by convert ←(c.π.naturality f).symm; apply id_comp

/--
A `c : cocone F` is
* an object `c.X` and
* a natural transformation `c.ι : F ⟶ c.X` from `F` to the constant `c.X` functor.

`cocone F` is equivalent, in the obvious way, to `Σ X, F.cocones.obj X`.
-/
structure cocone (F : J ⥤ C) :=
(X : C)
(ι : F ⟶ (const J).obj X)

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
  π := c.extensions.app (op X) f }

@[simp] lemma extend_π  (c : cone F) {X : Cᵒᵖ} (f : unop X ⟶ c.X) :
  (extend c f).π = c.extensions.app X f :=
rfl

def whisker {K : Type v} [small_category K] (E : K ⥤ J) (c : cone F) : cone (E ⋙ F) :=
{ X := c.X,
  π := whisker_left E c.π }

@[simp] lemma whisker_π_app (c : cone F) {K : Type v} [small_category K] (E : K ⥤ J) (k : K) :
  (c.whisker E).π.app k = (c.π).app (E.obj k) := rfl
end cone

namespace cocone
@[simp] def extensions (c : cocone F) : coyoneda.obj (op c.X) ⟶ F.cocones :=
{ app := λ X f, c.ι ≫ ((const J).map f) }

/-- A map from the vertex of a cocone induces a cocone by composition. -/
@[simp] def extend (c : cocone F) {X : C} (f : c.X ⟶ X) : cocone F :=
{ X := X,
  ι := c.extensions.app X f }

@[simp] lemma extend_ι  (c : cocone F) {X : C} (f : c.X ⟶ X) :
  (extend c f).ι = c.extensions.app X f :=
rfl

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

instance cone.category : category.{v+1} (cone F) :=
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

def postcompose {G : J ⥤ C} (α : F ⟶ G) : cone F ⥤ cone G :=
{ obj := λ c, { X := c.X, π := c.π ≫ α },
  map := λ c₁ c₂ f, { hom := f.hom, w' :=
  by intro; erw ← category.assoc; simp [-category.assoc] } }

@[simp] lemma postcompose_obj_X {G : J ⥤ C} (α : F ⟶ G) (c : cone F) :
  ((postcompose α).obj c).X = c.X := rfl

@[simp] lemma postcompose_obj_π {G : J ⥤ C} (α : F ⟶ G) (c : cone F) :
  ((postcompose α).obj c).π = c.π ≫ α := rfl

@[simp] lemma postcompose_map_hom {G : J ⥤ C} (α : F ⟶ G) {c₁ c₂ : cone F} (f : c₁ ⟶ c₂):
  ((postcompose α).map f).hom = f.hom := rfl

def forget : cone F ⥤ C :=
{ obj := λ t, t.X, map := λ s t f, f.hom }

@[simp] lemma forget_obj {t : cone F} : forget.obj t = t.X := rfl
@[simp] lemma forget_map {s t : cone F} {f : s ⟶ t} : forget.map f = f.hom := rfl

section
variables {D : Sort u'} [𝒟 : category.{v+1} D]
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

instance cocone.category : category.{v+1} (cocone F) :=
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

def precompose {G : J ⥤ C} (α : G ⟶ F) : cocone F ⥤ cocone G :=
{ obj := λ c, { X := c.X, ι := α ≫ c.ι },
  map := λ c₁ c₂ f, { hom := f.hom } }

@[simp] lemma precompose_obj_X {G : J ⥤ C} (α : G ⟶ F) (c : cocone F) :
  ((precompose α).obj c).X = c.X := rfl

@[simp] lemma precompose_obj_ι {G : J ⥤ C} (α : G ⟶ F) (c : cocone F) :
  ((precompose α).obj c).ι = α ≫ c.ι := rfl

@[simp] lemma precompose_map_hom {G : J ⥤ C} (α : G ⟶ F) {c₁ c₂ : cocone F} (f : c₁ ⟶ c₂) :
  ((precompose α).map f).hom = f.hom := rfl

def forget : cocone F ⥤ C :=
{ obj := λ t, t.X, map := λ s t f, f.hom }

@[simp] lemma forget_obj {t : cocone F} : forget.obj t = t.X := rfl
@[simp] lemma forget_map {s t : cocone F} {f : s ⟶ t} : forget.map f = f.hom := rfl

section
variables {D : Sort u'} [𝒟 : category.{v+1} D]
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

variables {D : Sort u'} [category.{v+1} D]
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

namespace category_theory.limits

variables {F : J ⥤ Cᵒᵖ}

def cone_of_cocone_left_op (c : cocone F.left_op) : cone F :=
{ X := op c.X,
  π := nat_trans.right_op (c.ι ≫ (const.op_obj_unop (op c.X)).hom), }

@[simp] lemma cone_of_cocone_left_op_X (c : cocone F.left_op) :
  (cone_of_cocone_left_op c).X = op c.X :=
rfl
@[simp] lemma cone_of_cocone_left_op_π_app (c : cocone F.left_op) (j) :
  (cone_of_cocone_left_op c).π.app j = (c.ι.app (op j)).op :=
begin
  dsimp [cone_of_cocone_left_op],
  simp,
end

def cocone_left_op_of_cone (c : cone F) : cocone (F.left_op) :=
{ X := unop c.X,
  ι := nat_trans.left_op c.π, }

@[simp] lemma cocone_left_op_of_cone_X (c : cone F) :
  (cocone_left_op_of_cone c).X = unop c.X :=
rfl
@[simp] lemma cocone_left_op_of_cone_ι_app (c : cone F) (j) :
  (cocone_left_op_of_cone c).ι.app j = (c.π.app (unop j)).unop :=
begin
  dsimp [cocone_left_op_of_cone],
  simp,
end

def cocone_of_cone_left_op (c : cone F.left_op) : cocone F :=
{ X := op c.X,
  ι := nat_trans.right_op ((const.op_obj_unop (op c.X)).hom ≫ c.π), }

@[simp] lemma cocone_of_cone_left_op_X (c : cone F.left_op) :
  (cocone_of_cone_left_op c).X = op c.X :=
rfl
@[simp] lemma cocone_of_cone_left_op_ι_app (c : cone F.left_op) (j) :
  (cocone_of_cone_left_op c).ι.app j = (c.π.app (op j)).op :=
begin
  dsimp [cocone_of_cone_left_op],
  simp,
end

def cone_left_op_of_cocone (c : cocone F) : cone (F.left_op) :=
{ X := unop c.X,
  π := nat_trans.left_op c.ι, }

@[simp] lemma cone_left_op_of_cocone_X (c : cocone F) :
  (cone_left_op_of_cocone c).X = unop c.X :=
rfl
@[simp] lemma cone_left_op_of_cocone_π_app (c : cocone F) (j) :
  (cone_left_op_of_cocone c).π.app j = (c.ι.app (unop j)).unop :=
begin
  dsimp [cone_left_op_of_cocone],
  simp,
end

end category_theory.limits
