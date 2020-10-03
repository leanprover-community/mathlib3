/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.const
import category_theory.yoneda
import category_theory.reflects_isomorphisms

universes v u u' -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]

open category_theory
open category_theory.category
open category_theory.functor
open opposite

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

/--
Functorially associated to each functor `J ⥤ C`, we have the `C`-presheaf consisting of
cones with a given cone point.
-/
@[simps] def cones : (J ⥤ C) ⥤ (Cᵒᵖ ⥤ Type v) :=
{ obj := functor.cones,
  map := λ F G f, whisker_left (const J).op (yoneda.map f) }

/--
Contravariantly associated to each functor `J ⥤ C`, we have the `C`-copresheaf consisting of
cocones with a given cocone point.
-/
@[simps] def cocones : (J ⥤ C)ᵒᵖ ⥤ (C ⥤ Type v) :=
{ obj := λ F, functor.cocones (unop F),
  map := λ F G f, whisker_left (const J) (coyoneda.map f) }

end

namespace limits

/--
A `c : cone F` is:
* an object `c.X` and
* a natural transformation `c.π : c.X ⟶ F` from the constant `c.X` functor to `F`.

`cone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cones.obj X`.
-/
structure cone (F : J ⥤ C) :=
(X : C)
(π : (const J).obj X ⟶ F)

@[simp, reassoc] lemma cone.w {F : J ⥤ C} (c : cone F) {j j' : J} (f : j ⟶ j') :
  c.π.app j ≫ F.map f = c.π.app j' :=
by { rw ← (c.π.naturality f), apply id_comp }

/--
A `c : cocone F` is
* an object `c.X` and
* a natural transformation `c.ι : F ⟶ c.X` from `F` to the constant `c.X` functor.

`cocone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
structure cocone (F : J ⥤ C) :=
(X : C)
(ι : F ⟶ (const J).obj X)

@[simp, reassoc] lemma cocone.w {F : J ⥤ C} (c : cocone F) {j j' : J} (f : j ⟶ j') :
  F.map f ≫ c.ι.app j' = c.ι.app j :=
by { rw (c.ι.naturality f), apply comp_id }

variables {F : J ⥤ C}

namespace cone

/-- The isomorphism between a cone on `F` and an element of the functor `F.cones`. -/
def equiv (F : J ⥤ C) : cone F ≅ Σ X, F.cones.obj X :=
{ hom := λ c, ⟨op c.X, c.π⟩,
  inv := λ c, { X := unop c.1, π := c.2 },
  hom_inv_id' := begin ext, cases x, refl, end,
  inv_hom_id' := begin ext, cases x, refl, end }

@[simp] def extensions (c : cone F) : yoneda.obj c.X ⟶ F.cones :=
{ app := λ X f, (const J).map f ≫ c.π }

/-- A map to the vertex of a cone induces a cone by composition. -/
@[simp] def extend (c : cone F) {X : C} (f : X ⟶ c.X) : cone F :=
{ X := X,
  π := c.extensions.app (op X) f }

@[simp] lemma extend_π  (c : cone F) {X : Cᵒᵖ} (f : unop X ⟶ c.X) :
  (extend c f).π = c.extensions.app X f :=
rfl

/-- Whisker a cone by precomposition of a functor. -/
@[simps] def whisker {K : Type v} [small_category K] (E : K ⥤ J) (c : cone F) : cone (E ⋙ F) :=
{ X := c.X,
  π := whisker_left E c.π }

end cone

namespace cocone

/-- The isomorphism between a cocone on `F` and an element of the functor `F.cocones`. -/
def equiv (F : J ⥤ C) : cocone F ≅ Σ X, F.cocones.obj X :=
{ hom := λ c, ⟨c.X, c.ι⟩,
  inv := λ c, { X := c.1, ι := c.2 },
  hom_inv_id' := begin ext, cases x, refl, end,
  inv_hom_id' := begin ext, cases x, refl, end }

@[simp] def extensions (c : cocone F) : coyoneda.obj (op c.X) ⟶ F.cocones :=
{ app := λ X f, c.ι ≫ (const J).map f }

/-- A map from the vertex of a cocone induces a cocone by composition. -/
@[simp] def extend (c : cocone F) {X : C} (f : c.X ⟶ X) : cocone F :=
{ X := X,
  ι := c.extensions.app X f }

@[simp] lemma extend_ι  (c : cocone F) {X : C} (f : c.X ⟶ X) :
  (extend c f).ι = c.extensions.app X f :=
rfl

/--
Whisker a cocone by precomposition of a functor. See `whiskering` for a functorial
version.
-/
@[simps] def whisker {K : Type v} [small_category K] (E : K ⥤ J) (c : cocone F) : cocone (E ⋙ F) :=
{ X := c.X,
  ι := whisker_left E c.ι }

end cocone

/-- A cone morphism between two cones for the same diagram is a morphism of the cone points which
commutes with the cone legs. -/
@[ext] structure cone_morphism (A B : cone F) :=
(hom : A.X ⟶ B.X)
(w'  : ∀ j : J, hom ≫ B.π.app j = A.π.app j . obviously)

restate_axiom cone_morphism.w'
attribute [simp, reassoc] cone_morphism.w

/-- The category of cones on a given diagram. -/
@[simps] instance cone.category : category.{v} (cone F) :=
{ hom  := λ A B, cone_morphism A B,
  comp := λ X Y Z f g, { hom := f.hom ≫ g.hom },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cones
/-- To give an isomorphism between cones, it suffices to give an
  isomorphism between their vertices which commutes with the cone
  maps. -/
@[ext, simps] def ext {c c' : cone F}
  (φ : c.X ≅ c'.X) (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j) : c ≅ c' :=
{ hom := { hom := φ.hom },
  inv := { hom := φ.inv, w' := λ j, φ.inv_comp_eq.mpr (w j) } }

/--
Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
def cone_iso_of_hom_iso {K : J ⥤ C} {c d : cone K} (f : c ⟶ d) [i : is_iso f.hom] :
  is_iso f :=
{ inv :=
  { hom := i.inv,
    w' := λ j, (as_iso f.hom).inv_comp_eq.2 (f.w j).symm } }

/--
Functorially postcompose a cone for `F` by a natural transformation `F ⟶ G` to give a cone for `G`.
-/
@[simps] def postcompose {G : J ⥤ C} (α : F ⟶ G) : cone F ⥤ cone G :=
{ obj := λ c, { X := c.X, π := c.π ≫ α },
  map := λ c₁ c₂ f, { hom := f.hom, w' :=
  by intro; erw ← category.assoc; simp [-category.assoc] } }

/-- Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
def postcompose_comp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
  postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
nat_iso.of_components (λ s, cones.ext (iso.refl _) (by tidy)) (by tidy)

/-- Postcomposing by the identity does not change the cone up to isomorphism. -/
def postcompose_id : postcompose (𝟙 F) ≅ 𝟭 (cone F) :=
nat_iso.of_components (λ s, cones.ext (iso.refl _) (by tidy)) (by tidy)

/--
If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cones.
-/
@[simps]
def postcompose_equivalence {G : J ⥤ C} (α : F ≅ G) : cone F ≌ cone G :=
{ functor := postcompose α.hom,
  inverse := postcompose α.inv,
  unit_iso := nat_iso.of_components (λ s, cones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ s, cones.ext (iso.refl _) (by tidy)) (by tidy) }

/--
Whiskering on the left by `E : K ⥤ J` gives a functor from `cone F` to `cone (E ⋙ F)`.
-/
@[simps]
def whiskering {K : Type v} [small_category K] (E : K ⥤ J) : cone F ⥤ cone (E ⋙ F) :=
{ obj := λ c, c.whisker E,
  map := λ c c' f, { hom := f.hom, } }

/--
Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[simps]
def whiskering_equivalence {K : Type v} [small_category K] (e : K ≌ J) :
  cone F ≌ cone (e.functor ⋙ F) :=
{ functor := whiskering e.functor,
  inverse := whiskering e.inverse ⋙
    postcompose ((functor.associator _ _ _).inv ≫ (whisker_right (e.counit_iso).hom F) ≫
      (functor.left_unitor F).hom),
  unit_iso := nat_iso.of_components (λ s, cones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ s, cones.ext (iso.refl _)
  (begin
    intro k,
    have t := s.π.naturality (e.unit_inv.app k),
    dsimp at t,
    simp only [←e.counit_app_functor k, id_comp] at t,
    dsimp,
    simp [t],
  end)) (by tidy), }

/--
The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
def equivalence_of_reindexing {K : Type v} [small_category K] {G : K ⥤ C}
  (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : cone F ≌ cone G :=
(whiskering_equivalence e).trans (postcompose_equivalence α)

@[simp]
lemma equivalence_of_reindexing_functor_obj {K : Type v} [small_category K] {G : K ⥤ C}
  (e : K ≌ J) (α : e.functor ⋙ F ≅ G) (c : cone F) :
  (equivalence_of_reindexing e α).functor.obj c =
  (postcompose α.hom).obj (cone.whisker e.functor c) :=
rfl

section
variable (F)

/-- Forget the cone structure and obtain just the cone point. -/
@[simps]
def forget : cone F ⥤ C :=
{ obj := λ t, t.X, map := λ s t f, f.hom }

variables {D : Type u'} [category.{v} D] (G : C ⥤ D)

/-- A functor `G : C ⥤ D` sends cones over `F` to cones over `F ⋙ G` functorially. -/
@[simps] def functoriality : cone F ⥤ cone (F ⋙ G) :=
{ obj := λ A,
  { X := G.obj A.X,
    π := { app := λ j, G.map (A.π.app j), naturality' := by intros; erw ←G.map_comp; tidy } },
  map := λ X Y f,
  { hom := G.map f.hom,
    w'  := by intros; rw [←functor.map_comp, f.w] } }

instance functoriality_full [full G] [faithful G] : full (functoriality F G) :=
{ preimage := λ X Y t,
  { hom := G.preimage t.hom,
    w' := λ j, G.map_injective (by simpa using t.w j) } }

instance functoriality_faithful [faithful G] : faithful (cones.functoriality F G) :=
{ map_injective' := λ X Y f g e, by { ext1, injection e, apply G.map_injective h_1 } }

/--
If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cones over `F` and cones over `F ⋙ e.functor`.
-/
@[simps]
def functoriality_equivalence (e : C ≌ D) : cone F ≌ cone (F ⋙ e.functor) :=
let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
  functor.associator _ _ _ ≪≫ iso_whisker_left _ (e.unit_iso).symm ≪≫ functor.right_unitor _ in
{ functor := functoriality F e.functor,
  inverse := (functoriality (F ⋙ e.functor) e.inverse) ⋙
    (postcompose_equivalence f).functor,
  unit_iso := nat_iso.of_components (λ c, cones.ext (e.unit_iso.app _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ c, cones.ext (e.counit_iso.app _) (by tidy)) (by tidy), }

/--
If `F` reflects isomorphisms, then `cones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cone_isomorphism (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) :
  reflects_isomorphisms (cones.functoriality K F) :=
begin
  constructor,
  introsI,
  haveI : is_iso (F.map f.hom) := (cones.forget (K ⋙ F)).map_is_iso ((cones.functoriality K F).map f),
  haveI := reflects_isomorphisms.reflects F f.hom,
  apply cone_iso_of_hom_iso
end

end

end cones

/-- A cocone morphism between two cocones for the same diagram is a morphism of the cocone points
which commutes with the cocone legs. -/
@[ext] structure cocone_morphism (A B : cocone F) :=
(hom : A.X ⟶ B.X)
(w'  : ∀ j : J, A.ι.app j ≫ hom = B.ι.app j . obviously)

restate_axiom cocone_morphism.w'
attribute [simp, reassoc] cocone_morphism.w

@[simps] instance cocone.category : category.{v} (cocone F) :=
{ hom  := λ A B, cocone_morphism A B,
  comp := λ _ _ _ f g,
  { hom := f.hom ≫ g.hom },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cocones
/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[ext, simps] def ext {c c' : cocone F}
  (φ : c.X ≅ c'.X) (w : ∀ j, c.ι.app j ≫ φ.hom = c'.ι.app j) : c ≅ c' :=
{ hom := { hom := φ.hom },
  inv := { hom := φ.inv, w' := λ j, φ.comp_inv_eq.mpr (w j).symm } }

/--
Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/
def cocone_iso_of_hom_iso {K : J ⥤ C} {c d : cocone K} (f : c ⟶ d) [i : is_iso f.hom] :
  is_iso f :=
{ inv :=
  { hom := i.inv,
    w' := λ j, (as_iso f.hom).comp_inv_eq.2 (f.w j).symm } }

/--
Functorially precompose a cocone for `F` by a natural transformation `G ⟶ F` to give a cocone for `G`.
-/
@[simps] def precompose {G : J ⥤ C} (α : G ⟶ F) : cocone F ⥤ cocone G :=
{ obj := λ c, { X := c.X, ι := α ≫ c.ι },
  map := λ c₁ c₂ f, { hom := f.hom } }

/-- Precomposing a cocone by the composite natural transformation `α ≫ β` is the same as
precomposing by `β` and then by `α`. -/
def precompose_comp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
  precompose (α ≫ β) ≅ precompose β ⋙ precompose α :=
nat_iso.of_components (λ s, cocones.ext (iso.refl _) (by tidy)) (by tidy)

/-- Precomposing by the identity does not change the cocone up to isomorphism. -/
def precompose_id : precompose (𝟙 F) ≅ 𝟭 (cocone F) :=
nat_iso.of_components (λ s, cocones.ext (iso.refl _) (by tidy)) (by tidy)

/--
If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cocones.
-/
@[simps]
def precompose_equivalence {G : J ⥤ C} (α : G ≅ F) : cocone F ≌ cocone G :=
{ functor := precompose α.hom,
  inverse := precompose α.inv,
  unit_iso := nat_iso.of_components (λ s, cocones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ s, cocones.ext (iso.refl _) (by tidy)) (by tidy) }

/--
Whiskering on the left by `E : K ⥤ J` gives a functor from `cocone F` to `cocone (E ⋙ F)`.
-/
@[simps]
def whiskering {K : Type v} [small_category K] (E : K ⥤ J) : cocone F ⥤ cocone (E ⋙ F) :=
{ obj := λ c, c.whisker E,
  map := λ c c' f, { hom := f.hom, } }

/--
Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[simps]
def whiskering_equivalence {K : Type v} [small_category K] (e : K ≌ J) :
  cocone F ≌ cocone (e.functor ⋙ F) :=
{ functor := whiskering e.functor,
  inverse := whiskering e.inverse ⋙
    precompose ((functor.left_unitor F).inv ≫ (whisker_right (e.counit_iso).inv F) ≫ (functor.associator _ _ _).inv),
  unit_iso := nat_iso.of_components (λ s, cocones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ s, cocones.ext (iso.refl _)
  (begin
    intro k,
    have t := s.ι.naturality (e.unit.app k),
    dsimp at t,
    simp only [←e.counit_inv_app_functor k, comp_id] at t,
    dsimp,
    simp [t],
  end)) (by tidy), }

/--
The categories of cocones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
def equivalence_of_reindexing {K : Type v} [small_category K] {G : K ⥤ C}
  (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : cocone F ≌ cocone G :=
(whiskering_equivalence e).trans (precompose_equivalence α.symm)

@[simp]
lemma equivalence_of_reindexing_functor_obj {K : Type v} [small_category K] {G : K ⥤ C}
  (e : K ≌ J) (α : e.functor ⋙ F ≅ G) (c : cocone F) :
  (equivalence_of_reindexing e α).functor.obj c =
  (precompose α.inv).obj (cocone.whisker e.functor c) :=
rfl

section
variable (F)

/-- Forget the cocone structure and obtain just the cocone point. -/
@[simps]
def forget : cocone F ⥤ C :=
{ obj := λ t, t.X, map := λ s t f, f.hom }

variables {D : Type u'} [category.{v} D] (G : C ⥤ D)

/-- A functor `G : C ⥤ D` sends cocones over `F` to cocones over `F ⋙ G` functorially. -/
@[simps] def functoriality : cocone F ⥤ cocone (F ⋙ G) :=
{ obj := λ A,
  { X := G.obj A.X,
    ι := { app := λ j, G.map (A.ι.app j), naturality' := by intros; erw ←G.map_comp; tidy } },
  map := λ _ _ f,
  { hom := G.map f.hom,
    w'  := by intros; rw [←functor.map_comp, cocone_morphism.w] } }

instance functoriality_full [full G] [faithful G] : full (functoriality F G) :=
{ preimage := λ X Y t,
  { hom := G.preimage t.hom,
    w' := λ j, G.map_injective (by simpa using t.w j) } }

instance functoriality_faithful [faithful G] : faithful (functoriality F G) :=
{ map_injective' := λ X Y f g e, by { ext1, injection e, apply G.map_injective h_1 } }

/--
If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cocones over `F` and cocones over `F ⋙ e.functor`.
-/
@[simps]
def functoriality_equivalence (e : C ≌ D) : cocone F ≌ cocone (F ⋙ e.functor) :=
let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
  functor.associator _ _ _ ≪≫ iso_whisker_left _ (e.unit_iso).symm ≪≫ functor.right_unitor _ in
{ functor := functoriality F e.functor,
  inverse := (functoriality (F ⋙ e.functor) e.inverse) ⋙
    (precompose_equivalence f.symm).functor,
  unit_iso := nat_iso.of_components (λ c, cocones.ext (e.unit_iso.app _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ c, cocones.ext (e.counit_iso.app _)
  begin
    -- Unfortunately this doesn't work by `tidy`.
    -- In this configuration `simp` reaches a dead-end and needs help.
    intros j,
    dsimp,
    simp only [←equivalence.counit_inv_app_functor, iso.inv_hom_id_app, map_comp, equivalence.fun_inv_map,
      assoc, id_comp, iso.inv_hom_id_app_assoc],
    dsimp, simp, -- See note [dsimp, simp].
  end) (by tidy), }

/--
If `F` reflects isomorphisms, then `cocones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cocone_isomorphism (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) :
  reflects_isomorphisms (cocones.functoriality K F) :=
begin
  constructor,
  introsI,
  haveI : is_iso (F.map f.hom) := (cocones.forget (K ⋙ F)).map_is_iso ((cocones.functoriality K F).map f),
  haveI := reflects_isomorphisms.reflects F f.hom,
  apply cocone_iso_of_hom_iso
end

end
end cocones

end limits

namespace functor

variables {D : Type u'} [category.{v} D]
variables {F : J ⥤ C} {G : J ⥤ C} (H : C ⥤ D)

open category_theory.limits

/-- The image of a cone in C under a functor G : C ⥤ D is a cone in D. -/
def map_cone   (c : cone F)   : cone (F ⋙ H)   := (cones.functoriality F H).obj c
/-- The image of a cocone in C under a functor G : C ⥤ D is a cocone in D. -/
def map_cocone (c : cocone F) : cocone (F ⋙ H) := (cocones.functoriality F H).obj c

@[simp] lemma map_cone_X (c : cone F) : (H.map_cone c).X = H.obj c.X := rfl
@[simp] lemma map_cocone_X (c : cocone F) : (H.map_cocone c).X = H.obj c.X := rfl

/-- Given a cone morphism `c ⟶ c'`, construct a cone morphism on the mapped cones functorially.  -/
def map_cone_morphism   {c c' : cone F}   (f : c ⟶ c')   :
  H.map_cone c ⟶ H.map_cone c' := (cones.functoriality F H).map f
/-- Given a cocone morphism `c ⟶ c'`, construct a cocone morphism on the mapped cocones functorially.  -/
def map_cocone_morphism {c c' : cocone F} (f : c ⟶ c') :
  H.map_cocone c ⟶ H.map_cocone c' := (cocones.functoriality F H).map f

@[simp] lemma map_cone_π (c : cone F) (j : J) :
  (map_cone H c).π.app j = H.map (c.π.app j) := rfl
@[simp] lemma map_cocone_ι (c : cocone F) (j : J) :
  (map_cocone H c).ι.app j = H.map (c.ι.app j) := rfl

/-- If `H` is an equivalence, we invert `H.map_cone` and get a cone for `F` from a cone
for `F ⋙ H`.-/
def map_cone_inv [is_equivalence H]
  (c : cone (F ⋙ H)) : cone F :=
(limits.cones.functoriality_equivalence F (as_equivalence H)).inverse.obj c

/-- `map_cone` is the left inverse to `map_cone_inv`. -/
def map_cone_map_cone_inv {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cone (F ⋙ H)) :
  map_cone H (map_cone_inv H c) ≅ c :=
(limits.cones.functoriality_equivalence F (as_equivalence H)).counit_iso.app c

/-- `map_cone` is the right inverse to `map_cone_inv`. -/
def map_cone_inv_map_cone {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cone F) :
  map_cone_inv H (map_cone H c) ≅ c :=
(limits.cones.functoriality_equivalence F (as_equivalence H)).unit_iso.symm.app c
/-- If `H` is an equivalence, we invert `H.map_cone` and get a cone for `F` from a cone
for `F ⋙ H`.-/

def map_cocone_inv [is_equivalence H]
  (c : cocone (F ⋙ H)) : cocone F :=
(limits.cocones.functoriality_equivalence F (as_equivalence H)).inverse.obj c

/-- `map_cocone` is the left inverse to `map_cocone_inv`. -/
def map_cocone_map_cocone_inv {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cocone (F ⋙ H)) :
  map_cocone H (map_cocone_inv H c) ≅ c :=
(limits.cocones.functoriality_equivalence F (as_equivalence H)).counit_iso.app c

/-- `map_cocone` is the right inverse to `map_cocone_inv`. -/
def map_cocone_inv_map_cocone {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cocone F) :
  map_cocone_inv H (map_cocone H c) ≅ c :=
(limits.cocones.functoriality_equivalence F (as_equivalence H)).unit_iso.symm.app c

end functor

end category_theory

namespace category_theory.limits

section
variables {F : J ⥤ C}

/-- Change a `cocone F` into a `cone F.op`. -/
@[simps] def cocone.op (c : cocone F) : cone F.op :=
{ X := op c.X,
  π :=
  { app := λ j, (c.ι.app (unop j)).op,
    naturality' := λ j j' f, has_hom.hom.unop_inj (by tidy) } }

/-- Change a `cone F` into a `cocone F.op`. -/
@[simps] def cone.op (c : cone F) : cocone F.op :=
{ X := op c.X,
  ι :=
  { app := λ j, (c.π.app (unop j)).op,
    naturality' := λ j j' f, has_hom.hom.unop_inj (by tidy) } }

/-- Change a `cocone F.op` into a `cone F`. -/
@[simps] def cocone.unop (c : cocone F.op) : cone F :=
{ X := unop c.X,
  π :=
  { app := λ j, (c.ι.app (op j)).unop,
    naturality' := λ j j' f, has_hom.hom.op_inj
    begin dsimp, simp only [comp_id], exact (c.w f.op).symm, end } }

/-- Change a `cone F.op` into a `cocone F`. -/
@[simps] def cone.unop (c : cone F.op) : cocone F :=
{ X := unop c.X,
  ι :=
  { app := λ j, (c.π.app (op j)).unop,
    naturality' := λ j j' f, has_hom.hom.op_inj
    begin dsimp, simp only [id_comp], exact (c.w f.op), end } }

variables (F)

/--
The category of cocones on `F`
is equivalent to the opposite category of
the category of cones on the opposite of `F`.
-/
@[simps]
def cocone_equivalence_op_cone_op : cocone F ≌ (cone F.op)ᵒᵖ :=
{ functor :=
  { obj := λ c, op (cocone.op c),
    map := λ X Y f, has_hom.hom.op
    { hom := f.hom.op,
      w' := λ j, by { apply has_hom.hom.unop_inj, dsimp, simp, }, } },
  inverse :=
  { obj := λ c, cone.unop (unop c),
    map := λ X Y f,
    { hom := f.unop.hom.unop,
      w' := λ j, by { apply has_hom.hom.op_inj, dsimp, simp, }, } },
  unit_iso := nat_iso.of_components (λ c, cocones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ c,
    by { op_induction c, dsimp, apply iso.op, exact cones.ext (iso.refl _) (by tidy), })
    begin
      intros,
      have hX : X = op (unop X) := rfl,
      revert hX,
      generalize : unop X = X',
      rintro rfl,
      have hY : Y = op (unop Y) := rfl,
      revert hY,
      generalize : unop Y = Y',
      rintro rfl,
      apply has_hom.hom.unop_inj,
      apply cone_morphism.ext,
      dsimp, simp,
    end,
  functor_unit_iso_comp' := λ c, begin apply has_hom.hom.unop_inj, ext, dsimp, simp, end }

end

section
variables {F : J ⥤ Cᵒᵖ}

/-- Change a cocone on `F.left_op : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
-- Here and below we only automatically generate the `@[simp]` lemma for the `X` field,
-- as we can write a simpler `rfl` lemma for the components of the natural transformation by hand.
@[simps X] def cone_of_cocone_left_op (c : cocone F.left_op) : cone F :=
{ X := op c.X,
  π := nat_trans.remove_left_op (c.ι ≫ (const.op_obj_unop (op c.X)).hom) }

@[simp] lemma cone_of_cocone_left_op_π_app (c : cocone F.left_op) (j) :
  (cone_of_cocone_left_op c).π.app j = (c.ι.app (op j)).op :=
by { dsimp [cone_of_cocone_left_op], simp }

/-- Change a cone on `F : J ⥤ Cᵒᵖ` to a cocone on `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps X] def cocone_left_op_of_cone (c : cone F) : cocone (F.left_op) :=
{ X := unop c.X,
  ι := nat_trans.left_op c.π }

@[simp] lemma cocone_left_op_of_cone_ι_app (c : cone F) (j) :
  (cocone_left_op_of_cone c).ι.app j = (c.π.app (unop j)).unop :=
by { dsimp [cocone_left_op_of_cone], simp }

/-- Change a cone on `F.left_op : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
@[simps X] def cocone_of_cone_left_op (c : cone F.left_op) : cocone F :=
{ X := op c.X,
  ι := nat_trans.remove_left_op ((const.op_obj_unop (op c.X)).hom ≫ c.π) }

@[simp] lemma cocone_of_cone_left_op_ι_app (c : cone F.left_op) (j) :
  (cocone_of_cone_left_op c).ι.app j = (c.π.app (op j)).op :=
by { dsimp [cocone_of_cone_left_op], simp }

/-- Change a cocone on `F : J ⥤ Cᵒᵖ` to a cone on `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps X] def cone_left_op_of_cocone (c : cocone F) : cone (F.left_op) :=
{ X := unop c.X,
  π := nat_trans.left_op c.ι }

@[simp] lemma cone_left_op_of_cocone_π_app (c : cocone F) (j) :
  (cone_left_op_of_cocone c).π.app j = (c.ι.app (unop j)).unop :=
by { dsimp [cone_left_op_of_cocone], simp }

end

end category_theory.limits

namespace category_theory.functor

open category_theory.limits

variables {F : J ⥤ C}
variables {D : Type u'} [category.{v} D]

section
variables (G : C ⥤ D)

/-- The opposite cocone of the image of a cone is the image of the opposite cocone. -/
def map_cone_op (t : cone F) : (G.map_cone t).op ≅ (G.op.map_cocone t.op) :=
cocones.ext (iso.refl _) (by tidy)

/-- The opposite cone of the image of a cocone is the image of the opposite cone. -/
def map_cocone_op {t : cocone F} : (G.map_cocone t).op ≅ (G.op.map_cone t.op) :=
cones.ext (iso.refl _) (by tidy)

end

end category_theory.functor
