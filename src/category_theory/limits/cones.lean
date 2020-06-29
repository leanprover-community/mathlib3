/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.const
import category_theory.yoneda

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

@[simp] lemma cone.w {F : J ⥤ C} (c : cone F) {j j' : J} (f : j ⟶ j') :
  c.π.app j ≫ F.map f = c.π.app j' :=
by convert ←(c.π.naturality f).symm; apply id_comp

/--
A `c : cocone F` is
* an object `c.X` and
* a natural transformation `c.ι : F ⟶ c.X` from `F` to the constant `c.X` functor.

`cocone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
structure cocone (F : J ⥤ C) :=
(X : C)
(ι : F ⟶ (const J).obj X)

@[simp] lemma cocone.w {F : J ⥤ C} (c : cocone F) {j j' : J} (f : j ⟶ j') :
  F.map f ≫ c.ι.app j' = c.ι.app j :=
by convert ←(c.ι.naturality f); apply comp_id


variables {F : J ⥤ C}

namespace cone

def equiv (F : J ⥤ C) : cone F ≅ Σ X, F.cones.obj X :=
{ hom := λ c, ⟨op c.X, c.π⟩,
  inv := λ c, { X := unop c.1, π := c.2 },
  hom_inv_id' := begin ext, cases x, refl, end,
  inv_hom_id' := begin ext, cases x, refl, end }

@[simp] def extensions (c : cone F) : yoneda.obj c.X ⟶ F.cones :=
{ app := λ X f, ((const J).map f) ≫ c.π }

/-- A map to the vertex of a cone induces a cone by composition. -/
@[simp] def extend (c : cone F) {X : C} (f : X ⟶ c.X) : cone F :=
{ X := X,
  π := c.extensions.app (op X) f }

@[simp] lemma extend_π  (c : cone F) {X : Cᵒᵖ} (f : unop X ⟶ c.X) :
  (extend c f).π = c.extensions.app X f :=
rfl

@[simps] def whisker {K : Type v} [small_category K] (E : K ⥤ J) (c : cone F) : cone (E ⋙ F) :=
{ X := c.X,
  π := whisker_left E c.π }

end cone

namespace cocone

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

@[simps] def whisker {K : Type v} [small_category K] (E : K ⥤ J) (c : cocone F) : cocone (E ⋙ F) :=
{ X := c.X,
  ι := whisker_left E c.ι }

end cocone

@[ext] structure cone_morphism (A B : cone F) :=
(hom : A.X ⟶ B.X)
(w'  : ∀ j : J, hom ≫ B.π.app j = A.π.app j . obviously)

restate_axiom cone_morphism.w'
attribute [simp] cone_morphism.w

@[simps] instance cone.category : category.{v} (cone F) :=
{ hom  := λ A B, cone_morphism A B,
  comp := λ X Y Z f g,
  { hom := f.hom ≫ g.hom,
    w' := by intro j; rw [assoc, g.w, f.w] },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cones
/-- To give an isomorphism between cones, it suffices to give an
  isomorphism between their vertices which commutes with the cone
  maps. -/
@[ext, simps] def ext {c c' : cone F}
  (φ : c.X ≅ c'.X) (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j) : c ≅ c' :=
{ hom := { hom := φ.hom },
  inv := { hom := φ.inv, w' := λ j, φ.inv_comp_eq.mpr (w j) } }

@[simps] def postcompose {G : J ⥤ C} (α : F ⟶ G) : cone F ⥤ cone G :=
{ obj := λ c, { X := c.X, π := c.π ≫ α },
  map := λ c₁ c₂ f, { hom := f.hom, w' :=
  by intro; erw ← category.assoc; simp [-category.assoc] } }

def postcompose_comp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
  postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
nat_iso.of_components (λ s, cones.ext (iso.refl _) (by tidy)) (by tidy)

def postcompose_id : postcompose (𝟙 F) ≅ 𝟭 (cone F) :=
nat_iso.of_components (λ s, cones.ext (iso.refl _) (by tidy)) (by tidy)

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
    simp only [←e.counit_functor k, id_comp] at t,
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

@[simps]
def forget : cone F ⥤ C :=
{ obj := λ t, t.X, map := λ s t f, f.hom }

variables {D : Type u'} [category.{v} D] (G : C ⥤ D)

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

end

end cones

@[ext] structure cocone_morphism (A B : cocone F) :=
(hom : A.X ⟶ B.X)
(w'  : ∀ j : J, A.ι.app j ≫ hom = B.ι.app j . obviously)

restate_axiom cocone_morphism.w'
attribute [simp] cocone_morphism.w

@[simps] instance cocone.category : category.{v} (cocone F) :=
{ hom  := λ A B, cocone_morphism A B,
  comp := λ _ _ _ f g,
  { hom := f.hom ≫ g.hom,
    w' := by intro j; rw [←assoc, f.w, g.w] },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cocones
/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[ext, simps] def ext {c c' : cocone F}
  (φ : c.X ≅ c'.X) (w : ∀ j, c.ι.app j ≫ φ.hom = c'.ι.app j) : c ≅ c' :=
{ hom := { hom := φ.hom },
  inv := { hom := φ.inv, w' := λ j, φ.comp_inv_eq.mpr (w j).symm } }

@[simps] def precompose {G : J ⥤ C} (α : G ⟶ F) : cocone F ⥤ cocone G :=
{ obj := λ c, { X := c.X, ι := α ≫ c.ι },
  map := λ c₁ c₂ f, { hom := f.hom } }

def precompose_comp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
  precompose (α ≫ β) ≅ precompose β ⋙ precompose α :=
by { fapply nat_iso.of_components, { intro s, fapply ext, refl, obviously }, obviously }

def precompose_id : precompose (𝟙 F) ≅ 𝟭 (cocone F) :=
by { fapply nat_iso.of_components, { intro s, fapply ext, refl, obviously }, obviously }

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
    simp only [e.functor_unit k, comp_id] at t,
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

@[simps]
def forget : cocone F ⥤ C :=
{ obj := λ t, t.X, map := λ s t f, f.hom }

variables {D : Type u'} [category.{v} D] (G : C ⥤ D)

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

@[simps]
def map_cone_inv [is_equivalence H]
  (c : cone (F ⋙ H)) : cone F :=
let t := (inv H).map_cone c in
let α : (F ⋙ H) ⋙ inv H ⟶ F :=
  ((whisker_left F is_equivalence.unit_iso.inv) : F ⋙ (H ⋙ inv H) ⟶ _) ≫ (functor.right_unitor _).hom in
{ X := t.X,
  π := ((category_theory.cones J C).map α).app (op t.X) t.π }

def map_cone_morphism   {c c' : cone F}   (f : c ⟶ c')   :
  (H.map_cone c) ⟶ (H.map_cone c') := (cones.functoriality F H).map f
def map_cocone_morphism {c c' : cocone F} (f : c ⟶ c') :
  (H.map_cocone c) ⟶ (H.map_cocone c') := (cocones.functoriality F H).map f

@[simp] lemma map_cone_π (c : cone F) (j : J) :
  (map_cone H c).π.app j = H.map (c.π.app j) := rfl
@[simp] lemma map_cocone_ι (c : cocone F) (j : J) :
  (map_cocone H c).ι.app j = H.map (c.ι.app j) := rfl

/-- `map_cone` is the left inverse to `map_cone_inv`. -/
def map_cone_map_cone_inv {F : J ⥤ D} (H : D ⥤ C) [is_equivalence H] (c : cone (F ⋙ H)) :
  map_cone H (map_cone_inv H c) ≅ c :=
begin
  apply cones.ext _ (λ j, _),
  { exact H.inv_fun_id.app c.X },
  { dsimp,
    erw [comp_id, ← H.inv_fun_id.hom.naturality (c.π.app j), comp_map, H.map_comp],
    congr' 1,
    erw [← cancel_epi (H.inv_fun_id.inv.app (H.obj (F.obj j))), nat_iso.inv_hom_id_app,
         ← (functor.as_equivalence H).functor_unit _, ← H.map_comp, nat_iso.hom_inv_id_app,
         H.map_id],
    refl }
end

end functor

end category_theory

namespace category_theory.limits

variables {F : J ⥤ Cᵒᵖ}

-- Here and below we only automatically generate the `@[simp]` lemma for the `X` field,
-- as we can be a simpler `rfl` lemma for the components of the natural transformation by hand.
@[simps X] def cone_of_cocone_left_op (c : cocone F.left_op) : cone F :=
{ X := op c.X,
  π := nat_trans.right_op (c.ι ≫ (const.op_obj_unop (op c.X)).hom) }

@[simp] lemma cone_of_cocone_left_op_π_app (c : cocone F.left_op) (j) :
  (cone_of_cocone_left_op c).π.app j = (c.ι.app (op j)).op :=
by { dsimp [cone_of_cocone_left_op], simp }

@[simps X] def cocone_left_op_of_cone (c : cone F) : cocone (F.left_op) :=
{ X := unop c.X,
  ι := nat_trans.left_op c.π }

@[simp] lemma cocone_left_op_of_cone_ι_app (c : cone F) (j) :
  (cocone_left_op_of_cone c).ι.app j = (c.π.app (unop j)).unop :=
by { dsimp [cocone_left_op_of_cone], simp }

@[simps X] def cocone_of_cone_left_op (c : cone F.left_op) : cocone F :=
{ X := op c.X,
  ι := nat_trans.right_op ((const.op_obj_unop (op c.X)).hom ≫ c.π) }

@[simp] lemma cocone_of_cone_left_op_ι_app (c : cone F.left_op) (j) :
  (cocone_of_cone_left_op c).ι.app j = (c.π.app (op j)).op :=
by { dsimp [cocone_of_cone_left_op], simp }

@[simps X] def cone_left_op_of_cocone (c : cocone F) : cone (F.left_op) :=
{ X := unop c.X,
  π := nat_trans.left_op c.ι }

@[simp] lemma cone_left_op_of_cocone_π_app (c : cocone F) (j) :
  (cone_left_op_of_cocone c).π.app j = (c.ι.app (unop j)).unop :=
by { dsimp [cone_left_op_of_cocone], simp }
end category_theory.limits
