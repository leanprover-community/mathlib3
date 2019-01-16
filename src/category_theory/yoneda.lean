-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

/- The Yoneda embedding, as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
   along with an instance that it is `fully_faithful`.

   Also the Yoneda lemma, `yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`. -/

import category_theory.natural_transformation
import category_theory.opposites
import category_theory.types
import category_theory.fully_faithful
import category_theory.natural_isomorphism

namespace category_theory

universes v₁ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

def yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁) :=
{ obj := λ X,
  { obj := λ Y : C, Y ⟶ X,
    map := λ Y Y' f g, f ≫ g,
    map_comp' := begin intros X_1 Y Z f g, ext1, dsimp at *, erw [category.assoc] end,
    map_id' := begin intros X_1, ext1, dsimp at *, erw [category.id_comp] end },
  map := λ X X' f, { app := λ Y g, g ≫ f } }

def coyoneda : Cᵒᵖ ⥤ (C ⥤ Type v₁) :=
{ obj := λ X : C,
  { obj := λ Y, X ⟶ Y,
    map := λ Y Y' f g, g ≫ f,
    map_comp' := begin intros X_1 Y Z f g, ext1, dsimp at *, erw [category.assoc] end,
    map_id' := begin intros X_1, ext1, dsimp at *, erw [category.comp_id] end },
  map := λ X X' f, { app := λ Y g, f ≫ g },
  map_comp' := begin intros X Y Z f g, ext1, ext1, dsimp at *, erw [category.assoc] end,
  map_id' := begin intros X, ext1, ext1, dsimp at *, erw [category.id_comp] end }

namespace yoneda
@[simp] lemma obj_obj (X Y : C) : (yoneda.obj X).obj Y = (Y ⟶ X) := rfl
@[simp] lemma obj_map (X : C) {Y Y' : C} (f : Y ⟶ Y') : (yoneda.obj X).map f = λ g, f ≫ g := rfl
@[simp] lemma map_app {X X' : C} (f : X ⟶ X') (Y : C) : (yoneda.map f).app Y = λ g, g ≫ f := rfl

lemma obj_map_id {X Y : Cᵒᵖ} (f : X ⟶ Y) :
  ((@yoneda C _).obj X).map f (𝟙 X) = ((@yoneda C _).map f).app Y (𝟙 Y) :=
by obviously

@[simp] lemma naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y)
  {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : f ≫ α.app Z' h = α.app Z (f ≫ h) :=
begin erw [functor_to_types.naturality], refl end

instance yoneda_fully_faithful : fully_faithful (@yoneda C _) :=
{ preimage := λ X Y f, (f.app X) (𝟙 X),
  injectivity' := λ X Y f g p,
  begin
    injection p with h,
    convert (congr_fun (congr_fun h X) (𝟙 X)) ; simp
  end }

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply yoneda.ext,
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C)
  (p : Π {Z : C}, (Z ⟶ X) → (Z ⟶ Y)) (q : Π {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
  (h₁ : Π {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : Π {Z : C} (f : Z ⟶ Y), p (q f) = f)
  (n : Π {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
@preimage_iso _ _ _ _ yoneda _ _ _ _
  (nat_iso.of_components (λ Z, { hom := p, inv := q, }) (by tidy))

-- We need to help typeclass inference with some awkward universe levels here.
instance prod_category_instance_1 : category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
category_theory.prod.{(max u₁ v₁)  v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

instance prod_category_instance_2 : category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
category_theory.prod.{v₁ (max u₁ v₁)} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

end yoneda

namespace coyoneda
@[simp] lemma obj_obj (X Y : C) : (coyoneda.obj X).obj Y = (X ⟶ Y) := rfl
@[simp] lemma obj_map {X' X : C} (f : X' ⟶ X) (Y : C) : (coyoneda.obj Y).map f = λ g, g ≫ f := rfl
@[simp] lemma map_app (X : C) {Y Y' : C} (f : Y ⟶ Y') : (coyoneda.map f).app X = λ g, f ≫ g := rfl
end coyoneda

class representable (F : Cᵒᵖ ⥤ Type v₁) :=
(X : C)
(w : yoneda.obj X ≅ F)

variables (C)
open yoneda

def yoneda_evaluation : (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) ⥤ Type (max u₁ v₁) :=
(evaluation_uncurried Cᵒᵖ (Type v₁)) ⋙ ulift_functor.{u₁}

@[simp] lemma yoneda_evaluation_map_down
  (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (x : (yoneda_evaluation C).obj P) :
  ((yoneda_evaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) := rfl

def yoneda_pairing : (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) ⥤ Type (max u₁ v₁) :=
(functor.prod yoneda.op (functor.id (Cᵒᵖ ⥤ Type v₁))) ⋙ functor.hom (Cᵒᵖ ⥤ Type v₁)

@[simp] lemma yoneda_pairing_map
  (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yoneda_pairing C).obj P) :
  (yoneda_pairing C).map α β = yoneda.map α.1 ≫ β ≫ α.2 := rfl

def yoneda_lemma : yoneda_pairing C ≅ yoneda_evaluation C :=
{ hom :=
  { app := λ F x, ulift.up ((x.app F.1) (𝟙 F.1)),
    naturality' :=
    begin
      intros X Y f, ext1, ext1,
      cases f, cases Y, cases X,
      dsimp at *, simp at *,
      erw [←functor_to_types.naturality,
           obj_map_id,
           functor_to_types.naturality,
           functor_to_types.map_id]
    end },
  inv :=
  { app := λ F x,
    { app := λ X a, (F.2.map a) x.down,
      naturality' :=
      begin
        intros X Y f, ext1,
        cases x, cases F,
        dsimp at *,
        erw [functor_to_types.map_comp]
      end },
    naturality' :=
    begin
      intros X Y f, ext1, ext1, ext1,
      cases x, cases f, cases Y, cases X,
      dsimp at *,
      erw [←functor_to_types.naturality, functor_to_types.map_comp]
    end },
  hom_inv_id' :=
  begin
    ext1, ext1, ext1, ext1, cases X, dsimp at *,
    erw [←functor_to_types.naturality,
         obj_map_id,
         functor_to_types.naturality,
         functor_to_types.map_id]
  end,
  inv_hom_id' :=
  begin
    ext1, ext1, ext1,
    cases x, cases X,
    dsimp at *,
    erw [functor_to_types.map_id]
  end }.

variables {C}

@[simp] def yoneda_sections (X : C) (F : Cᵒᵖ ⥤ Type v₁) : (yoneda.obj X ⟹ F) ≅ ulift.{u₁} (F.obj X) :=
nat_iso.app (yoneda_lemma C) (X, F)

omit 𝒞
@[simp] def yoneda_sections_small {C : Type u₁} [small_category C] (X : C) (F : Cᵒᵖ ⥤ Type u₁) : (yoneda.obj X ⟹ F) ≅ F.obj X :=
yoneda_sections X F ≪≫ ulift_trivial _

end category_theory
