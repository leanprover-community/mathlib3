/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.braided
import category_theory.reflects_isomorphisms

/-!
# Half braidings and the Drinfeld center of a monoidal category

We define `center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

For now we only define the `category` structure on `center C`.
Writing down the `monoidal_category` and `braided_category` data is easy enough,
but verifying the axioms seems intimidating!
-/

open category_theory
open category_theory.monoidal_category

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]

/--
A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`, natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same as natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which send the unique
`0`-morphism to `X`.
-/
@[nolint has_inhabited_instance]
structure half_braiding (X : C) :=
(β : Π U, X ⊗ U ≅ U ⊗ X)
(naturality' : ∀ {U U'} (f : U ⟶ U'), (𝟙 X ⊗ f) ≫ (β U').hom = (β U).hom ≫ (f ⊗ 𝟙 X) . obviously)

restate_axiom half_braiding.naturality'
attribute [simp, reassoc] half_braiding.naturality

variables (C)
/--
The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, where `X : C`
and `b` is a half-braiding on `X`.
-/
@[nolint has_inhabited_instance]
def center := Σ X : C, half_braiding X

namespace center

variables {C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext, nolint has_inhabited_instance]
structure hom (X Y : center C) :=
(f : X.1 ⟶ Y.1)
(comm' : ∀ U, (f ⊗ 𝟙 U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (𝟙 U ⊗ f) . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

instance : category (center C) :=
{ hom := hom,
  id := λ X, { f := 𝟙 X.1, },
  comp := λ X Y Z f g, { f := f.f ≫ g.f, }, }

@[simp] lemma id_f (X : center C) : hom.f (𝟙 X) = 𝟙 X.1 := rfl
@[simp] lemma comp_f {X Y Z : center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f := rfl

/--
Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
def iso_mk {X Y : center C} (f : X ⟶ Y) [is_iso f.f] : X ≅ Y :=
{ hom := f,
  inv := ⟨inv f.f, λ U, begin
    dsimp,
    apply (cancel_epi (f.f ⊗ 𝟙 U)).mp,
    simp [←comp_tensor_id_assoc, ←id_tensor_comp],
  end⟩, }

section
variables (C)

/-- The forgetful functor from the Drinfeld center to the original category. -/
@[simps]
def forget : center C ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.f, }

instance : reflects_isomorphisms (forget C) :=
{ reflects := λ A B f i, by { dsimp at i, resetI, change is_iso (iso_mk f).hom, apply_instance, } }

end

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_obj (X Y : center C) : center C :=
⟨X.1 ⊗ Y.1,
  { β := λ U,
    α_ _ _ _ ≪≫ (iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm
      ≪≫ (X.2.β U ⊗ iso.refl Y.1) ≪≫ α_ _ _ _,
    naturality' := λ U U' f,
    begin
      dsimp,
      rw [category.assoc, category.assoc, category.assoc, category.assoc,
        id_tensor_associator_naturality_assoc, ←id_tensor_comp_assoc, half_braiding.naturality,
        id_tensor_comp_assoc, associator_inv_naturality_assoc, ←comp_tensor_id_assoc,
        half_braiding.naturality, comp_tensor_id_assoc, associator_naturality, ←tensor_id],
    end, }⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_hom {X₁ Y₁ X₂ Y₂ : center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  tensor_obj X₁ X₂ ⟶ tensor_obj Y₁ Y₂ :=
{ f := f.f ⊗ g.f,
  comm' := sorry }

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_unit : center C :=
⟨𝟙_ C,
  { β := λ U, (λ_ U) ≪≫ (ρ_ U).symm,
    naturality' := sorry, }⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def associator (X Y Z : center C) : tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
iso_mk ⟨(α_ X.1 Y.1 Z.1).hom, begin sorry, end⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def left_unitor (X : center C) : tensor_obj tensor_unit X ≅ X :=
iso_mk ⟨(λ_ X.1).hom, begin sorry, end⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def right_unitor (X : center C) : tensor_obj X tensor_unit ≅ X :=
iso_mk ⟨(ρ_ X.1).hom, begin sorry, end⟩

section
local attribute [simp] associator_naturality left_unitor_naturality right_unitor_naturality
  pentagon

instance : monoidal_category (center C) :=
{ tensor_obj := λ X Y, tensor_obj X Y,
  tensor_hom := λ X₁ Y₁ X₂ Y₂ f g, tensor_hom f g,
  tensor_unit := tensor_unit,
  associator := associator,
  left_unitor := left_unitor,
  right_unitor := right_unitor, }

@[simp] lemma tensor_β (X Y : center C) (U : C) :
  (X ⊗ Y).2.β U =
    α_ _ _ _ ≪≫ (iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm
      ≪≫ (X.2.β U ⊗ iso.refl Y.1) ≪≫ α_ _ _ _ :=
rfl
@[simp] lemma tensor_f {X₁ Y₁ X₂ Y₂ : center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  (f ⊗ g).f = f.f ⊗ g.f :=
rfl

end

/-- Auxiliary definition for the `braided_category` instance on `center C`. -/
@[simps]
def braiding (X Y : center C) : X ⊗ Y ≅ Y ⊗ X :=
iso_mk ⟨(X.2.β Y.1).hom, λ U, begin simp, sorry end⟩

instance : braided_category (center C) :=
{ braiding := braiding,
  braiding_naturality' := sorry,
  hexagon_forward' := sorry,
  hexagon_reverse' := sorry, }

end center

end category_theory
