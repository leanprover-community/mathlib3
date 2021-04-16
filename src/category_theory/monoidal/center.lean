/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.braided

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

end center

end category_theory
