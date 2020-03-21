/-
-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/
import category_theory.concrete_category.concrete_monoidal_category

universes v u

open category_theory
open category_theory.monoidal_category

namespace category_theory

variables (V : Type (v+1)) [large_category V] [concrete_category V]
  [monoidal_category.{v} V] [𝒱 : concrete_monoidal_category V]
include 𝒱

local attribute [instance] concrete_category.has_coe_to_sort

class category_over (C : Type u) :=
(hom   : C → C → V)
(notation X ` ⟶[V] ` Y:10 := hom X Y)
(id    : Π X : C, 𝟙_ V ⟶ (X ⟶[V] X))
(notation `𝟙[V] `X := id X)
(notation `𝟙' ` X := forget.as_term (id X))
(comp  : Π X Y Z : C, (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z))
(notation f ` ≫' ` g := (forget V).map (comp _ _ _) (forget.μ f g))
(id_comp' : ∀ (X Y : C) (f : X ⟶[V] Y), ((𝟙' X) ≫' f) = f . obviously)
(comp_id' : ∀ (X Y : C) (f : X ⟶[V] Y), (f ≫' (𝟙' Y)) = f . obviously)
(assoc' : ∀ (W X Y Z : C) (f : W ⟶[V] X) (g : X ⟶[V] Y) (h : Y ⟶[V] Z),
  ((f ≫' g) ≫' h) = (f ≫' (g ≫' h)) . obviously)

restate_axiom category_over.id_comp'
restate_axiom category_over.comp_id'
restate_axiom category_over.assoc'

attribute [simp] category_over.id_comp category_over.comp_id category_over.assoc

notation X ` ⟶[`V`] ` Y:10 := category_over.hom V X Y
notation `𝟙[`V`] `X := category_over.id V X

example (C : Type u) [category_over V C] (X Y : C) : V := X ⟶[V] Y
example (C : Type u) [category_over V C] (X : C) : 𝟙_ V ⟶ (X ⟶[V] X) := 𝟙[V] X

/-- We check that we can construct the trivial enrichment of `Type` in `Type`. -/
instance : category_over (Type u) (Type u) :=
{ hom := λ X Y, X ⟶ Y,
  id := λ X, λ _, 𝟙 _,
  comp := λ X Y Z p, (limits.prod.fst : (X ⟶ Y) ⊗ (Y ⟶ Z) ⟶ (X ⟶ Y)) p ≫ (limits.prod.snd : (X ⟶ Y) ⊗ (Y ⟶ Z) ⟶ (Y ⟶ Z)) p, }

@[priority 100]
instance category_of_category_over (C : Type u) [category_over V C] : category.{v} C :=
{ hom := λ X Y, ((X ⟶[V] Y : V) : Type v),
  id := λ X, forget.as_term (category_over.id V X),
  comp := λ X Y Z f g, (forget V).map (category_over.comp V _ _ _) (forget.μ f g), }

section
variables (W : Type (v+1)) [large_category W] [concrete_category W]
  [monoidal_category.{v} W] [𝒲 : concrete_monoidal_category W]
include 𝒲
variables [has_forget₂ V W] [lax_monoidal.{v v} ((forget₂ V W).obj)]

def transport (C : Type u) [category_over V C] : category_over W C :=
{ hom := λ X Y, (forget₂ V W).obj (X ⟶[V] Y),
  id := λ X, (lax_monoidal.ε (forget₂ V W).obj) ≫ (forget₂ V W).map (𝟙[V] X),
  comp := λ X Y Z, lax_monoidal.μ.{v v} (forget₂ V W).obj (X ⟶[V] Y) (Y ⟶[V] Z) ≫ (forget₂ V W).map (category_over.comp V _ _ _),
  id_comp' := λ X Y f,
  begin
    dsimp,
    simp,
    dsimp [forget.μ],
    dsimp [forget.lax],
    dsimp [forget.as_term],
    simp,
    erw forget_map_forget₂_map V W,
  end,
  comp_id' := sorry,
  assoc' := sorry, }
end

end category_theory
