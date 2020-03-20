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
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒱 𝒞

class enriched_over :=
(e_hom   : C → C → V)
(notation X ` ⟶[V] ` Y:10 := e_hom X Y)
(e_id    : Π X : C, 𝟙_ V ⟶ (X ⟶[V] X))
(notation ` 𝟙[V] ` := e_id)
(e_comp  : Π X Y Z : C, (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z))
(e_hom_forget : Π X Y : C, (forget V).obj (X ⟶[V] Y) ≃ (X ⟶ Y))
(e_id_forget'  : Π X : C, (e_hom_forget X X) (forget.as_term (𝟙[V] X)) = 𝟙 X . obviously)
(e_comp_forget' : Π (X Y Z : C) (f : (forget V).obj (X ⟶[V] Y)) (g : (forget V).obj (Y ⟶[V] Z)),
  (e_hom_forget X Y) f ≫ (e_hom_forget Y Z) g = (e_hom_forget X Z) ((forget V).map (e_comp X Y Z) (forget.μ f g)) . obviously)

restate_axiom enriched_over.e_id_forget'
restate_axiom enriched_over.e_comp_forget'

notation X ` ⟶[`V`] ` Y:10 := enriched_over.e_hom V X Y
notation ` 𝟙[`V`] `X := enriched_over.e_id V X

example [enriched_over V C] (X Y : C) : V := X ⟶[V] Y
example [enriched_over V C] (X : C) : 𝟙_ V ⟶ (X ⟶[V] X) := 𝟙[V] X

/-- We check that we can construct the trivial enrichment of `Type` in `Type`. -/
instance : enriched_over (Type u) (Type u) :=
{ e_hom := λ X Y, X ⟶ Y,
  e_id := λ X, λ _, 𝟙 _,
  e_comp := λ X Y Z p, (limits.prod.fst : (X ⟶ Y) ⊗ (Y ⟶ Z) ⟶ (X ⟶ Y)) p ≫ (limits.prod.snd : (X ⟶ Y) ⊗ (Y ⟶ Z) ⟶ (Y ⟶ Z)) p,
  e_hom_forget := λ X Y, equiv.refl _ }

section
variables (W : Type (v+1)) [large_category W] [concrete_category W]
  [monoidal_category.{v} W] [𝒲 : concrete_monoidal_category W]
include 𝒲
variables [has_forget₂ V W] [lax_monoidal.{v v} ((forget₂ V W).obj)]

def transport [enriched_over V C] : enriched_over W C :=
{ e_hom := λ X Y, (forget₂ V W).obj (X ⟶[V] Y),
  e_id := λ X, (lax_monoidal.ε (forget₂ V W).obj) ≫ (forget₂ V W).map (𝟙[V] X),
  e_comp := λ X Y Z, lax_monoidal.μ.{v v} (forget₂ V W).obj (X ⟶[V] Y) (Y ⟶[V] Z) ≫ (forget₂ V W).map (enriched_over.e_comp V _ _ _),
  e_hom_forget := λ X Y, (equiv.cast (forget_obj_forget₂_obj V W (X ⟶[V] Y))).trans (enriched_over.e_hom_forget V X Y),
  e_id_forget' := sorry,
  e_comp_forget' := λ X Y Z f g,
  sorry, }
end

end category_theory
