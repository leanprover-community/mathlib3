-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.monoidal.types
import category_theory.monoidal.functor
import category_theory.opposites

universes v u

open category_theory
open category_theory.monoidal
open opposite

namespace category_theory

open category_theory.monoidal_category

variables (V : Type (v+1)) [large_category V] [𝒱 : monoidal_category.{v} V]
include 𝒱

class enriched_category (C : Type u) :=
(hom   : C → C → V)
(notation X ` ⟶[V] ` Y:10 := hom X Y)
(id    : Π X : C, 𝟙_ V ⟶ (X ⟶[V] X))
(notation ` 𝟙[V] ` := id) -- This notation is only temporary
(comp  : Π X Y Z : C, (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z))
(id_comp' : Π X Y : C, (𝟙[V] X ⊗ 𝟙 _) ≫ comp X X Y = (λ_ (X ⟶[V] Y)).hom . obviously)
(comp_id' : Π X Y : C, (𝟙 _ ⊗ 𝟙[V] Y) ≫ comp X Y Y = (ρ_ (X ⟶[V] Y)).hom . obviously)
(assoc' : Π W X Y Z : C, (α_ _ _ _).inv ≫ (comp W X Y ⊗ 𝟙 _) ≫ comp W Y Z = (𝟙 _ ⊗ comp X Y Z) ≫ comp W X Z . obviously)

restate_axiom enriched_category.id_comp'
restate_axiom enriched_category.comp_id'
restate_axiom enriched_category.assoc'
attribute [simp] enriched_category.id_comp enriched_category.comp_id enriched_category.assoc
attribute [reassoc] enriched_category.id_comp enriched_category.comp_id

notation `𝟙[` V `]` := enriched_category.id V
notation X ` ⟶[` V `] ` Y:10 := enriched_category.hom V X Y

end category_theory
