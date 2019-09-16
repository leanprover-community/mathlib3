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

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

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

open enriched_category

section
variables {V}
variables {W : Type (v+1)} [large_category W] [𝒲 : monoidal_category.{v} W]
include 𝒲
variables (Λ : lax_monoidal_functor.{v v} V W)
def transport_enrichment (Λ : lax_monoidal_functor.{v v} V W) (C : Type u) := C

variables {C : Type u} [𝒞 : enriched_category V C]
include 𝒞

instance : enriched_category W (transport_enrichment Λ C) :=
{ hom := λ X Y : C, Λ.obj (X ⟶[V] Y),
  id := λ X : C, Λ.ε ≫ Λ.map (𝟙[V] X),
  comp := λ X Y Z : C, Λ.μ _ _ ≫ Λ.map (comp V X Y Z),
  id_comp' := λ X Y, sorry,
  comp_id' := sorry,
  assoc' := sorry }
end

section
variables (C : Type u) [𝒞 : enriched_category V C]
variables (D : Type u) [𝒟 : enriched_category V D]
include 𝒞 𝒟

structure enriched_functor :=
(obj : C → D)
(map : Π X Y : C, (X ⟶[V] Y) ⟶ (obj X ⟶[V] obj Y))
(map_id' : Π X : C, (𝟙[V] X) ≫ map X X = 𝟙[V] (obj X) . obviously)
(map_comp' : Π X Y Z : C, comp _ X Y Z ≫ map X Z = (map X Y ⊗ map Y Z) ≫ comp _ _ _ _ . obviously)

restate_axiom enriched_functor.map_id'
restate_axiom enriched_functor.map_comp'
attribute [simp, reassoc] enriched_functor.map_id enriched_functor.map_comp

end

namespace enriched_functor

variables (C : Type u) [𝒞 : enriched_category V C]
include 𝒞

def id : enriched_functor V C C :=
{ obj := id,
  map := λ X Y, 𝟙 (X ⟶[V] Y) }

variables {C}
variables {D : Type u} [𝒟 : enriched_category V D]
variables {E : Type u} [ℰ : enriched_category V E]
include 𝒟 ℰ

def comp (F : enriched_functor V C D) (G : enriched_functor V D E) : enriched_functor V C E :=
{ obj := λ X, G.obj (F.obj X),
  map := λ X Y, F.map _ _ ≫ G.map _ _  }

end enriched_functor

section

variables {C : Type u} [𝒞 : enriched_category V C]
variables {D : Type u} [𝒟 : enriched_category V D]
include 𝒞 𝒟
variables (F G : enriched_functor V C D)

-- We need at least a braiding on V before we can talk about natural transformations!

-- There is not always a V-object of natural transformations from F to G.
-- We can characterise the type of V-homs `α ⟶ (enriched_nat_trans F G)`.

-- structure enriched_nat_trans_yoneda (α : Vᵒᵖ) :=
-- (p : Π X : C, (unop α) ⟶ (F.obj X ⟶[V] G.obj X))
-- (h : Π X Y : C)

-- def enriched_nat_trans : Vᵒᵖ ⥤ Sort v :=
-- { obj := }


end

end category_theory
