-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.concrete_category
import category_theory.monoidal.types
import category_theory.monoidal.functor

universes v u

open category_theory
open category_theory.monoidal

namespace category_theory

open category_theory.monoidal_category

variables {c d : Type u → Type v}

class concrete_monoidal_category (hom : out_param $ ∀ {α β}, c α → c β → (α → β) → Prop) extends concrete_category @hom :=
(tensor_unit : bundled c)
(tensor_obj : Π (α β : bundled c), bundled c)
(μ : Π (α β : bundled c), α.α × β.α → (tensor_obj α β).α)
(μ_ext : Π {α β γ : bundled c} (f g : (tensor_obj α β) ⟶ γ) (h : (f : (tensor_obj α β).α → γ.α) ∘ μ α β = (g : (tensor_obj α β).α → γ.α) ∘ μ α β), f = g)
(tensor_hom : Π {α β γ δ : bundled c} (f : α ⟶ β) (g : γ ⟶ δ), (tensor_obj α γ) ⟶ (tensor_obj β δ))

attribute [extensionality] concrete_monoidal_category.μ_ext

open concrete_monoidal_category

variables (hom : ∀ {α β : Type u}, c α → c β → (α → β) → Prop)
variables [h : concrete_monoidal_category @hom]
include h

instance : monoidal_category (bundled c) :=
{ ..h }



variables (C : Sort u) [𝒞 : category.{v+1} C]
variables (c : Sort v → Sort v) [𝒱 : monoidal_category.{v} (bundled c)]
include 𝒞 𝒱

set_option pp.universes true
class enriched_over (F : is_lax_monoidal.{v v+1} (@bundled.α c)) :=
(e_hom   : C → C → V)
(e_id    : Π X : C, tensor_unit V ⟶ e_hom X X)
(e_comp  : Π X Y Z : C, e_hom X Y ⊗ e_hom Y Z ⟶ e_hom X Z)
(e_hom_F : Π X Y : C, F.obj (e_hom X Y) = (X ⟶ Y)) -- is this 'evil'?
(e_id_F  : Π X : C, F.map (e_id X) begin end = 𝟙 X)

end category_theory
