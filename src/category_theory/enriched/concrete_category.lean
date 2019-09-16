-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.concrete_category
import category_theory.monoidal.types
import category_theory.monoidal.functorial

universes v u

open category_theory
open category_theory.monoidal

namespace category_theory

open category_theory.monoidal_category


class concrete_monoidal_category (C : Type (u+1)) extends concrete_category.{u} C, monoidal_category.{u} C :=
(lax_monoidal : lax_monoidal.{u u} (concrete_category.forget C).obj)

attribute [instance] concrete_monoidal_category.lax_monoidal

open concrete_monoidal_category

variables (C : Type u) [𝒞 : category.{v} C]
variables (V : Type (v+1)) [𝒱 : concrete_monoidal_category.{v} V]
include 𝒞 𝒱

set_option pp.universes true
class enriched_over :=
(e_hom   : C → C → V)
(e_id    : Π X : C, tensor_unit V ⟶ e_hom X X)
(e_comp  : Π X Y Z : C, e_hom X Y ⊗ e_hom Y Z ⟶ e_hom X Z)
(e_hom_forget : Π X Y : C, (forget V).obj (e_hom X Y) ≃ (X ⟶ Y)) -- make X Y implicit?
(e_id_forget  : Π X : C, e_hom_forget X X ((forget V).map (e_id X) sorry) = 𝟙 X)

end category_theory
