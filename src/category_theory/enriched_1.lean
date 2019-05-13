-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.monoidal.types
import category_theory.monoidal.functor

universes v u

open category_theory
open category_theory.monoidal

namespace category_theory

open category_theory.monoidal.monoidal_category

variables (C : Sort u) [𝒞 : category.{v+1} C]
variables (V : Sort v) [𝒱 : monoidal_category.{v} V]
include 𝒞 𝒱

set_option pp.universes true
class enriched_over (F : lax_monoidal_functor.{v v+1} V (Type v)) :=
(e_hom   : C → C → V)
(e_id    : Π X : C, tensor_unit V ⟶ e_hom X X)
(e_comp  : Π X Y Z : C, e_hom X Y ⊗ e_hom Y Z ⟶ e_hom X Z)
(e_hom_F : Π X Y : C, F.obj (e_hom X Y) = (X ⟶ Y)) -- is this 'evil'?
(e_id_F  : Π X : C, F.map (e_id X) begin end = 𝟙 X)

end category_theory
