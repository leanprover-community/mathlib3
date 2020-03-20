/-
-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/
import category_theory.concrete_category
import category_theory.monoidal.types
import category_theory.monoidal.functorial

universes v u

open category_theory
open category_theory.monoidal_category

namespace category_theory

/--
A concrete monoidal category is a monoidal category whose forgetful functor to `Type` is lax
monoidal. A prototypical example to think about is `Vec`, equipped with tensor products as the
monoidal structure, forgetting to `Type`, equipped with cartesian products as the monoidal
structure. Observe that we have a map (in `Type`) `V × W → V ⊗ W`, which is the lax tensorator, but
there is not a map in the other direction.
-/
class concrete_monoidal_category (C : Type (u+1)) [category.{u} C] [concrete_category.{u} C] [monoidal_category.{u} C] :=
(lax_monoidal : lax_monoidal.{u u} (concrete_category.forget C).obj)

attribute [instance] concrete_monoidal_category.lax_monoidal

instance : concrete_monoidal_category (Type u) :=
{ lax_monoidal := category_theory.lax_monoidal_id }

section
variables (V : Type (v+1)) [category.{v} V] [concrete_category.{v} V] [monoidal_category.{v} V] [𝒱 : concrete_monoidal_category.{v} V]
include 𝒱

def forget.lax : lax_monoidal_functor.{v v} V (Type v) := lax_monoidal_functor.of (forget V).obj

-- The `by tidy` here is constructing the unique element of the terminal object in Type,
-- which unfortunately is not `punit`, but some unspeakable function type,
-- that `tidy` is clever enough to produce the element of.
def forget.ε : (forget V).obj (𝟙_ V) := (forget.lax.{v} V).ε (by tidy)

variables {V}

def forget.μ {X Y : V} (x : (forget V).obj X) (y : (forget V).obj Y) : (forget V).obj (X ⊗ Y) :=
(forget.lax.{v} V).μ X Y (by { fsplit, rintros ⟨⟩, exact x, exact y, tidy, })

/--
Convert a morphism from the monoidal unit of `V` to `X` into a term of the underlying type of `X`.
-/
def forget.as_term {X : V} (f : 𝟙_ V ⟶ X) : (forget V).obj X := (forget V).map f (forget.ε V)
end

end category_theory
