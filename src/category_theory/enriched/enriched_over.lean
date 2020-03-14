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

-- move to `equiv/basic.lean`?
@[simp] lemma foo {X Y : Type u} (e : X ≃ Y) (y : Y) : e.inv_fun y = e.symm y := rfl

open category_theory.monoidal_category

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

def forget.ε : (forget V).obj (𝟙_ V) := (forget.lax.{v} V).ε (by tidy)

variables {V}

def forget.μ {X Y : V} (x : (forget V).obj X) (y : (forget V).obj Y) : (forget V).obj (X ⊗ Y) :=
(forget.lax.{v} V).μ X Y (by { fsplit, rintros ⟨⟩, exact x, exact y, tidy, })

/--
Convert a morphism from the monoidal unit of `V` to `X` into a term of the underlying type of `X`.
-/
def as_term {X : V} (f : 𝟙_ V ⟶ X) : (forget V).obj X := (forget V).map f (forget.ε V)
-- If `forget V` is represented by some object `R`, then we could construct
--   def of_term {X : V} (x : (forget V).obj X) : R ⟶ X := sorry
-- e.g. `forget Type` is represented by `punit`, and `forget CommRing` is represented by $ℤ[x]$.
end

open concrete_monoidal_category

variables (V : Type (v+1)) [category.{v} V] [concrete_category.{v} V] [monoidal_category.{v} V] [𝒱 : concrete_monoidal_category.{v} V]
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒱 𝒞

class enriched_over :=
(e_hom   : C → C → V)
(notation X ` ⟶[V] ` Y:10 := e_hom X Y)
(e_id    : Π X : C, 𝟙_ V ⟶ (X ⟶[V] X))
(notation ` 𝟙[V] ` := e_id)
(e_comp  : Π X Y Z : C, (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z))
(e_hom_forget : Π X Y : C, (forget V).obj (X ⟶[V] Y) ≃ (X ⟶ Y))
(e_id_forget  : Π X : C, e_hom_forget X X (as_term (𝟙[V] X)) = 𝟙 X . obviously)
(e_comp_forget : Π (X Y Z : C) (f : (forget V).obj (X ⟶[V] Y)) (g : (forget V).obj (Y ⟶[V] Z)),
  e_hom_forget X Y f ≫ e_hom_forget Y Z g = e_hom_forget X Z ((forget V).map (e_comp X Y Z) (forget.μ f g)) . obviously)

restate_axiom enriched_over.e_id_forget
restate_axiom enriched_over.e_comp_forget

-- We check that we can construct the trivial enrichment of `Type` in `Type`:
example : enriched_over (Type u) (Type u) :=
{ e_hom := λ X Y, X ⟶ Y,
  e_id := λ X, λ _, 𝟙 _,
  e_comp := λ X Y Z p, p.val (limits.walking_pair.left) ≫ p.val (limits.walking_pair.right), -- that was ugly...
  e_hom_forget := λ X Y, equiv.refl _ }


end category_theory
