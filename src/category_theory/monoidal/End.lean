/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.functor

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

/--
The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).
-/
def endofunctor_monoidal_category : monoidal_category (C ⥤ C) :=
{ tensor_obj   := λ F G, F ⋙ G,
  tensor_hom   := λ F G F' G' α β, α ◫ β,
  tensor_unit  := 𝟭 C,
  associator   := λ F G H, functor.associator F G H,
  left_unitor  := λ F, functor.left_unitor F,
  right_unitor := λ F, functor.right_unitor F, }.

open category_theory.monoidal_category

variables [monoidal_category.{v} C]

local attribute [instance] endofunctor_monoidal_category
local attribute [reducible] endofunctor_monoidal_category

/--
Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
@[simps]
def tensoring_right_monoidal : monoidal_functor C (C ⥤ C) :=
{ ε := (right_unitor_nat_iso C).inv,
  μ := λ X Y,
  { app := λ Z, (α_ Z X Y).hom,
    naturality' := λ Z Z' f, by { dsimp, rw associator_naturality, simp, } },
  μ_natural' := λ X Y X' Y' f g, by { ext Z, dsimp, simp [associator_naturality], },
  associativity' := λ X Y Z, by { ext W, dsimp, simp [pentagon], },
  left_unitality' := λ X, by { ext Y, dsimp, rw [category.id_comp, triangle, ←tensor_comp], simp, },
  right_unitality' := λ X,
  begin
    ext Y, dsimp,
    rw [tensor_id, category.comp_id, right_unitor_tensor_inv, category.assoc, iso.inv_hom_id_assoc,
      ←id_tensor_comp, iso.inv_hom_id, tensor_id],
  end,
  ε_is_iso := by apply_instance,
  μ_is_iso := λ X Y,
    -- We could avoid needing to do this explicitly by
    -- constructing a partially applied analogue of `associator_nat_iso`.
  ⟨⟨{ app := λ Z, (α_ Z X Y).inv,
      naturality' := λ Z Z' f, by { dsimp, rw ←associator_inv_naturality, simp, } },
    by tidy⟩⟩,
  ..tensoring_right C }.

end category_theory
