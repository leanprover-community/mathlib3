/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category
import category_theory.const

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.monoidal_category

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

namespace category_theory.monoidal_category_functor_category

variables (F G F' G' : C ⥤ D)

@[simps]
def tensor_obj : C ⥤ D :=
{ obj := λ X, F.obj X ⊗ G.obj X,
  map := λ X Y f, F.map f ⊗ G.map f,
  map_id' := λ X, by rw [F.map_id, G.map_id, tensor_id],
  map_comp' := λ X Y Z f g, by rw [F.map_comp, G.map_comp, tensor_comp], }

variables {F G F' G'}
variables (α : F ⟶ G) (β : F' ⟶ G')

@[simps]
def tensor_hom : tensor_obj F F' ⟶ tensor_obj G G' :=
{ app := λ X, α.app X ⊗ β.app X,
  naturality' :=
  λ X Y f, by { dsimp, rw [←tensor_comp, α.naturality, β.naturality, tensor_comp], } }

end category_theory.monoidal_category_functor_category

open category_theory.monoidal_category_functor_category

instance : monoidal_category (C ⥤ D) :=
{ tensor_obj := λ F G, tensor_obj F G,
  tensor_hom := λ F G F' G' α β, tensor_hom α β,
  tensor_id' := λ F G, by { ext, dsimp, rw [tensor_id], },
  tensor_comp' := λ F G H F' G' H' α β γ δ, by { ext, dsimp, rw [tensor_comp], },
  tensor_unit := (category_theory.functor.const C).obj (𝟙_ D),
  left_unitor :=  λ F,
    nat_iso.of_components (λ X, λ_ (F.obj X)) (λ X Y f, by { dsimp, rw left_unitor_naturality, }),
  right_unitor := λ F,
    nat_iso.of_components (λ X, ρ_ (F.obj X)) (λ X Y f, by { dsimp, rw right_unitor_naturality, }),
  associator := λ F G H,
    nat_iso.of_components
      (λ X, α_ (F.obj X) (G.obj X) (H.obj X)) (λ X Y f, by { dsimp, rw associator_naturality, }),
  left_unitor_naturality' := λ F G α, by { ext X, dsimp, rw left_unitor_naturality, },
  right_unitor_naturality' := λ F G α, by { ext X, dsimp, rw right_unitor_naturality, },
  associator_naturality' := λ F G H F' G' H' α β γ, by { ext X, dsimp, rw associator_naturality, },
  triangle' := λ F G, begin ext X, dsimp, rw triangle, end,
  pentagon' := λ F G H K, begin ext X, dsimp, rw pentagon, end, }
