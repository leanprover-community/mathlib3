/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.monad.products
import category_theory.over

/-!
# Adjunctions related to the over category

Construct the left adjoint `star X` to `over.forget X : over X ⥤ C`.

## TODO
Show `star X` itself has a left adjoint provided `C` is locally cartesian closed.
-/
noncomputable theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory
open category limits comonad

variables {C : Type u} [category.{v} C] (X : C)

/--
The functor from `C` to `over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps]
def star [has_binary_products C] : C ⥤ over X :=
cofree _ ⋙ coalgebra_to_over X

/--
The functor `over.forget X : over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forget_adj_star [has_binary_products C] : over.forget X ⊣ star X :=
(coalgebra_equiv_over X).symm.to_adjunction.comp _ _ (adj _)

/--
Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [has_binary_products C] : is_left_adjoint (over.forget X) := ⟨_, forget_adj_star X⟩

@[simps {rhs_md := semireducible, simp_rhs := tt}]
def base_change [has_pullbacks C] {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj := λ g, over.mk (pullback.snd : pullback g.hom f ⟶ _),
  map := λ g₁ g₂ i, over.hom_mk (pullback.map _ _ _ _ i.left (𝟙 _) (𝟙 _) (by simp) (by simp))
    (by simp) }
.

@[simps]
def base_change_unit [has_pullbacks C] {X Y : C} (f : X ⟶ Y) :
  𝟭 _ ⟶ over.map f ⋙ base_change f :=
{ app := λ g, over.hom_mk (pullback.lift (𝟙 _) g.hom (category.id_comp _)) (by { dsimp, simp }) }

@[simps]
def map_adj_base_change [has_pullbacks C] {X Y : C} (f : X ⟶ Y) : over.map f ⊣ base_change f :=
adjunction.mk_of_unit_counit
{ unit := base_change_unit f,
  counit := { app := λ g, over.hom_mk pullback.fst pullback.condition } }

end category_theory
