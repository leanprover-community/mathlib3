/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.binary_products
import category_theory.monad.products
import category_theory.over

/-!
# Adjunctions related to the over category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
@[simps obj_left obj_hom map_left]
def star [has_binary_products C] : C ⥤ over X :=
cofree _ ⋙ coalgebra_to_over X

/--
The functor `over.forget X : over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forget_adj_star [has_binary_products C] : over.forget X ⊣ star X :=
(coalgebra_equiv_over X).symm.to_adjunction.comp (adj _)

/--
Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [has_binary_products C] : is_left_adjoint (over.forget X) := ⟨_, forget_adj_star X⟩

end category_theory
