/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.over
import category_theory.limits.preserves.basic
import category_theory.limits.creates
import category_theory.limits.shapes.binary_products
import category_theory.monad.products

noncomputable theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory
open category limits comonad

variables {C : Type u} [category.{v} C] (X : C)

def star [has_binary_products C] : C ⥤ over X :=
cofree _ ⋙ coalgebra_to_over X

lemma forget_iso [has_binary_products C] : over_to_coalgebra X ⋙ forget _ = over.forget X :=
rfl

/--
Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forget_adj_star [has_binary_products C] : over.forget X ⊣ star X :=
(coalgebra_equiv_over X).symm.to_adjunction.comp _ _ (adj _)

/--
(Implementation). Define the "dependent sum" functor, which makes a functor `C / A ⥤ C / B` given
a morphism `f : A ⟶ B`. This functor is naturally isomorphic to `over.map f`, but in this form it
is easier to prove adjunction properties, as (if enough structure exists), `over.forget` is a left
adjoint and the first functor is an equivalence.
As far as possible, definitions should use `over.map` rather than this.
-/
def dependent_sum {A B : C} (f : A ⟶ B) : over A ⥤ over B :=
(over.iterated_slice_equiv (over.mk f)).inverse ⋙ over.forget _

/--
`over.map f` gives nice definitional equalities but `dependent_sum` makes it easy to prove
adjunction properties
-/
def dependent_sum_iso_over_map {A B : C} (f : A ⟶ B) : dependent_sum f ≅ over.map f :=
nat_iso.of_components (λ X, over.iso_mk (iso.refl _)) (λ X Y g, by tidy)

end category_theory
