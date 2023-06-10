/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.bicategory.End
import category_theory.monoidal.functor

/-!
# Promoting a monoidal category to a single object bicategory.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A monoidal category can be thought of as a bicategory with a single object.

The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.

We verify that the endomorphisms of that single object recovers the original monoidal category.

One could go much further: the bicategory of monoidal categories
(equipped with monoidal functors and monoidal natural transformations)
is equivalent to the bicategory consisting of
* single object bicategories,
* pseudofunctors, and
* (oplax) natural transformations `η` such that `η.app punit.star = 𝟙 _`.
-/

namespace category_theory

variables (C : Type*) [category C] [monoidal_category C]

/--
Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
@[nolint unused_arguments, derive inhabited]
def monoidal_single_obj (C : Type*) [category C] [monoidal_category C] := punit

open monoidal_category

instance : bicategory (monoidal_single_obj C) :=
{ hom := λ _ _, C,
  id := λ _, 𝟙_ C,
  comp := λ _ _ _ X Y, X ⊗ Y,
  whisker_left := λ _ _ _ X Y Z f, 𝟙 X ⊗ f,
  whisker_right := λ _ _ _ X Y f Z, f ⊗ 𝟙 Z,
  associator := λ _ _ _ _ X Y Z, α_ X Y Z,
  left_unitor := λ _ _ X, λ_ X,
  right_unitor := λ _ _ X, ρ_ X,
  comp_whisker_left' :=
    by { intros, rw [associator_inv_naturality, iso.hom_inv_id_assoc, tensor_id], },
  whisker_assoc' := by { intros, rw [associator_inv_naturality, iso.hom_inv_id_assoc], },
  whisker_right_comp' :=
    by { intros, rw [←tensor_id, associator_naturality, iso.inv_hom_id_assoc], },
  id_whisker_left' := by { intros, rw [left_unitor_inv_naturality, iso.hom_inv_id_assoc], },
  whisker_right_id' := by { intros, rw [right_unitor_inv_naturality, iso.hom_inv_id_assoc], },
  pentagon' := by { intros, rw [pentagon], }, }

namespace monoidal_single_obj

/-- The unique object in the bicategory obtained by "promoting" a monoidal category. -/
@[nolint unused_arguments]
protected def star : monoidal_single_obj C := punit.star

/--
The monoidal functor from the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
to the original monoidal category.

We subsequently show this is an equivalence.
-/
@[simps]
def End_monoidal_star_functor : monoidal_functor (End_monoidal (monoidal_single_obj.star C)) C :=
{ obj := λ X, X,
  map := λ X Y f, f,
  ε := 𝟙 _,
  μ := λ X Y, 𝟙 _,
  μ_natural' := λ X Y X' Y' f g, begin
    dsimp,
    simp only [category.id_comp, category.comp_id],
    -- Should we provide further simp lemmas so this goal becomes visible?
    exact (tensor_id_comp_id_tensor _ _).symm,
  end, }

noncomputable theory

/--
The equivalence between the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
and the original monoidal category.
-/
def End_monoidal_star_functor_is_equivalence :
  is_equivalence (End_monoidal_star_functor C).to_functor :=
{ inverse :=
  { obj := λ X, X,
    map := λ X Y f, f, },
  unit_iso := nat_iso.of_components (λ X, as_iso (𝟙 _)) (by tidy),
  counit_iso := nat_iso.of_components (λ X, as_iso (𝟙 _)) (by tidy), }

end monoidal_single_obj

end category_theory
