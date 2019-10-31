/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import category_theory.products.basic

/-#
The associator functor `((C × D) × E) ⥤ (C × (D × E))` and its inverse form an equivalence.
-/

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory

namespace category_theory.prod

variables (C : Type u₁) [𝒞 : category.{v₁} C]
          (D : Type u₂) [𝒟 : category.{v₂} D]
          (E : Type u₃) [ℰ : category.{v₃} E]
include 𝒞 𝒟 ℰ

-- Here and below we specify explicitly the projections to generate `@[simp]` lemmas for, 
-- as the default behaviour of `@[simps]` will generate projections all the way down to components of pairs.
@[simps obj map] def associator : ((C × D) × E) ⥤ (C × (D × E)) :=
{ obj := λ X, (X.1.1, (X.1.2, X.2)),
  map := λ _ _ f, (f.1.1, (f.1.2, f.2)) }

@[simps obj map] def inverse_associator : (C × (D × E)) ⥤ ((C × D) × E) :=
{ obj := λ X, ((X.1, X.2.1), X.2.2),
  map := λ _ _ f, ((f.1, f.2.1), f.2.2) }

def associativity : (C × D) × E ≌ C × (D × E) :=
equivalence.mk (associator C D E) (inverse_associator C D E)
  (nat_iso.of_components (λ X, eq_to_iso (by simp)) (by tidy))
  (nat_iso.of_components (λ X, eq_to_iso (by simp)) (by tidy))

instance associator_is_equivalence : is_equivalence (associator C D E) :=
(by apply_instance : is_equivalence (associativity C D E).functor)

instance inverse_associator_is_equivalence : is_equivalence (inverse_associator C D E) :=
(by apply_instance : is_equivalence (associativity C D E).inverse)

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end category_theory.prod
