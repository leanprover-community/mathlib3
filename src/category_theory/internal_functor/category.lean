/-
Copyright (c) 2023 Zach Murray. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zach Murray
-/
import category_theory.category.basic
import category_theory.limits.shapes.pullbacks
import category_theory.internal_category.basic
import category_theory.internal_functor.basic
import category_theory.internal_natural_transformation
open category_theory
open category_theory.limits

/-!
# The Category of Internal Functors

Defines the category of functors and natural transformations between two fixed internal categories.
-/

noncomputable theory

namespace category_theory

universes v u
variables {𝔸 : Type u} [category.{v} 𝔸]
          (𝔻 𝔼 : internal_category 𝔸)

instance internal_functor.category : category.{_} (𝔻 ⟹ 𝔼) :=
{ hom := λ F G, internal_nat_trans F G,
  id := λ F, internal_nat_trans.id F,
  comp := λ _ _ _  α β, vcomp α β }

lemma vcomp_app' {F G H : 𝔻 ⟹ 𝔼} (α : F ⟶ G) (β : G ⟶ H) :
  (α ≫ β).app = pullback.lift α.app β.app (by simp) ≫ 𝔼.c := rfl

@[simp]
lemma id_app' (F : 𝔻 ⟹ 𝔼) : 𝟙 F = internal_nat_trans.id F := rfl

end category_theory
