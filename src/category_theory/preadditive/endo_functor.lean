/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/

import category_theory.preadditive.default
import category_theory.endofunctor.algebra
import category_theory.preadditive.additive_functor

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive categories and `F` is an additive endofunctor on `C` then `algebra F` is
also preadditive.
-/

universes v₁ u₁ -- morphism levels before object levels. See note [category_theory universes].

namespace category_theory
variables (C : Type u₁) [category.{v₁} C] [preadditive C] (F : C ⥤ C)
  [functor.additive (F : C ⥤ C)]

open category_theory.limits preadditive

/-- The category of algebras over an additive endofunctor on a preadditive category is preadditive.
-/
@[simps]
instance endofunctor.algebra_preadditive : preadditive (endofunctor.algebra F) :=
{ hom_group := λ A₁ A₂, { add := λ α β,
    { f := α.f + β.f,
      h' := by simp only [functor.map_add, add_comp, endofunctor.algebra.hom.h, comp_add] },
    zero :=
    { f := 0,
      h' := by simp only [functor.map_zero, zero_comp, comp_zero] },
    neg := λ α,
    { f := -α.f,
      h' := by simp only [functor.map_neg, neg_comp, endofunctor.algebra.hom.h, comp_neg] },
    sub := λ α β,
    { f := α.f - β.f,
      h' := by simp only [functor.map_sub, sub_comp, endofunctor.algebra.hom.h, comp_sub] },
    add_assoc := by { intros, ext, apply add_assoc },
    zero_add := by { intros, ext, apply zero_add },
    add_zero := by { intros, ext, apply add_zero },
    sub_eq_add_neg := by { intros, ext, apply sub_eq_add_neg },
    add_left_neg := by { intros, ext, apply add_left_neg },
    add_comm := by { intros, ext, apply add_comm } },
  add_comp' := by { intros, ext, apply add_comp },
  comp_add' := by { intros, ext, apply comp_add } }

instance forget_additive : (endofunctor.algebra.forget F).additive := {}

end category_theory
