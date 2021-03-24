/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.default
import category_theory.single_obj

/-!
# `single_obj α` is preadditive when `α` is a ring.

-/

universes v u

namespace category_theory

variables {α : Type*} [ring α]

instance : preadditive (single_obj α) :=
{ hom_group := λ _ _, by { change add_comm_group α, apply_instance, },
  add_comp' := λ _ _ _ f f' g, mul_add g f f',
  comp_add' := λ _ _ _ f g g', add_mul g g' f, }

-- TODO once we have preadditive functors, define PreAdditiveCat, and `Ring ⥤ PreAdditiveCat`.

end category_theory
