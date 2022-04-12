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

namespace category_theory

variables {α : Type*} [ring α]

instance : preadditive (single_obj α) :=
{ add_comp' := λ _ _ _ f f' g, mul_add g f f',
  comp_add' := λ _ _ _ f g g', add_mul g g' f, }

-- TODO define `PreAddCat` (with additive functors as morphisms), and `Ring ⥤ PreAddCat`.

end category_theory
