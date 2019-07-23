/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import category_theory.monad.basic
import category_theory.types

/-!

# Convert from `monad` (i.e. Lean's `Type`-based monads) to `category_theory.monad`

This allows us to use these monadss in category theory.

-/

namespace category_theory

section
universes u

variables (m : Type u → Type u) [_root_.monad m] [is_lawful_monad m]

instance : monad (of_type_functor m) :=
{ η           := ⟨@pure m _, assume α β f, (is_lawful_applicative.map_comp_pure m f).symm ⟩,
  μ           := ⟨@mjoin m _, assume α β (f : α → β), funext $ assume a, mjoin_map_map f a ⟩,
  assoc'      := assume α, funext $ assume a, mjoin_map_mjoin a,
  left_unit'  := assume α, funext $ assume a, mjoin_pure a,
  right_unit' := assume α, funext $ assume a, mjoin_map_pure a }

end

end category_theory
