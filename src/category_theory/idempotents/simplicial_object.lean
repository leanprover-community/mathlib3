/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_object
import category_theory.idempotents.functor_categories

/-!

# Idempotent completeness of categories of simplicial objects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we provide an instance expressing that `simplicial_object C`
and `cosimplicial_object C` are idempotent complete categories when the
category `C` is.

-/

namespace category_theory

namespace idempotents

variables {C : Type*} [category C] [is_idempotent_complete C]

instance : is_idempotent_complete (simplicial_object C) :=
idempotents.functor_category_is_idempotent_complete _ _

instance : is_idempotent_complete (cosimplicial_object C) :=
idempotents.functor_category_is_idempotent_complete _ _

end idempotents

end category_theory
