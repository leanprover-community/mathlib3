/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import algebra.algebra.restrict_scalars

/-!
# Additional typeclass for modules over an algebra

For an object in `M : Module A`, where `A` is a `k`-algebra,
we provide additional typeclasses on the underlying type `M`,
namely `module k M` and `is_scalar_tower k A M`.

## Note

If you begin with a `[module k M] [module A M] [is_scalar_tower k A M]`,
and build a bundled module via `Module.of A M`,
these instances will not necessarily agree with the original ones.

It seems without making a parallel version `Module' k A`, for modules over a `k`-algebra `A`,
that carries these typeclasses, this seems hard to achieve.
(An alternative would be to always require these typeclasses,
requiring users to write `Module' ℤ A` when `A` is merely a ring.)
-/

namespace Module

variables {k : Type*} [field k]
variables {A : Type*} [ring A] [algebra k A]

instance (M : Module A) : module k M :=
by { change module k (restrict_scalars k A M), apply_instance, }

instance (M : Module A) : is_scalar_tower k A M :=
by { change is_scalar_tower k A (restrict_scalars k A M), apply_instance, }

-- We verify that the morphism spaces become `k`-modules.
example (M N : Module A) : module k (M ⟶ N) := by apply_instance

end Module
