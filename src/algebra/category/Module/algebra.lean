/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.restrict_scalars
import category_theory.linear.basic
import algebra.category.Module.basic

/-!
# Additional typeclass for modules over an algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For an object in `M : Module A`, where `A` is a `k`-algebra,
we provide additional typeclasses on the underlying type `M`,
namely `module k M` and `is_scalar_tower k A M`.
These are not made into instances by default.

We provide the `linear k (Module A)` instance.

## Note

If you begin with a `[module k M] [module A M] [is_scalar_tower k A M]`,
and build a bundled module via `Module.of A M`,
these instances will not necessarily agree with the original ones.

It seems without making a parallel version `Module' k A`, for modules over a `k`-algebra `A`,
that carries these typeclasses, this seems hard to achieve.
(An alternative would be to always require these typeclasses, and remove the original `Module`,
requiring users to write `Module' ℤ A` when `A` is merely a ring.)
-/

universes v u w
open category_theory

namespace Module

variables {k : Type u} [field k]
variables {A : Type w} [ring A] [algebra k A]

/--
Type synonym for considering a module over a `k`-algebra as a `k`-module.
-/
def module_of_algebra_Module (M : Module.{v} A) : module k M :=
restrict_scalars.module k A M

localized "attribute [instance] Module.module_of_algebra_Module" in Module

lemma is_scalar_tower_of_algebra_Module (M : Module.{v} A) : is_scalar_tower k A M :=
restrict_scalars.is_scalar_tower k A M

localized "attribute [instance] Module.is_scalar_tower_of_algebra_Module" in Module

-- We verify that the morphism spaces become `k`-modules.
example (M N : Module.{v} A) : module k (M ⟶ N) := by apply_instance

instance linear_over_field : linear k (Module.{v} A) :=
{ hom_module := λ M N, by apply_instance, }

end Module
