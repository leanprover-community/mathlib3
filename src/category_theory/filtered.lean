/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import category_theory.category
import order.bounded_lattice

/-!
# Filtered categories

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

Filtered colimits are often better behaved than arbitrary colimits.
See `category_theory/limits/types` for some details.

(We'll prove existence of cocones for finite diagrams in a subsequent PR.)

## Future work
* Finite limits commute with filtered colimits
* Forgetful functors for algebraic categories typically preserve filtered colimits.
-/

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

variables (C : Type u) [category.{v} C]

/--
A category `is_filtered_or_empty` if
1. for every pair of objects there exists another object "to the right", and
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal.
-/
class is_filtered_or_empty : Prop :=
(cocone_objs : ∀ (X Y : C), ∃ Z (f : X ⟶ Z) (g : Y ⟶ Z), true)
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ Z (h : Y ⟶ Z), f ≫ h = g ≫ h)


section prio
set_option default_priority 100 -- see Note [default priority]

/--
A category `is_filtered` if
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.
-/
class is_filtered extends is_filtered_or_empty C : Prop :=
[nonempty : nonempty C]

end prio

@[priority 100]
instance is_filtered_or_empty_of_semilattice_sup
  (α : Type u) [semilattice_sup α] : is_filtered_or_empty α :=
{ cocone_objs := λ X Y, ⟨X ⊔ Y, hom_of_le le_sup_left, hom_of_le le_sup_right, trivial⟩,
  cocone_maps := λ X Y f g, ⟨Y, 𝟙 _, (by ext)⟩, }

@[priority 100]
instance is_filtered_of_semilattice_sup_top
  (α : Type u) [semilattice_sup_top α] : is_filtered α :=
{ nonempty := ⟨⊤⟩,
  ..category_theory.is_filtered_or_empty_of_semilattice_sup α }

end category_theory
