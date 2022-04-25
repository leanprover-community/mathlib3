/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import representation_theory.Action
import algebra.category.Module.basic

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

-/

universes u

open category_theory

/-- The category of `k`-linear representations of a monoid `G`. -/
@[derive [large_category, concrete_category]]
abbreviation Rep (k G : Type u) [ring k] [monoid G] :=
Action (Module.{u} k) (Mon.of G)

namespace Rep

variables {k G : Type u} [ring k] [monoid G]

instance : has_coe_to_sort (Rep k G) (Type u) := concrete_category.has_coe_to_sort _

instance (V : Rep k G) : add_comm_monoid V :=
by { change add_comm_monoid ((forget₂ (Rep k G) (Module k)).obj V), apply_instance, }

instance (V : Rep k G) : module k V :=
by { change module k ((forget₂ (Rep k G) (Module k)).obj V), apply_instance, }

-- This works well with the new design for representations:
example (V : Rep k G) : G →* (V →ₗ[k] V) := V.ρ

/-- Lift an unbundled representation to `Rep`. -/
@[simps ρ]
def of (V : Type u) [add_comm_group V] [module k V] (ρ : G →* (V →ₗ[k] V)) : Rep k G :=
⟨Module.of k V, ρ⟩

end Rep
