/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import algebraic_topology.simplicial_object
import category_theory.limits.shapes.wide_pullbacks
import category_theory.arrow

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve assocaited to an arrow, provided
the base category has the correct wide pullbacks.

Several variables are provided, given `f : arrow C`:
1. `f.cech_nerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmented_cech_nerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `simplicial_object.cech_nerve` and `simplicial_object.augmented_cech_nerve` are
  functorial versions of 1 resp. 2.

-/

open category_theory
open category_theory.limits

noncomputable theory

universes v u

variables {C : Type u} [category.{v} C]

namespace category_theory.arrow

variables (f : arrow C)
variables [∀ n : ℕ, has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The Čech nerve associated to an arrow. -/
@[simps]
def cech_nerve : simplicial_object C :=
{ obj := λ n, wide_pullback f.right
    (λ i : ulift (fin (n.unop.len + 1)), f.left) (λ i, f.hom),
  map := λ m n g, wide_pullback.lift wide_pullback.base
    (λ i, wide_pullback.π $ ulift.up $ g.unop.to_preorder_hom i.down) (by tidy) }

/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
def augmented_cech_nerve : simplicial_object.augmented C :=
{ left := f.cech_nerve,
  right := f.right,
  hom := { app := λ i, wide_pullback.base } }

end category_theory.arrow

namespace simplicial_object

variables [∀ (n : ℕ) (f : arrow C),
  has_wide_pullback f.right (λ i : ulift (fin (n+1)), f.left) (λ i, f.hom)]

/-- The Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def cech_nerve : arrow C ⥤ simplicial_object C :=
{ obj := λ f, f.cech_nerve,
  map := λ f g F,
  { app := λ n, wide_pullback.lift (wide_pullback.base ≫ F.right)
      (λ i, wide_pullback.π i ≫ F.left) (λ i, by simp [← category.assoc]) },
  -- tidy needs a bit of help here...
  map_id' := by { intros i, ext, tidy },
  map_comp' := begin
    intros f g h F G,
    ext,
    all_goals {
      dsimp,
      simp only [category.assoc, limits.wide_pullback.lift_base,
        limits.wide_pullback.lift_π, limits.limit.lift_π_assoc],
      simpa only [← category.assoc] },
  end }

/-- The augmented Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def augmented_cech_nerve : arrow C ⥤ simplicial_object.augmented C :=
{ obj := λ f, f.augmented_cech_nerve,
  map := λ f g F,
  { left := cech_nerve.map F,
    right := F.right } }

end simplicial_object
