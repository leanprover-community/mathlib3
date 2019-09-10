/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import topology.topological_space.category.basic
import category_theory.adjunction.basic

universe u

open category_theory
open Top

namespace Top

def adj₁ : discrete ⊣ forget :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, f,
    inv_fun := λ f, ⟨f, continuous_bot⟩,
    left_inv := by tidy,
    right_inv := by tidy },
  unit := { app := λ X, id },
  counit := { app := λ X, ⟨id, continuous_bot⟩ } }

def adj₂ : forget ⊣ trivial :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f, continuous_top⟩,
    inv_fun := λ f, f,
    left_inv := by tidy,
    right_inv := by tidy },
  unit := { app := λ X, ⟨id, continuous_top⟩ },
  counit := { app := λ X, id } }

end Top
