-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Mario Carneiro

import category_theory.instances.Top.basic
import category_theory.adjunction.basic

universe u

open category_theory
open category_theory.instances

namespace category_theory.instances.Top

def adj₁ : discrete ⊣ forget :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, f,
    inv_fun := λ f, ⟨f, continuous_top⟩,
    left_inv := by tidy,
    right_inv := by tidy },
  unit := { app := λ X, id },
  counit := { app := λ X, ⟨id, continuous_top⟩ } }

def adj₂ : forget ⊣ trivial :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f, continuous_bot⟩,
    inv_fun := λ f, f,
    left_inv := by tidy,
    right_inv := by tidy },
  unit := { app := λ X, ⟨id, continuous_bot⟩ },
  counit := { app := λ X, id } }

end category_theory.instances.Top
