/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.presheafed_space

noncomputable theory

namespace algebraic_geometry
open topological_space category_theory opposite
open category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]
/--
Closed immersion between presheafed spaces.
-/
class PresheafedSpace.is_closed_immersion {X Y : PresheafedSpace C} (f : X ⟶ Y) :=
(base_closed : closed_embedding f.base)
(continuous_inverse : continuous $ set.range_splitting f.base)
(c_epi : epi f.c)

def PresheafedSpace.is_closed_immersion.homeomorph {X Y : PresheafedSpace C} (f : X ⟶ Y)
  [hf: PresheafedSpace.is_closed_immersion f] :
  X ≃ₜ set.range f.base :=
{ to_fun := set.range_factorization f.base,
  inv_fun := set.range_splitting f.base,
  left_inv := set.right_inverse_range_splitting hf.base_closed.inj,
  right_inv := set.left_inverse_range_splitting f,
  continuous_to_fun := by simp only [set.range_factorization]; continuity,
  continuous_inv_fun := hf.continuous_inverse }

end algebraic_geometry
