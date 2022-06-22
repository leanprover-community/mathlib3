import algebraic_geometry.presheafed_space

noncomputable theory

namespace algebraic_geometry

open topological_space category_theory opposite
open category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

class PresheafedSpace.is_close_immersion {X Y : PresheafedSpace C} (f : X ⟶ Y) :=
(base_close : closed_embedding f.base)
(continuous_inverse : continuous $ set.range_splitting f.base)
(c_epi : ∀ U : opens X, epi f.c)

def PresheafedSpace.is_close_immersion.homeomorph {X Y : PresheafedSpace C} (f : X ⟶ Y)
  [hf: PresheafedSpace.is_close_immersion f] :
  X ≃ₜ set.range f.base :=
{ to_fun := set.range_factorization f.base,
  inv_fun := set.range_splitting f.base,
  left_inv := set.right_inverse_range_splitting hf.base_close.inj,
  right_inv := set.left_inverse_range_splitting f,
  continuous_to_fun := by simp only [set.range_factorization]; continuity,
  continuous_inv_fun := PresheafedSpace.is_close_immersion.continuous_inverse }

end algebraic_geometry
