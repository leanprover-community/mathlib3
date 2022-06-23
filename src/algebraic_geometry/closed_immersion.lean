/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.presheafed_space
import algebraic_geometry.sheafed_space
import algebraic_geometry.locally_ringed_space
import algebraic_geometry.Scheme
import algebraic_geometry.pullbacks

noncomputable theory

namespace algebraic_geometry
open topological_space category_theory opposite
open category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

/--
Closed immersion between presheafed spaces.
-/
class PresheafedSpace.is_closed_immersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop :=
(base_closed : closed_embedding f.base)
(continuous_inverse : continuous $ set.range_splitting f.base)
(c_epi : epi f.c)

/--
If `f : X ⟶ Y` is a closed immersion between presheafed spaces, then `X` as a topological space is
homeomorphic to the range of `f` endowed with the subspace topology.
-/
def PresheafedSpace.is_closed_immersion.homeomorph {X Y : PresheafedSpace C} (f : X ⟶ Y)
  [hf: PresheafedSpace.is_closed_immersion f] :
  X ≃ₜ set.range f.base :=
{ to_fun := set.range_factorization f.base,
  inv_fun := set.range_splitting f.base,
  left_inv := set.right_inverse_range_splitting hf.base_closed.inj,
  right_inv := set.left_inverse_range_splitting f,
  continuous_to_fun := by simp only [set.range_factorization]; continuity,
  continuous_inv_fun := hf.continuous_inverse }

instance PresheafedSpace.is_closed_immersion.id {X : PresheafedSpace C} :
  PresheafedSpace.is_closed_immersion (𝟙 X) :=
{ base_closed := closed_embedding_id,
  continuous_inverse := (⟨λ s os, begin
    rw is_open_induced_iff,
    refine ⟨s, os, _⟩,
    ext x,
    split;
    intros hx;
    rw [set.mem_preimage] at hx ⊢,
    { have := set.apply_range_splitting (𝟙 (X : Top.{v})) x,
      simp only [Top.id_app] at this,
      rwa this },
    { have := set.apply_range_splitting (𝟙 (X : Top.{v})) x,
      simp only [Top.id_app] at this,
      rwa this at hx, },
  end⟩ : continuous (set.range_splitting $ 𝟙 (X : Top.{v}))),
  c_epi := infer_instance }

/--
A morphism of sheafed spaces is a closed immersion iff it is a closed immersion as a morphism of
presheafed spaces.
-/
abbreviation SheafedSpace.is_closed_immersion [has_products C]
  {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
PresheafedSpace.is_closed_immersion f

/-- A morphism of locally ringed spaces is a closed immersion iff it is a closed immersion as a
morphism between sheafed spaces.
-/
abbreviation LocallyRingedSpace.is_closed_immersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
SheafedSpace.is_closed_immersion f.1

/-- A morphism of schemes is a closed immersion iff it is a closed immersion as a morphism between
locally ringed space.
-/
abbreviation is_closed_immersion {X Y : Scheme} (f : X ⟶ Y) : Prop :=
LocallyRingedSpace.is_closed_immersion f

end algebraic_geometry
