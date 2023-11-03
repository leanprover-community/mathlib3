/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import algebraic_geometry.presheafed_space
import algebraic_geometry.sheafed_space
import algebraic_geometry.locally_ringed_space
import algebraic_geometry.Scheme
import algebraic_geometry.pullbacks

/-!
# Closed Immersion

This files defines closed immersions in the category of (pre)sheafed spaces, locally ringed spaces
and schemes.
-/


noncomputable theory

namespace algebraic_geometry
open topological_space category_theory opposite
open category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

/--
Closed immersion between presheafed spaces are morphisms `f : X ⟶ Y`, such that
* the underlying continuous map is a closed embedding;
* `𝓞_Y ⟶ f_* 𝓞_X` is surjective
-/
class PresheafedSpace.is_closed_immersion [concrete_category C] [has_colimits C]
  {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop :=
(base_closed : closed_embedding f.base)
(c_surj : ∀ y : Y, function.surjective $ (forget C).map
  ((Top.presheaf.stalk_functor _ $ y).map f.c))

instance PresheafedSpace.is_closed_immersion.id [concrete_category C] [has_colimits C]
  {X : PresheafedSpace C} :
  PresheafedSpace.is_closed_immersion (𝟙 X) :=
{ base_closed := closed_embedding_id,
  c_surj := λ x, begin
    change function.surjective
      ((forget C).map ((Top.presheaf.stalk_functor _ x).map (PresheafedSpace.id _).c)),
    dunfold PresheafedSpace.id,
    rw eq_to_hom_map,
    generalize_proofs h1 h2,
    intros y,
    use (forget C).map (eq_to_hom h2.symm) y,
    change ((forget C).map _ ≫ (forget C).map _) _ = y,
    rw [←(forget C).map_comp, eq_to_hom_trans, eq_to_hom_refl, (forget C).map_id],
    refl,
  end }
/--
A morphism of sheafed spaces is a closed immersion iff it is a closed immersion as a morphism of
presheafed spaces.
-/
abbreviation SheafedSpace.is_closed_immersion [concrete_category C] [has_colimits C]
  [has_products C]
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
