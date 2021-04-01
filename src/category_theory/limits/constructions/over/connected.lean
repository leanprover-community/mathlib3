/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.over
import category_theory.limits.connected
import category_theory.limits.creates

/-!
# Connected limits in the over category

Shows that the forgetful functor `over B ⥤ C` creates connected limits, in particular `over B` has
any connected limit which `C` has.
-/

universes v u -- morphism levels before object levels. See note [category_theory universes].

noncomputable theory

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.over

namespace creates_connected

/--
(Impl) Given a diagram in the over category, produce a natural transformation from the
diagram legs to the specific object.
-/
def nat_trans_in_over {B : C} (F : J ⥤ over B) :
  F ⋙ forget B ⟶ (category_theory.functor.const J).obj B :=
{ app := λ j, (F.obj j).hom }

local attribute [tidy] tactic.case_bash

/--
(Impl) Given a cone in the base category, raise it to a cone in the over category. Note this is
where the connected assumption is used.
-/
@[simps]
def raise_cone [is_connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget B)) :
  cone F :=
{ X := over.mk (c.π.app (classical.arbitrary J) ≫ (F.obj (classical.arbitrary J)).hom),
  π :=
  { app := λ j,
      over.hom_mk (c.π.app j) (nat_trans_from_is_connected (c.π ≫ nat_trans_in_over F) j _) } }

lemma raised_cone_lowers_to_original [is_connected J] {B : C} {F : J ⥤ over B}
  (c : cone (F ⋙ forget B)) (t : is_limit c) :
  (forget B).map_cone (raise_cone c) = c :=
by tidy

/-- (Impl) Show that the raised cone is a limit. -/
def raised_cone_is_limit [is_connected J] {B : C} {F : J ⥤ over B}
  {c : cone (F ⋙ forget B)} (t : is_limit c) :
  is_limit (raise_cone c) :=
{ lift := λ s, over.hom_mk (t.lift ((forget B).map_cone s)) (by { dsimp, simp }),
  uniq' := λ s m K, by { ext1, apply t.hom_ext, intro j, simp [← K j] } }

end creates_connected

/-- The forgetful functor from the over category creates any connected limit. -/
instance forget_creates_connected_limits
  [is_connected J] {B : C} : creates_limits_of_shape J (forget B) :=
{ creates_limit := λ K,
    creates_limit_of_reflects_iso (λ c t,
      { lifted_cone := creates_connected.raise_cone c,
        valid_lift := eq_to_iso (creates_connected.raised_cone_lowers_to_original c t),
        makes_limit := creates_connected.raised_cone_is_limit t } ) }

/-- The over category has any connected limit which the original category has. -/
instance has_connected_limits
  {B : C} [is_connected J] [has_limits_of_shape J C] : has_limits_of_shape J (over B) :=
{ has_limit := λ F, has_limit_of_created F (forget B) }

end category_theory.over
