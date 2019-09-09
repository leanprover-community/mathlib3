/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monad.adjunction
import category_theory.adjunction.limits

namespace category_theory
open category
open category_theory.limits

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace monad

variables {C : Sort u₁} [𝒞 : category.{v₁+1} C]
include 𝒞
variables {T : C ⥤ C} [monad.{v₁+1} T]

variables {J : Type v₁} [𝒥 : small_category J]
include 𝒥

namespace forget_creates_limits
variables (D : J ⥤ algebra T) [has_limit.{v₁} (D ⋙ forget T)]

def γ : (D ⋙ forget T ⋙ T) ⟶ (D ⋙ forget T) := { app := λ j, (D.obj j).a }

@[simp] lemma γ_app (j) : (γ D).app j = (D.obj j).a := rfl

def c : cone (D ⋙ forget T) :=
{ X := T.obj (limit (D ⋙ forget T)),
  π := (functor.const_comp _ _ T).inv ≫ whisker_right (limit.cone (D ⋙ forget T)).π T ≫ (γ D) }

@[simp] lemma c_π (j) :
(c D).π.app j = 𝟙 _ ≫ T.map (limit.π (D ⋙ forget T) j) ≫ (D.obj j).a := rfl

def cone_point (D : J ⥤ algebra T) [has_limit.{v₁} (D ⋙ forget T)] : algebra T :=
{ A := limit (D ⋙ forget T),
  a := limit.lift _ (c D),
  unit' :=
  begin
    ext1,
    rw [category.assoc, limit.lift_π],
    dsimp,
    erw [id_comp, ←category.assoc, ←nat_trans.naturality,
        id_comp, category.assoc, algebra.unit, comp_id],
    refl,
  end,
  assoc' :=
  begin
    ext1,
    dsimp,
    simp only [limit.lift_π, γ_app, c_π, limit.cone_π, id_comp, functor.const_comp,
                whisker_right.app, nat_trans.comp_app, category.assoc],
    conv { to_rhs,
      rw [←category.assoc, ←T.map_comp, limit.lift_π],
      dsimp [c],
      rw [id_comp], },
    conv { to_lhs,
      rw [←category.assoc, ←nat_trans.naturality, category.assoc],
      erw [algebra.assoc (D.obj j), ←category.assoc, ←T.map_comp], },
  end }

@[simp] lemma cone_point_a (D : J ⥤ algebra T) [has_limit.{v₁} (D ⋙ forget T)] :
(cone_point D).a = limit.lift _ (
let μ := limit.cone (D ⋙ forget T) in
  { X := T.obj μ.X,
    π := (functor.const_comp _ _ T).inv ≫ whisker_right μ.π T ≫ (γ D) }) := rfl

end forget_creates_limits

-- Theorem 5.6.5 from [Riehl][riehl2017]
def forget_creates_limits (D : J ⥤ algebra T) [has_limit.{v₁} (D ⋙ forget T)] : has_limit D :=
{ cone :=
  { X := forget_creates_limits.cone_point D,
    π :=
    { app := λ j, { f := limit.π (D ⋙ forget T) j },
      naturality' := λ X Y f, by { ext, dsimp, erw [id_comp, limit.w] } } },
  is_limit :=
  { lift := λ s,
    { f := limit.lift _ ((forget T).map_cone s),
      h' :=
      begin
        ext, dsimp,
        simp only [limit.lift_π, limit.cone_π, forget_map, id_comp, functor.const_comp,
                    whisker_right.app, nat_trans.comp_app, category.assoc, functor.map_cone_π],
        dsimp,
        rw [id_comp, ←category.assoc, ←T.map_comp],
        simp only [limit.lift_π, monad.forget_map, algebra.hom.h, functor.map_cone_π],
      end },
    uniq' := λ s m w, by { ext1, ext1, simpa using congr_arg algebra.hom.f (w j) } } }

end monad

variables {C : Sort u₁} [𝒞 : category.{v₁+1} C] {D : Sort u₁} [𝒟 : category.{v₁+1} D]
include 𝒞 𝒟
variables {J : Type v₁} [𝒥 : small_category J]

include 𝒥

instance comp_comparison_forget_has_limit
  (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit.{v₁} (F ⋙ R)] :
  has_limit ((F ⋙ monad.comparison R) ⋙ monad.forget ((left_adjoint R) ⋙ R)) :=
(@has_limit_of_iso _ _ _ _ (F ⋙ R) _ _ (iso_whisker_left F (monad.comparison_forget R).symm))

instance comp_comparison_has_limit
  (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit.{v₁} (F ⋙ R)] :
  has_limit (F ⋙ monad.comparison R) :=
monad.forget_creates_limits (F ⋙ monad.comparison R)

def monadic_creates_limits (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit.{v₁} (F ⋙ R)] :
  has_limit F :=
adjunction.has_limit_of_comp_equivalence _ (monad.comparison R)

omit 𝒥

section

def has_limits_of_reflective (R : D ⥤ C) [reflective R] [has_limits.{v₁} C] : has_limits.{v₁} D :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, monadic_creates_limits F R } }

local attribute [instance] has_limits_of_reflective
include 𝒥

-- We verify that, even jumping through these monadic hoops,
-- the limit is actually calculated in the obvious way:
example (R : D ⥤ C) [reflective R] [has_limits.{v₁} C] (F : J ⥤ D) :
limit F = (left_adjoint R).obj (limit (F ⋙ R)) := rfl

end
end category_theory
