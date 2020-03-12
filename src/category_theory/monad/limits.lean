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

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞
variables {T : C ⥤ C} [monad.{v₁} T]

variables {J : Type v₁} [𝒥 : small_category J]
include 𝒥

namespace forget_creates_limits
variables (D : J ⥤ algebra T) [has_limit.{v₁} (D ⋙ forget T)]

@[simps] def γ : (D ⋙ forget T ⋙ T) ⟶ (D ⋙ forget T) := { app := λ j, (D.obj j).a }

@[simps] def c : cone (D ⋙ forget T) :=
{ X := T.obj (limit (D ⋙ forget T)),
  π := (functor.const_comp _ _ T).inv ≫ whisker_right (limit.cone (D ⋙ forget T)).π T ≫ (γ D) }

@[simps] def cone_point (D : J ⥤ algebra T) [has_limit.{v₁} (D ⋙ forget T)] : algebra T :=
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
    simp only [limit.lift_π, γ_app, c_π, limit.cone_π, functor.const_comp, whisker_right_app,
                nat_trans.comp_app, category.assoc],
    dsimp,
    simp only [id_comp],
    conv { to_rhs,
      rw [←category.assoc, ←T.map_comp, limit.lift_π],
      dsimp [c],
      rw [id_comp], },
    conv { to_lhs,
      rw [←category.assoc, ←nat_trans.naturality, category.assoc],
      erw [algebra.assoc (D.obj j), ←category.assoc, ←T.map_comp], },
  end }

end forget_creates_limits

-- Theorem 5.6.5 from [Riehl][riehl2017]
def forget_creates_limits (D : J ⥤ algebra T) [has_limit (D ⋙ forget T)] : has_limit D :=
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
                    whisker_right_app, nat_trans.comp_app, category.assoc, functor.map_cone_π],
        dsimp,
        rw [id_comp, ←category.assoc, ←T.map_comp],
        simp only [limit.lift_π, monad.forget_map, algebra.hom.h, functor.map_cone_π],
      end },
    uniq' := λ s m w, by { ext1, ext1, simpa using congr_arg algebra.hom.f (w j) } } }

@[simps] def γ (D : J ⥤ algebra T) [has_colimit.{v₁} (D ⋙ forget T)] :
  ((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T) := { app := λ j, (D.obj j).a }

@[simps]
def c (D : J ⥤ algebra T) [has_colimit.{v₁} (D ⋙ forget T)] : cocone ((D ⋙ forget T) ⋙ T) :=
{ X := colimit (D ⋙ forget T),
  ι := γ D ≫ (colimit.cocone (D ⋙ forget T)).ι }

@[reducible]
def lambda [preserves_colimits_of_shape J T] (D : J ⥤ algebra T) [has_colimit.{v₁} (D ⋙ forget T)] :=
(preserves_colimit.preserves T (colimit.is_colimit (D ⋙ forget T))).desc (c D)

lemma commuting
  [preserves_colimits_of_shape J T] (D : J ⥤ algebra T) [has_colimit.{v₁} (D ⋙ forget T)] (j : J) :
T.map (colimit.ι (D ⋙ forget T) j) ≫ lambda D = (D.obj j).a ≫ colimit.ι (D ⋙ forget T) j :=
is_colimit.fac (preserves_colimit.preserves T (colimit.is_colimit (D ⋙ forget T))) (c D) j

@[simps] def cocone_point
  [preserves_colimits_of_shape J T] (D : J ⥤ algebra T) [has_colimit.{v₁} (D ⋙ forget T)] :
algebra T :=
{ A := colimit (D ⋙ forget T),
  a := lambda D,
  unit' :=
  begin
    ext1,
    rw comp_id,
    rw ← category.assoc,
    erw nat_trans.naturality' (η_ T),
    rw category.assoc,
    erw commuting,
    erw ← category.assoc,
    erw algebra.unit,
    apply id_comp
  end,
  assoc' :=
  begin
    apply is_colimit.hom_ext (preserves_colimit.preserves T (preserves_colimit.preserves T (colimit.is_colimit (D ⋙ forget T)))),
    intro j,
    rw ← category.assoc,
    erw nat_trans.naturality (μ_ T),
    rw ← functor.map_cocone_ι,
    erw category.assoc,
    rw is_colimit.fac _ (c D) j,
    rw ← category.assoc,
    erw ← functor.map_comp,
    rw is_colimit.fac _ (c D) j,
    rw ← functor.map_cocone_ι,
    dsimp,
    rw ← category.assoc, rw algebra.assoc, rw category.assoc,
    rw functor.map_comp,
    rw category.assoc,
    erw is_colimit.fac (preserves_colimit.preserves T (colimit.is_colimit (D ⋙ forget T))) (c D) j,
    refl
  end
}

def forget_creates_colimits_of_monad_preserves
  [preserves_colimits_of_shape J T] (D : J ⥤ algebra T) [has_colimit (D ⋙ forget T)] :
has_colimit D :=
{ cocone :=
  { X := cocone_point D,
    ι :=
    { app := λ j, { f := colimit.ι (D ⋙ forget T) j,
                    h' := commuting _ _ },
      naturality' := λ A B f, by { ext1, dsimp, erw [comp_id, colimit.w (D ⋙ forget T)] } } },
  is_colimit :=
  { desc := λ s,
    { f := colimit.desc _ ((forget T).map_cocone s),
      h' :=
      begin
        dsimp,
        apply is_colimit.hom_ext (preserves_colimit.preserves T (colimit.is_colimit (D ⋙ forget T))),
        intro j,
        rw ← category.assoc, erw ← functor.map_comp,
        erw colimit.ι_desc,
        rw ← category.assoc, erw commuting,
        rw category.assoc, rw colimit.ι_desc,
        apply algebra.hom.h
      end },
    uniq' := λ s m J, by { ext1, ext1, simpa using congr_arg algebra.hom.f (J j) }
  }
}

end monad

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₁} [𝒟 : category.{v₁} D]
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
