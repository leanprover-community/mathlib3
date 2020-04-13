/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott MorrisoE
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
/-- The forgetful functor from the Eilenberg-Moore category creates limits. -/
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

namespace forget_creates_colimits
-- Let's hide the implementation details in a namespace
variables (D : J ⥤ algebra T)
-- We have a diagram D of shape J in the category of algebras, and we assume that its image
-- D ⋙ forget T under the forgetful functor has a colimit (written L).

-- We'll construct a colimiting coalgebra for D, whose carrier will also be L.
-- To do this, we must find a map TL ⟶ L. Since T preserves colimits, TL is also a colimit.
-- In particular, it is a colimit for the diagram `(D ⋙ forget T) ⋙ T`
-- so to construct a map TL ⟶ L it suffices to show that L is the apex of a cocone for this diagram.
-- In other words, we need a natural transformation from const L to `(D ⋙ forget T) ⋙ T`.
-- But we already know that L is the apex of a cocone for the diagram `D ⋙ forget T`, so it
-- suffices to give a natural transformation `((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T)`:

/--
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
apex `colimit (D ⋙ forget T)`.
 -/
@[simps] def γ : ((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T) := { app := λ j, (D.obj j).a }

variable [has_colimit.{v₁} (D ⋙ forget T)]
/--
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simps]
def c : cocone ((D ⋙ forget T) ⋙ T) :=
{ X := colimit (D ⋙ forget T),
  ι := γ D ≫ (colimit.cocone (D ⋙ forget T)).ι }

variable [preserves_colimits_of_shape J T]

/--
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and the fact that
`T` preserves colimits to produce this morphism.
-/
@[reducible]
def lambda : (functor.map_cocone T (colimit.cocone (D ⋙ forget T))).X ⟶ colimit (D ⋙ forget T) :=
(preserves_colimit.preserves (colimit.is_colimit (D ⋙ forget T))).desc (c D)

/-- The key property defining the map `λ : TL ⟶ L`. -/
lemma commuting (j : J) :
T.map (colimit.ι (D ⋙ forget T) j) ≫ lambda D = (D.obj j).a ≫ colimit.ι (D ⋙ forget T) j :=
is_colimit.fac (preserves_colimit.preserves (colimit.is_colimit (D ⋙ forget T))) (c D) j

/--
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We are required to
show it satisfies the two algebra laws, which follow from the algebra laws for the image of `D` and
our `commuting` lemma.
-/
@[simps] def cocone_point :
algebra T :=
{ A := colimit (D ⋙ forget T),
  a := lambda D,
  unit' :=
  begin
    ext1,
    erw [comp_id, ← category.assoc, (η_ T).naturality, category.assoc, commuting, ← category.assoc],
    erw algebra.unit, apply id_comp
  end,
  assoc' :=
  begin
    apply is_colimit.hom_ext (preserves_colimit.preserves (preserves_colimit.preserves (colimit.is_colimit (D ⋙ forget T)))),
    intro j,
    erw [← category.assoc, nat_trans.naturality (μ_ T), ← functor.map_cocone_ι, category.assoc,
         is_colimit.fac _ (c D) j],
    rw ← category.assoc,
    erw [← functor.map_comp, commuting],
    dsimp,
    erw [← category.assoc, algebra.assoc, category.assoc, functor.map_comp, category.assoc, commuting],
    apply_instance, apply_instance
  end
}

end forget_creates_colimits

-- TODO: the converse of this is true as well
-- TODO: generalise to monadic functors, as for creating limits
/--
The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.

The colimiting algebra itself has been constructed in `cocone_point`. We now must show it
actually forms a cocone, and that this is colimiting.
-/
def forget_creates_colimits_of_monad_preserves
  [preserves_colimits_of_shape J T] (D : J ⥤ algebra T) [has_colimit (D ⋙ forget T)] :
has_colimit D :=
{ cocone :=
  { X := forget_creates_colimits.cocone_point D,
    ι :=
    { app := λ j, { f := colimit.ι (D ⋙ forget T) j,
                    h' := forget_creates_colimits.commuting _ _ },
      naturality' := λ A B f, by { ext1, dsimp, erw [comp_id, colimit.w (D ⋙ forget T)] } } },
  is_colimit :=
  { desc := λ s,
    { f := colimit.desc _ ((forget T).map_cocone s),
      h' :=
      begin
        dsimp,
        apply is_colimit.hom_ext (preserves_colimit.preserves (colimit.is_colimit (D ⋙ forget T))),
        intro j,
        rw ← category.assoc, erw ← functor.map_comp,
        erw colimit.ι_desc,
        rw ← category.assoc, erw forget_creates_colimits.commuting,
        rw category.assoc, rw colimit.ι_desc,
        apply algebra.hom.h,
        apply_instance
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

/-- Any monadic functor creates limits. -/
def monadic_creates_limits (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit.{v₁} (F ⋙ R)] :
  has_limit F :=
adjunction.has_limit_of_comp_equivalence _ (monad.comparison R)

omit 𝒥

section

def has_limits_of_reflective (R : D ⥤ C) [has_limits.{v₁} C] [reflective R] : has_limits.{v₁} D :=
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
