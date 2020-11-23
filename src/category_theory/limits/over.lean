/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.over
import category_theory.limits.preserves.basic

noncomputable theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.functor

/-- We can interpret a functor `F` into the category of arrows with codomain `X` as a cocone over
    the diagram given by the domains of the arrows in the image of `F` such that the apex of the
    cocone is `X`. -/
@[simps] def to_cocone (F : J ⥤ over X) : cocone (F ⋙ over.forget X) :=
{ X := X,
  ι := { app := λ j, (F.obj j).hom } }

/-- We can interpret a functor `F` into the category of arrows with domain `X` as a cone over the
    diagram given by the codomains of the arrows in the image of `F` such that the apex of the cone
    is `X`. -/
@[simps] def to_cone (F : J ⥤ under X) : cone (F ⋙ under.forget X) :=
{ X := X,
  π := { app := λ j, (F.obj j).hom } }

end category_theory.functor

namespace category_theory.over

/-- A colimit of `F ⋙ over.forget` induces a cocone over `F`. This is an implementation detail,
    use the `has_colimit` instance provided below. -/
@[simps] def colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget X)] : cocone F :=
{ X := mk $ colimit.desc (F ⋙ forget X) F.to_cocone,
  ι :=
  { app := λ j, hom_mk $ colimit.ι (F ⋙ forget X) j,
    naturality' :=
    begin
      intros j j' f,
      have := colimit.w (F ⋙ forget X) f,
      tidy
    end } }

/-- The cocone constructed from the colimit of `F ⋙ forget X` is a colimit. This is an
    implementation detail, use the `has_colimit` instance provided below.  -/
def forget_colimit_is_colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget X)] :
  is_colimit ((forget X).map_cocone (colimit F)) :=
is_colimit.of_iso_colimit (colimit.is_colimit (F ⋙ forget X)) (cocones.ext (iso.refl _) (by tidy))

instance : reflects_colimits (forget X) :=
{ reflects_colimits_of_shape := λ J 𝒥,
  { reflects_colimit := λ F,
    by constructor; exactI λ t ht,
    { desc := λ s, hom_mk (ht.desc ((forget X).map_cocone s))
        begin
          apply ht.hom_ext, intro j,
          rw [←category.assoc, ht.fac],
          transitivity (F.obj j).hom,
          exact w (s.ι.app j), -- TODO: How to write (s.ι.app j).w?
          exact (w (t.ι.app j)).symm,
        end,
      fac' := begin
        intros s j, ext, exact ht.fac ((forget X).map_cocone s) j
        -- TODO: Ask Simon about multiple ext lemmas for defeq types (comma_morphism & over.category.hom)
      end,
      uniq' :=
      begin
        intros s m w,
        ext1 j,
        exact ht.uniq ((forget X).map_cocone s) m.left (λ j, congr_arg comma_morphism.left (w j))
      end } } }

instance has_colimit {F : J ⥤ over X} [has_colimit (F ⋙ forget X)] : has_colimit F :=
has_colimit.mk { cocone := colimit F,
  is_colimit := reflects_colimit.reflects (forget_colimit_is_colimit F) }

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (over X) :=
{ has_colimit := λ F, by apply_instance }

instance has_colimits [has_colimits C] : has_colimits (over X) :=
{ has_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance forget_preserves_colimit {X : C} {F : J ⥤ over X} [has_colimit (F ⋙ forget X)] :
  preserves_colimit F (forget X) :=
preserves_colimit_of_preserves_colimit_cocone
  (reflects_colimit.reflects (forget_colimit_is_colimit F)) (forget_colimit_is_colimit F)

instance forget_preserves_colimits_of_shape [has_colimits_of_shape J C] {X : C} :
  preserves_colimits_of_shape J (forget X) :=
{ preserves_colimit := λ F, by apply_instance }

instance forget_preserves_colimits [has_colimits C] {X : C} :
  preserves_colimits (forget X) :=
{ preserves_colimits_of_shape := λ J 𝒥, by apply_instance }

end category_theory.over

namespace category_theory.under

/-- A limit of `F ⋙ under.forget` induces a cone over `F`. This is an implementation detail,
    use the `has_limit` instance provided below. -/
@[simps] def limit (F : J ⥤ under X) [has_limit (F ⋙ forget X)] : cone F :=
{ X := mk $ limit.lift (F ⋙ forget X) F.to_cone,
  π :=
  { app := λ j, hom_mk $ limit.π (F ⋙ forget X) j,
    naturality' :=
    begin
      intros j j' f,
      have := (limit.w (F ⋙ forget X) f).symm,
      tidy
    end } }

/-- The cone constructed from the limit of `F ⋙ forget X` is a limit. This is an
    implementation detail, use the `has_limit` instance provided below.  -/
def forget_limit_is_limit (F : J ⥤ under X) [has_limit (F ⋙ forget X)] :
  is_limit ((forget X).map_cone (limit F)) :=
is_limit.of_iso_limit (limit.is_limit (F ⋙ forget X)) (cones.ext (iso.refl _) (by tidy))

instance : reflects_limits (forget X) :=
{ reflects_limits_of_shape := λ J 𝒥,
  { reflects_limit := λ F,
    by constructor; exactI λ t ht,
    { lift := λ s, hom_mk (ht.lift ((forget X).map_cone s))
        begin
          apply ht.hom_ext, intro j,
          rw [category.assoc, ht.fac],
          transitivity (F.obj j).hom,
          exact w (s.π.app j),
          exact (w (t.π.app j)).symm,
        end,
      fac' := begin
        intros s j, ext, exact ht.fac ((forget X).map_cone s) j
      end,
      uniq' :=
      begin
        intros s m w,
        ext1 j,
        exact ht.uniq ((forget X).map_cone s) m.right (λ j, congr_arg comma_morphism.right (w j))
      end } } }

instance has_limit {F : J ⥤ under X} [has_limit (F ⋙ forget X)] : has_limit F :=
has_limit.mk { cone := limit F,
  is_limit := reflects_limit.reflects (forget_limit_is_limit F) }

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (under X) :=
{ has_limit := λ F, by apply_instance }

instance has_limits [has_limits C] : has_limits (under X) :=
{ has_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance forget_preserves_limits [has_limits C] {X : C} :
  preserves_limits (forget X) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by exactI
    preserves_limit_of_preserves_limit_cone
      (reflects_limit.reflects (forget_limit_is_limit F)) (forget_limit_is_limit F) } }

end category_theory.under
