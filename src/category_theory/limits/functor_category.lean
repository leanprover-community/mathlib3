/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves.basic

open category_theory category_theory.category

namespace category_theory.limits

universes v v₂ u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u} [category.{v} C]

variables {J K : Type v} [small_category J] [category.{v₂} K]

-- @[simp, reassoc] lemma cone.functor_w {F : J ⥤ (K ⥤ C)} (c : cone F) {j j' : J} (f : j ⟶ j') (k : K) :
--   (c.π.app j).app k ≫ (F.map f).app k = (c.π.app j').app k :=
-- by convert ←nat_trans.congr_app (c.π.naturality f).symm k; apply id_comp

-- @[simp, reassoc] lemma cocone.functor_w {F : J ⥤ (K ⥤ C)} (c : cocone F) {j j' : J} (f : j ⟶ j') (k : K) :
--   (F.map f).app k ≫ (c.ι.app j').app k = (c.ι.app j).app k :=
-- by convert ←nat_trans.congr_app (c.ι.naturality f) k; apply comp_id
/--
The evaluation functors jointly reflect limits: that is, to show a cone is a limit of `F`
it suffices to show that each evaluation cone is a limit. In other words, to prove a cone is
limiting you can show it's pointwise limiting.
-/
def eval_jointly_reflects {F : J ⥤ K ⥤ C} (c : cone F)
  (t : Π (k : K), is_limit (((evaluation K C).obj k).map_cone c)) : is_limit c :=
{ lift := λ s,
  { app := λ k, (t k).lift ⟨s.X.obj k, whisker_right s.π ((evaluation K C).obj k)⟩,
    naturality' :=
    begin
      intros,
      apply (t Y).hom_ext,
      intro j,
      rw [assoc, (t Y).fac _ j],
      simpa using ((t X).fac_assoc ⟨s.X.obj X, whisker_right s.π ((evaluation K C).obj X)⟩ j _).symm,
    end },
  fac' := λ s j, nat_trans.ext _ _ $ funext $ λ k, (t k).fac _ j,
  uniq' := λ s m w, nat_trans.ext _ _ $ funext $ λ x, (t x).hom_ext $ λ j,
  begin
    rw (t x).fac,
    simp [← w],
  end }

/--
Given a functor `F` and a collection of limit cones for each diagram `F (-) k`, we can stitch
them together to give a cone for the diagram `F`.
`combined_is_limit` shows that the new cone is limiting, and `eval_combined` shows it is
(essentially) made up of the original cones.
-/
@[simps] def combine_cones (F : J ⥤ K ⥤ C) (c : Π (k : K), limit_cone (F.flip.obj k)) :
  cone F :=
{ X :=
  { obj := λ k, (c k).cone.X,
    map := λ k₁ k₂ f, (c k₂).is_limit.lift ⟨_, (c k₁).cone.π ≫ F.flip.map f⟩,
    map_id' := λ k, (c k).is_limit.hom_ext (λ j, by { dsimp, simp }),
    map_comp' := λ k₁ k₂ k₃ f₁ f₂, (c k₃).is_limit.hom_ext (λ j, by simp) },
  π :=
  { app := λ j, { app := λ k, (c k).cone.π.app j },
    naturality' := λ j₁ j₂ g, nat_trans.ext _ _ $ funext $ λ k, (c k).cone.π.naturality g } }

/-- The stitched together cones each project down to the original given cones (up to iso). -/
def eval_combined (F : J ⥤ K ⥤ C) (c : Π (k : K), limit_cone (F.flip.obj k)) (k : K) :
  ((evaluation K C).obj k).map_cone (combine_cones F c) ≅ (c k).cone :=
cones.ext (iso.refl _) (by tidy)

/-- Stitching together limiting cones gives a new limiting cone. -/
def combined_is_limit (F : J ⥤ K ⥤ C) (c : Π (k : K), limit_cone (F.flip.obj k)) :
  is_limit (combine_cones F c) :=
eval_jointly_reflects _ (λ k, (c k).is_limit.of_iso_limit (eval_combined F c k).symm)

noncomputable theory

/--
Construct a cone for `F` by stitching together the limiting cones for each `k` which we know
exist from the typeclass.
-/
def functor_category_limit_cone [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) : cone F :=
combine_cones F (λ k, get_limit_cone _)

@[simps] def functor_category_colimit_cocone [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) :
  cocone F :=
{ X := F.flip ⋙ colim,
  ι :=
  { app := λ j,
    { app := λ k, colimit.ι (F.flip.obj k) j },
      naturality' := λ j j' f,
        by ext k; convert (colimit.w (F.flip.obj k) _) using 1; apply comp_id } }

@[simp] def evaluate_functor_category_limit_cone
  [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
  ((evaluation K C).obj k).map_cone (functor_category_limit_cone F) ≅
    limit.cone (F.flip.obj k) :=
eval_combined F _ k

@[simp] def evaluate_functor_category_colimit_cocone
  [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
  ((evaluation K C).obj k).map_cocone (functor_category_colimit_cocone F) ≅
    colimit.cocone (F.flip.obj k) :=
cocones.ext (iso.refl _) (by tidy)

def functor_category_is_limit_cone [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) :
  is_limit (functor_category_limit_cone F) :=
combined_is_limit _ _

def functor_category_is_colimit_cocone [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) :
  is_colimit (functor_category_colimit_cocone F) :=
{ desc := λ s,
  { app := λ k, colimit.desc (F.flip.obj k) (((evaluation K C).obj k).map_cocone s) },
  uniq' := λ s m w,
  begin
    ext1, ext1 k,
    exact is_colimit.uniq _
      (((evaluation K C).obj k).map_cocone s) (m.app k) (λ j, nat_trans.congr_app (w j) k)
  end }

instance functor_category_has_limits_of_shape
  [has_limits_of_shape J C] : has_limits_of_shape J (K ⥤ C) :=
{ has_limit := λ F, has_limit.mk
  { cone := functor_category_limit_cone F,
    is_limit := functor_category_is_limit_cone F } }

instance functor_category_has_colimits_of_shape
  [has_colimits_of_shape J C] : has_colimits_of_shape J (K ⥤ C) :=
{ has_colimit := λ F, has_colimit.mk
  { cocone := functor_category_colimit_cocone F,
    is_colimit := functor_category_is_colimit_cocone F } }

instance functor_category_has_limits [has_limits C] : has_limits (K ⥤ C) :=
{ has_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance functor_category_has_colimits [has_colimits C] : has_colimits (K ⥤ C) :=
{ has_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance evaluation_preserves_limits_of_shape [has_limits_of_shape J C] (k : K) :
  preserves_limits_of_shape J ((evaluation K C).obj k) :=
{ preserves_limit :=
  λ F, preserves_limit_of_preserves_limit_cone (functor_category_is_limit_cone _) $
    is_limit.of_iso_limit (limit.is_limit _)
      (evaluate_functor_category_limit_cone F k).symm }

instance evaluation_preserves_colimits_of_shape [has_colimits_of_shape J C] (k : K) :
  preserves_colimits_of_shape J ((evaluation K C).obj k) :=
{ preserves_colimit :=
  λ F, preserves_colimit_of_preserves_colimit_cocone (functor_category_is_colimit_cocone _) $
    is_colimit.of_iso_colimit (colimit.is_colimit _)
      (evaluate_functor_category_colimit_cocone F k).symm }

instance evaluation_preserves_limits [has_limits C] (k : K) :
  preserves_limits ((evaluation K C).obj k) :=
{ preserves_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance evaluation_preserves_colimits [has_colimits C] (k : K) :
  preserves_colimits ((evaluation K C).obj k) :=
{ preserves_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

end category_theory.limits
