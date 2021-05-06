/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.arrow
import category_theory.over
import category_theory.limits.punit
import category_theory.limits.preserves.basic
import category_theory.limits.creates

/-!
# Limits and colimits in comma categories

We build limits in the comma category `comma L R` provided that the two source categories have
limits and `R` preserves them.
This is used to construct limits in the arrow category, structured arrow category and under
category, and show that the appropriate forgetful functors create limits.

The duals of all the above are also given.
-/

namespace category_theory
open category limits

universes v u₁ u₂ u₃

variables {J : Type v} [small_category J]
variables {A : Type u₁} [category.{v} A]
variables {B : Type u₂} [category.{v} B]
variables {T : Type u₃} [category.{v} T]

namespace comma

variables {L : A ⥤ T} {R : B ⥤ T}

variables (F : J ⥤ comma L R)

@[simps]
def limit_auxiliary_cone (c₁ : cone (F ⋙ fst L R)) :
  cone ((F ⋙ snd L R) ⋙ R) :=
(cones.postcompose (whisker_left F (comma.nat_trans L R) : _)).obj (L.map_cone c₁)

@[simps]
def cone_of_preserves [preserves_limit (F ⋙ snd L R) R]
  (c₁ : cone (F ⋙ fst L R)) {c₂ : cone (F ⋙ snd L R)} (t₂ : is_limit c₂) :
  cone F :=
{ X :=
  { left := c₁.X,
    right := c₂.X,
    hom := (is_limit_of_preserves R t₂).lift (limit_auxiliary_cone _ c₁) },
  π :=
  { app := λ j,
    { left := c₁.π.app j,
      right := c₂.π.app j,
      w' := ((is_limit_of_preserves R t₂).fac (limit_auxiliary_cone F c₁) j).symm },
    naturality' := λ j₁ j₂ t, by ext; dsimp; simp [←c₁.w t, ←c₂.w t] } }

def cone_of_preserves_is_limit [preserves_limit (F ⋙ snd L R) R]
  {c₁ : cone (F ⋙ fst L R)} (t₁ : is_limit c₁)
  {c₂ : cone (F ⋙ snd L R)} (t₂ : is_limit c₂) :
  is_limit (cone_of_preserves F c₁ t₂) :=
{ lift := λ s,
  { left := t₁.lift ((fst L R).map_cone s),
    right := t₂.lift ((snd L R).map_cone s),
    w' := (is_limit_of_preserves R t₂).hom_ext $ λ j,
    begin
      rw [cone_of_preserves_X_hom, assoc, assoc, (is_limit_of_preserves R t₂).fac,
        limit_auxiliary_cone_π_app, ←L.map_comp_assoc, t₁.fac, R.map_cone_π_app, ←R.map_comp,
        t₂.fac],
      exact (s.π.app j).w,
    end },
  uniq' := λ s m w, comma_morphism.ext _ _
      (t₁.uniq ((fst L R).map_cone s) _ (λ j, by simp [←w]))
      (t₂.uniq ((snd L R).map_cone s) _ (λ j, by simp [←w])) }

@[simps]
def limit_auxiliary_cocone (c₂ : cocone (F ⋙ snd L R)) :
  cocone ((F ⋙ fst L R) ⋙ L) :=
(cocones.precompose (whisker_left F (comma.nat_trans L R) : _)).obj (R.map_cocone c₂)

@[simps]
def cocone_of_preserves [preserves_colimit (F ⋙ fst L R) L]
  {c₁ : cocone (F ⋙ fst L R)} (t₁ : is_colimit c₁) (c₂ : cocone (F ⋙ snd L R))  :
  cocone F :=
{ X :=
  { left := c₁.X,
    right := c₂.X,
    hom := (is_colimit_of_preserves L t₁).desc (limit_auxiliary_cocone _ c₂) },
  ι :=
  { app := λ j,
    { left := c₁.ι.app j,
      right := c₂.ι.app j,
      w' := ((is_colimit_of_preserves L t₁).fac (limit_auxiliary_cocone _ c₂) j) },
    naturality' := λ j₁ j₂ t, by ext; dsimp; simp [←c₁.w t, ←c₂.w t] } }

def cocone_of_preserves_is_colimit [preserves_colimit (F ⋙ fst L R) L]
  {c₁ : cocone (F ⋙ fst L R)} (t₁ : is_colimit c₁)
  {c₂ : cocone (F ⋙ snd L R)} (t₂ : is_colimit c₂) :
  is_colimit (cocone_of_preserves F t₁ c₂) :=
{ desc := λ s,
  { left := t₁.desc ((fst L R).map_cocone s),
    right := t₂.desc ((snd L R).map_cocone s),
    w' := (is_colimit_of_preserves L t₁).hom_ext $ λ j,
    begin
      rw [cocone_of_preserves_X_hom, (is_colimit_of_preserves L t₁).fac_assoc,
        limit_auxiliary_cocone_ι_app, assoc, ←R.map_comp, t₂.fac, L.map_cocone_ι_app,
        ←L.map_comp_assoc, t₁.fac],
      exact (s.ι.app j).w,
    end },
  uniq' := λ s m w, comma_morphism.ext _ _
      (t₁.uniq ((fst L R).map_cocone s) _ (by simp [←w]))
      (t₂.uniq ((snd L R).map_cocone s) _ (by simp [←w])) }

instance has_limit (F : J ⥤ comma L R)
  [has_limit (F ⋙ fst L R)] [has_limit (F ⋙ snd L R)]
  [preserves_limit (F ⋙ snd L R) R] :
  has_limit F :=
has_limit.mk ⟨_, cone_of_preserves_is_limit _ (limit.is_limit _) (limit.is_limit _)⟩

instance has_limits_of_shape
  [has_limits_of_shape J A] [has_limits_of_shape J B] [preserves_limits_of_shape J R] :
  has_limits_of_shape J (comma L R) := {}

instance has_limits [has_limits A] [has_limits B] [preserves_limits R] :
  has_limits (comma L R) := {}

instance has_colimit (F : J ⥤ comma L R)
  [has_colimit (F ⋙ fst L R)] [has_colimit (F ⋙ snd L R)]
  [preserves_colimit (F ⋙ fst L R) L] :
  has_colimit F :=
has_colimit.mk ⟨_, cocone_of_preserves_is_colimit _ (colimit.is_colimit _) (colimit.is_colimit _)⟩

instance has_colimits_of_shape
  [has_colimits_of_shape J A] [has_colimits_of_shape J B] [preserves_colimits_of_shape J L] :
  has_colimits_of_shape J (comma L R) := {}

instance has_colimits [has_colimits A] [has_colimits B] [preserves_colimits L] :
  has_colimits (comma L R) := {}

end comma

namespace arrow

instance has_limit (F : J ⥤ arrow T)
  [has_limit (F ⋙ comma.fst (𝟭 T) (𝟭 T))] [has_limit (F ⋙ comma.snd (𝟭 T) (𝟭 T))] :
  has_limit F :=
comma.has_limit _

instance has_limits_of_shape [has_limits_of_shape J T] : has_limits_of_shape J (arrow T) := {}
instance has_limits [has_limits T] : has_limits (arrow T) := {}

end arrow

namespace structured_arrow

variables {X : T} {G : A ⥤ T} (F : J ⥤ structured_arrow X G)

instance has_limits_of_shape [has_limits_of_shape J A] [preserves_limits_of_shape J G] :
  has_limits_of_shape J (structured_arrow X G) := {}

instance has_limits [has_limits A] [preserves_limits G] :
  has_limits (structured_arrow X G) := {}

noncomputable instance creates_limit [preserves_limit (F ⋙ proj X G) G] :
  creates_limit F (proj X G) :=
creates_limit_of_reflects_iso $ λ c t,
{ lifted_cone := comma.cone_of_preserves _ punit_cone t,
  makes_limit := comma.cone_of_preserves_is_limit _ punit_cone_is_limit _,
  valid_lift := cones.ext (iso.refl _) $ λ j, (category.id_comp _).symm }

noncomputable instance creates_limits_of_shape [preserves_limits_of_shape J G] :
  creates_limits_of_shape J (structured_arrow.proj X G) :=
{}

noncomputable instance creates_limits [preserves_limits G] :
  creates_limits (structured_arrow.proj X G : _) :=
{}

end structured_arrow

namespace under

variables {X : T}

instance [has_limits_of_shape J T] : has_limits_of_shape J (under X) := {}
instance [has_limits T] : has_limits (under X) := {}

end under

namespace costructured_arrow

variables {G : A ⥤ T} {X : T} (F : J ⥤ costructured_arrow G X)

instance has_colimit [i₁ : has_colimit (F ⋙ proj G X)] [i₂ : preserves_colimit (F ⋙ proj G X) G] :
  has_colimit F :=
@@comma.has_colimit _ _ _ _ _ i₁ _ i₂

instance has_colimits_of_shape [has_colimits_of_shape J A] [preserves_colimits_of_shape J G] :
  has_colimits_of_shape J (costructured_arrow G X) :=
{}

instance has_colimits [has_colimits A] [preserves_colimits G] :
  has_colimits (costructured_arrow G X) :=
{}

noncomputable instance creates_colimit [preserves_colimit (F ⋙ proj G X) G] :
  creates_colimit F (proj G X) :=
creates_colimit_of_reflects_iso $ λ c t,
{ lifted_cocone := comma.cocone_of_preserves _ t punit_cocone,
  makes_colimit := comma.cocone_of_preserves_is_colimit _ _ punit_cocone_is_colimit,
  valid_lift := cocones.ext (iso.refl _) $ λ j, category.comp_id _ }

noncomputable instance creates_colimits_of_shape [preserves_colimits_of_shape J G] :
  creates_colimits_of_shape J (proj G X) :=
{}

noncomputable instance creates_colimits [preserves_colimits G] :
  creates_colimits (proj G X : _) :=
{}

end costructured_arrow

namespace over

variables {X : T}

instance [has_colimits_of_shape J T] : has_colimits_of_shape J (over X) := {}
instance [has_colimits T] : has_colimits (over X) := {}

end over

end category_theory
