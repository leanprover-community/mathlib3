/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Bhavik Mehta
-/
import category_theory.limits.limits

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C → D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/

open category_theory

namespace category_theory.limits

universes v u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]

variables {J : Type v} [small_category J] {K : J ⥤ C}

class preserves_limit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(preserves : Π {c : cone K}, is_limit c → is_limit (F.map_cone c))
class preserves_colimit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(preserves : Π {c : cocone K}, is_colimit c → is_colimit (F.map_cocone c))

/-- A functor which preserves limits preserves chosen limits up to isomorphism. -/
def preserves_limit_iso (K : J ⥤ C) [has_limit K] (F : C ⥤ D) [has_limit (K ⋙ F)] [preserves_limit K F] :
  F.obj (limit K) ≅ limit (K ⋙ F) :=
is_limit.cone_point_unique_up_to_iso (preserves_limit.preserves (limit.is_limit K)) (limit.is_limit (K ⋙ F))
/-- A functor which preserves colimits preserves chosen colimits up to isomorphism. -/
def preserves_colimit_iso (K : J ⥤ C) [has_colimit K] (F : C ⥤ D) [has_colimit (K ⋙ F)] [preserves_colimit K F] :
  F.obj (colimit K) ≅ colimit (K ⋙ F) :=
is_colimit.cocone_point_unique_up_to_iso (preserves_colimit.preserves (colimit.is_colimit K)) (colimit.is_colimit (K ⋙ F))

class preserves_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(preserves_limit : Π {K : J ⥤ C}, preserves_limit K F)
class preserves_colimits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(preserves_colimit : Π {K : J ⥤ C}, preserves_colimit K F)

class preserves_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(preserves_limits_of_shape : Π {J : Type v} [𝒥 : small_category J], by exactI preserves_limits_of_shape J F)
class preserves_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(preserves_colimits_of_shape : Π {J : Type v} [𝒥 : small_category J], by exactI preserves_colimits_of_shape J F)

attribute [instance, priority 100] -- see Note [lower instance priority]
  preserves_limits_of_shape.preserves_limit preserves_limits.preserves_limits_of_shape
  preserves_colimits_of_shape.preserves_colimit preserves_colimits.preserves_colimits_of_shape

instance preserves_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (preserves_limit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr
instance preserves_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (preserves_colimit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr

instance preserves_limits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (preserves_limits_of_shape J F) :=
by { split, intros, cases a, cases b, congr }
instance preserves_colimits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (preserves_colimits_of_shape J F) :=
by { split, intros, cases a, cases b, congr }

instance preserves_limits_subsingleton (F : C ⥤ D) : subsingleton (preserves_limits F) :=
by { split, intros, cases a, cases b, cc }
instance preserves_colimits_subsingleton (F : C ⥤ D) : subsingleton (preserves_colimits F) :=
by { split, intros, cases a, cases b, cc }

instance id_preserves_limits : preserves_limits (𝟭 C) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ K, by exactI ⟨λ c h,
  ⟨λ s, h.lift ⟨s.X, λ j, s.π.app j, λ j j' f, s.π.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩ } }

instance id_preserves_colimits : preserves_colimits (𝟭 C) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ K, by exactI ⟨λ c h,
  ⟨λ s, h.desc ⟨s.X, λ j, s.ι.app j, λ j j' f, s.ι.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩ } }

section
variables {E : Type u₃} [ℰ : category.{v} E]
variables (F : C ⥤ D) (G : D ⥤ E)

local attribute [elab_simple] preserves_limit.preserves preserves_colimit.preserves

instance comp_preserves_limit [preserves_limit K F] [preserves_limit (K ⋙ F) G] :
  preserves_limit K (F ⋙ G) :=
⟨λ c h, preserves_limit.preserves (preserves_limit.preserves h)⟩

instance comp_preserves_colimit [preserves_colimit K F] [preserves_colimit (K ⋙ F) G] :
  preserves_colimit K (F ⋙ G) :=
⟨λ c h, preserves_colimit.preserves (preserves_colimit.preserves h)⟩

end

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
def preserves_limit_of_preserves_limit_cone {F : C ⥤ D} {t : cone K}
  (h : is_limit t) (hF : is_limit (F.map_cone t)) : preserves_limit K F :=
⟨λ t' h', is_limit.of_iso_limit hF (functor.map_iso _ (is_limit.unique_up_to_iso h h'))⟩

/-- Transfer preservation of limits along a natural isomorphism in the shape. -/
def preserves_limit_of_iso {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [preserves_limit K₁ F] :
  preserves_limit K₂ F :=
{ preserves := λ c t,
  begin
    have t' := is_limit.of_right_adjoint (cones.postcompose_equivalence h).inverse t,
    let hF := iso_whisker_right h F,
    have := is_limit.of_right_adjoint (cones.postcompose_equivalence hF).functor
              (preserves_limit.preserves t'),
    apply is_limit.of_iso_limit this,
    refine cones.ext (iso.refl _) (λ j, _),
    dsimp,
    rw [← F.map_comp],
    simp,
  end }

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
def preserves_colimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : cocone K}
  (h : is_colimit t) (hF : is_colimit (F.map_cocone t)) : preserves_colimit K F :=
⟨λ t' h', is_colimit.of_iso_colimit hF (functor.map_iso _ (is_colimit.unique_up_to_iso h h'))⟩

/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
def preserves_colimit_of_iso {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [preserves_colimit K₁ F] :
  preserves_colimit K₂ F :=
{ preserves := λ c t,
  begin
    have t' := is_colimit.of_cocone_equiv (cocones.precompose_equivalence h).functor t,
    let hF := iso_whisker_right h F,
    have := is_colimit.of_cocone_equiv (cocones.precompose_equivalence hF).inverse
              (preserves_colimit.preserves t'),
    apply is_colimit.of_iso_colimit this,
    refine cocones.ext (iso.refl _) (λ j, _),
    dsimp,
    rw [← F.map_comp],
    simp,
  end }

/-
A functor F : C → D reflects limits if whenever the image of a cone
under F is a limit cone in D, the cone was already a limit cone in C.
Note that again we do not assume a priori that D actually has any
limits.
-/

class reflects_limit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(reflects : Π {c : cone K}, is_limit (F.map_cone c) → is_limit c)
class reflects_colimit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(reflects : Π {c : cocone K}, is_colimit (F.map_cocone c) → is_colimit c)

class reflects_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(reflects_limit : Π {K : J ⥤ C}, reflects_limit K F)
class reflects_colimits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(reflects_colimit : Π {K : J ⥤ C}, reflects_colimit K F)

class reflects_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(reflects_limits_of_shape : Π {J : Type v} {𝒥 : small_category J}, by exactI reflects_limits_of_shape J F)
class reflects_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(reflects_colimits_of_shape : Π {J : Type v} {𝒥 : small_category J}, by exactI reflects_colimits_of_shape J F)

instance reflects_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (reflects_limit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr
instance reflects_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (reflects_colimit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr

instance reflects_limits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (reflects_limits_of_shape J F) :=
by { split, intros, cases a, cases b, congr }
instance reflects_colimits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (reflects_colimits_of_shape J F) :=
by { split, intros, cases a, cases b, congr }

instance reflects_limits_subsingleton (F : C ⥤ D) : subsingleton (reflects_limits F) :=
by { split, intros, cases a, cases b, cc }
instance reflects_colimits_subsingleton (F : C ⥤ D) : subsingleton (reflects_colimits F) :=
by { split, intros, cases a, cases b, cc }

@[priority 100] -- see Note [lower instance priority]
instance reflects_limit_of_reflects_limits_of_shape (K : J ⥤ C) (F : C ⥤ D)
  [H : reflects_limits_of_shape J F] : reflects_limit K F :=
reflects_limits_of_shape.reflects_limit
@[priority 100] -- see Note [lower instance priority]
instance reflects_colimit_of_reflects_colimits_of_shape (K : J ⥤ C) (F : C ⥤ D)
  [H : reflects_colimits_of_shape J F] : reflects_colimit K F :=
reflects_colimits_of_shape.reflects_colimit

@[priority 100] -- see Note [lower instance priority]
instance reflects_limits_of_shape_of_reflects_limits (F : C ⥤ D)
  [H : reflects_limits F] : reflects_limits_of_shape J F :=
reflects_limits.reflects_limits_of_shape
@[priority 100] -- see Note [lower instance priority]
instance reflects_colimits_of_shape_of_reflects_colimits (F : C ⥤ D)
  [H : reflects_colimits F] : reflects_colimits_of_shape J F :=
reflects_colimits.reflects_colimits_of_shape

instance id_reflects_limits : reflects_limits (𝟭 C) :=
{ reflects_limits_of_shape := λ J 𝒥,
  { reflects_limit := λ K, by exactI ⟨λ c h,
  ⟨λ s, h.lift ⟨s.X, λ j, s.π.app j, λ j j' f, s.π.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩ } }

instance id_reflects_colimits : reflects_colimits (𝟭 C) :=
{ reflects_colimits_of_shape := λ J 𝒥,
  { reflects_colimit := λ K, by exactI ⟨λ c h,
  ⟨λ s, h.desc ⟨s.X, λ j, s.ι.app j, λ j j' f, s.ι.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩ } }

section
variables {E : Type u₃} [ℰ : category.{v} E]
variables (F : C ⥤ D) (G : D ⥤ E)

instance comp_reflects_limit [reflects_limit K F] [reflects_limit (K ⋙ F) G] :
  reflects_limit K (F ⋙ G) :=
⟨λ c h, reflects_limit.reflects (reflects_limit.reflects h)⟩

instance comp_reflects_colimit [reflects_colimit K F] [reflects_colimit (K ⋙ F) G] :
  reflects_colimit K (F ⋙ G) :=
⟨λ c h, reflects_colimit.reflects (reflects_colimit.reflects h)⟩

end

variable (F : C ⥤ D)

/-- A fully faithful functor reflects limits. -/
def fully_faithful_reflects_limits [full F] [faithful F] : reflects_limits F :=
{ reflects_limits_of_shape := λ J 𝒥₁, by exactI
  { reflects_limit := λ K,
    { reflects := λ c t,
      is_limit.mk_cone_morphism (λ s, (cones.functoriality K F).preimage (t.lift_cone_morphism _)) $
      begin
        apply (λ s m, (cones.functoriality K F).map_injective _),
        rw [functor.image_preimage],
        apply t.uniq_cone_morphism,
      end } } }

/-- A fully faithful functor reflects colimits. -/
def fully_faithful_reflects_colimits [full F] [faithful F] : reflects_colimits F :=
{ reflects_colimits_of_shape := λ J 𝒥₁, by exactI
  { reflects_colimit := λ K,
    { reflects := λ c t,
      is_colimit.mk_cocone_morphism (λ s, (cocones.functoriality K F).preimage (t.desc_cocone_morphism _)) $
      begin
        apply (λ s m, (cocones.functoriality K F).map_injective _),
        rw [functor.image_preimage],
        apply t.uniq_cocone_morphism,
      end } } }

end category_theory.limits
