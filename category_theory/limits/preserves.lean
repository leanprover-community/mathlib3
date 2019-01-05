-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton

-- Preservation and reflection of (co)limits.

import category_theory.whiskering
import category_theory.limits.limits

open category_theory

namespace category_theory.limits

universes v u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v} C]
variables {D : Type u₂} [𝒟 : category.{v} D]
include 𝒞 𝒟

variables {J : Type v} [small_category J] {K : J ⥤ C}

/- Note on "preservation of (co)limits"

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

class preserves_limit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(preserves : Π {c : cone K}, is_limit c → is_limit (F.map_cone c))
class preserves_colimit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(preserves : Π {c : cocone K}, is_colimit c → is_colimit (F.map_cocone c))

@[class] def preserves_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
Π {K : J ⥤ C}, preserves_limit K F
@[class] def preserves_colimits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
Π {K : J ⥤ C}, preserves_colimit K F

@[class] def preserves_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
Π {J : Type v} {𝒥 : small_category J}, by exactI preserves_limits_of_shape J F
@[class] def preserves_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
Π {J : Type v} {𝒥 : small_category J}, by exactI preserves_colimits_of_shape J F

instance preserves_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (preserves_limit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr
instance preserves_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (preserves_colimit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr

instance preserves_limits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (preserves_limits_of_shape J F) :=
by split; intros; funext; apply subsingleton.elim
instance preserves_colimits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (preserves_colimits_of_shape J F) :=
by split; intros; funext; apply subsingleton.elim

instance preserves_limits_subsingleton (F : C ⥤ D) : subsingleton (preserves_limits F) :=
by split; intros; funext; resetI; apply subsingleton.elim
instance preserves_colimits_subsingleton (F : C ⥤ D) : subsingleton (preserves_colimits F) :=
by split; intros; funext; resetI; apply subsingleton.elim

instance preserves_limit_of_preserves_limits_of_shape (F : C ⥤ D)
  [H : preserves_limits_of_shape J F] : preserves_limit K F :=
H
instance preserves_colimit_of_preserves_colimits_of_shape (F : C ⥤ D)
  [H : preserves_colimits_of_shape J F] : preserves_colimit K F :=
H

instance preserves_limits_of_shape_of_preserves_limits (F : C ⥤ D)
  [H : preserves_limits F] : preserves_limits_of_shape J F :=
@H J _
instance preserves_colimits_of_shape_of_preserves_colimits (F : C ⥤ D)
  [H : preserves_colimits F] : preserves_colimits_of_shape J F :=
@H J _

instance id_preserves_limits : preserves_limits (functor.id C) :=
λ J 𝒥 K, by exactI ⟨λ c h,
  ⟨λ s, h.lift ⟨s.X, λ j, s.π.app j, λ j j' f, s.π.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩

instance id_preserves_colimits : preserves_colimits (functor.id C) :=
λ J 𝒥 K, by exactI ⟨λ c h,
  ⟨λ s, h.desc ⟨s.X, λ j, s.ι.app j, λ j j' f, s.ι.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩

section
variables {E : Type u₃} [ℰ : category.{v} E]
variables (F : C ⥤ D) (G : D ⥤ E)

local attribute [elab_simple] preserves_limit.preserves preserves_colimit.preserves

instance comp_preserves_limit [preserves_limit K F] [preserves_limit (K ⋙ F) G] :
  preserves_limit K (F ⋙ G) :=
⟨λ c h, preserves_limit.preserves G (preserves_limit.preserves F h)⟩

instance comp_preserves_colimit [preserves_colimit K F] [preserves_colimit (K ⋙ F) G] :
  preserves_colimit K (F ⋙ G) :=
⟨λ c h, preserves_colimit.preserves G (preserves_colimit.preserves F h)⟩

end

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
def preserves_limit_of_preserves_limit_cone {F : C ⥤ D} {t : cone K}
  (h : is_limit t) (hF : is_limit (F.map_cone t)) : preserves_limit K F :=
⟨λ t' h', is_limit.of_iso_limit hF (functor.on_iso _ (is_limit.unique h h'))⟩

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
def preserves_colimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : cocone K}
  (h : is_colimit t) (hF : is_colimit (F.map_cocone t)) : preserves_colimit K F :=
⟨λ t' h', is_colimit.of_iso_colimit hF (functor.on_iso _ (is_colimit.unique h h'))⟩

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

@[class] def reflects_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
Π {K : J ⥤ C}, reflects_limit K F
@[class] def reflects_colimits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
Π {K : J ⥤ C}, reflects_colimit K F

@[class] def reflects_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
Π {J : Type v} {𝒥 : small_category J}, by exactI reflects_limits_of_shape J F
@[class] def reflects_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
Π {J : Type v} {𝒥 : small_category J}, by exactI reflects_colimits_of_shape J F

instance reflects_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (reflects_limit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr
instance reflects_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : subsingleton (reflects_colimit K F) :=
by split; rintros ⟨a⟩ ⟨b⟩; congr

instance reflects_limits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (reflects_limits_of_shape J F) :=
by split; intros; funext; apply subsingleton.elim
instance reflects_colimits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  subsingleton (reflects_colimits_of_shape J F) :=
by split; intros; funext; apply subsingleton.elim

instance reflects_limits_subsingleton (F : C ⥤ D) : subsingleton (reflects_limits F) :=
by split; intros; funext; resetI; apply subsingleton.elim
instance reflects_colimits_subsingleton (F : C ⥤ D) : subsingleton (reflects_colimits F) :=
by split; intros; funext; resetI; apply subsingleton.elim

instance reflects_limit_of_reflects_limits_of_shape (K : J ⥤ C) (F : C ⥤ D)
  [H : reflects_limits_of_shape J F] : reflects_limit K F :=
H
instance reflects_colimit_of_reflects_colimits_of_shape (K : J ⥤ C) (F : C ⥤ D)
  [H : reflects_colimits_of_shape J F] : reflects_colimit K F :=
H

instance reflects_limits_of_shape_of_reflects_limits (F : C ⥤ D)
  [H : reflects_limits F] : reflects_limits_of_shape J F :=
@H J _
instance reflects_colimits_of_shape_of_reflects_colimits (F : C ⥤ D)
  [H : reflects_colimits F] : reflects_colimits_of_shape J F :=
@H J _

instance id_reflects_limits : reflects_limits (functor.id C) :=
λ J 𝒥 K, by exactI ⟨λ c h,
  ⟨λ s, h.lift ⟨s.X, λ j, s.π.app j, λ j j' f, s.π.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩

instance id_reflects_colimits : reflects_colimits (functor.id C) :=
λ J 𝒥 K, by exactI ⟨λ c h,
  ⟨λ s, h.desc ⟨s.X, λ j, s.ι.app j, λ j j' f, s.ι.naturality f⟩,
   by cases K; rcases c with ⟨_, _, _⟩; intros s j; cases s; exact h.fac _ j,
   by cases K; rcases c with ⟨_, _, _⟩; intros s m w; rcases s with ⟨_, _, _⟩; exact h.uniq _ m w⟩⟩

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

end category_theory.limits
