/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.creates

/-!
# Limits in full subcategories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the notion of a property closed under taking limits and show that if `P` is closed
under taking limits, then limits in `full_subcategory P` can be constructed from limits in `C`.
More precisely, the inclusion creates such limits.

-/

noncomputable theory

universes w' w v u

open category_theory

namespace category_theory.limits

/-- We say that a property is closed under limits of shape `J` if whenever all objects in a
    `J`-shaped diagram have the property, any limit of this diagram also has the property. -/
def closed_under_limits_of_shape {C : Type u} [category.{v} C] (J : Type w) [category.{w'} J]
  (P : C → Prop) : Prop :=
∀ ⦃F : J ⥤ C⦄ ⦃c : cone F⦄ (hc : is_limit c), (∀ j, P (F.obj j)) → P c.X

/-- We say that a property is closed under colimits of shape `J` if whenever all objects in a
    `J`-shaped diagram have the property, any colimit of this diagram also has the property. -/
def closed_under_colimits_of_shape {C : Type u} [category.{v} C] (J : Type w) [category.{w'} J]
  (P : C → Prop) : Prop :=
∀ ⦃F : J ⥤ C⦄ ⦃c : cocone F⦄ (hc : is_colimit c), (∀ j, P (F.obj j)) → P c.X

section
variables {C : Type u} [category.{v} C] {J : Type w} [category.{w'} J] {P : C → Prop}

lemma closed_under_limits_of_shape.limit (h : closed_under_limits_of_shape J P) {F : J ⥤ C}
  [has_limit F] : (∀ j, P (F.obj j)) → P (limit F) :=
h (limit.is_limit _)

lemma closed_under_colimits_of_shape.colimit (h : closed_under_colimits_of_shape J P) {F : J ⥤ C}
  [has_colimit F] : (∀ j, P (F.obj j)) → P (colimit F) :=
h (colimit.is_colimit _)

end

section
variables {J : Type w} [category.{w'} J] {C : Type u} [category.{v} C] {P : C → Prop}

/-- If a `J`-shaped diagram in `full_subcategory P` has a limit cone in `C` whose cone point lives
    in the full subcategory, then this defines a limit in the full subcategory. -/
def creates_limit_full_subcategory_inclusion' (F : J ⥤ full_subcategory P)
  {c : cone (F ⋙ full_subcategory_inclusion P)} (hc : is_limit c) (h : P c.X) :
  creates_limit F (full_subcategory_inclusion P) :=
creates_limit_of_fully_faithful_of_iso' hc ⟨_, h⟩ (iso.refl _)

/-- If a `J`-shaped diagram in `full_subcategory P` has a limit in `C` whose cone point lives in the
    full subcategory, then this defines a limit in the full subcategory. -/
def creates_limit_full_subcategory_inclusion (F : J ⥤ full_subcategory P)
  [has_limit (F ⋙ full_subcategory_inclusion P)]
  (h : P (limit (F ⋙ full_subcategory_inclusion P))) :
  creates_limit F (full_subcategory_inclusion P) :=
creates_limit_full_subcategory_inclusion' F (limit.is_limit _) h

/-- If a `J`-shaped diagram in `full_subcategory P` has a colimit cocone in `C` whose cocone point
    lives in the full subcategory, then this defines a colimit in the full subcategory. -/
def creates_colimit_full_subcategory_inclusion' (F : J ⥤ full_subcategory P)
  {c : cocone (F ⋙ full_subcategory_inclusion P)} (hc : is_colimit c) (h : P c.X) :
  creates_colimit F (full_subcategory_inclusion P) :=
creates_colimit_of_fully_faithful_of_iso' hc ⟨_, h⟩ (iso.refl _)

/-- If a `J`-shaped diagram in `full_subcategory P` has a colimit in `C` whose cocone point lives in
    the full subcategory, then this defines a colimit in the full subcategory. -/
def creates_colimit_full_subcategory_inclusion (F : J ⥤ full_subcategory P)
  [has_colimit (F ⋙ full_subcategory_inclusion P)]
  (h : P (colimit (F ⋙ full_subcategory_inclusion P))) :
  creates_colimit F (full_subcategory_inclusion P) :=
creates_colimit_full_subcategory_inclusion' F (colimit.is_colimit _) h

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def creates_limit_full_subcategory_inclusion_of_closed (h : closed_under_limits_of_shape J P)
  (F : J ⥤ full_subcategory P) [has_limit (F ⋙ full_subcategory_inclusion P)] :
  creates_limit F (full_subcategory_inclusion P) :=
creates_limit_full_subcategory_inclusion F (h.limit (λ j, (F.obj j).property))

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def creates_limits_of_shape_full_subcategory_inclusion (h : closed_under_limits_of_shape J P)
  [has_limits_of_shape J C] : creates_limits_of_shape J (full_subcategory_inclusion P) :=
{ creates_limit := λ F, creates_limit_full_subcategory_inclusion_of_closed h F }

lemma has_limit_of_closed_under_limits (h : closed_under_limits_of_shape J P)
  (F : J ⥤ full_subcategory P) [has_limit (F ⋙ full_subcategory_inclusion P)] : has_limit F :=
have creates_limit F (full_subcategory_inclusion P),
  from creates_limit_full_subcategory_inclusion_of_closed h F,
by exactI has_limit_of_created F (full_subcategory_inclusion P)

lemma has_limits_of_shape_of_closed_under_limits (h : closed_under_limits_of_shape J P)
  [has_limits_of_shape J C] : has_limits_of_shape J (full_subcategory P) :=
{ has_limit := λ F, has_limit_of_closed_under_limits h F }

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def creates_colimit_full_subcategory_inclusion_of_closed (h : closed_under_colimits_of_shape J P)
  (F : J ⥤ full_subcategory P) [has_colimit (F ⋙ full_subcategory_inclusion P)] :
  creates_colimit F (full_subcategory_inclusion P) :=
creates_colimit_full_subcategory_inclusion F (h.colimit (λ j, (F.obj j).property))

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def creates_colimits_of_shape_full_subcategory_inclusion
  (h : closed_under_colimits_of_shape J P) [has_colimits_of_shape J C] :
  creates_colimits_of_shape J (full_subcategory_inclusion P) :=
{ creates_colimit := λ F, creates_colimit_full_subcategory_inclusion_of_closed h F }

lemma has_colimit_of_closed_under_colimits (h : closed_under_colimits_of_shape J P)
  (F : J ⥤ full_subcategory P) [has_colimit (F ⋙ full_subcategory_inclusion P)] : has_colimit F :=
have creates_colimit F (full_subcategory_inclusion P),
  from creates_colimit_full_subcategory_inclusion_of_closed h F,
by exactI has_colimit_of_created F (full_subcategory_inclusion P)

lemma has_colimits_of_shape_of_closed_under_colimits (h : closed_under_colimits_of_shape J P)
  [has_colimits_of_shape J C] : has_colimits_of_shape J (full_subcategory P) :=
{ has_colimit := λ F, has_colimit_of_closed_under_colimits h F }

end

end category_theory.limits
