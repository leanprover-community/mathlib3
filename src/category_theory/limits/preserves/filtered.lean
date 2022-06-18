/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import category_theory.limits.preserves.basic
import category_theory.filtered

/-!
# Preservation of filtered colimits and cofiltered limits.
Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits). See e.g. `algebra/category/Mon/filtered_colimits`.

## Future work
This could be generalised to allow diagrams in lower universes.
-/

open category_theory
open category_theory.functor

namespace category_theory.limits

universes v u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables {E : Type u₃} [category.{v} E]

variables {J : Type v} [small_category J] {K : J ⥤ C}

/--
A functor is said to preserve filtered colimits, if it preserves all colimits of shape `J`, where
`J` is a filtered category.
-/
class preserves_filtered_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(preserves_filtered_colimits : Π (J : Type v) [small_category J] [is_filtered J],
  preserves_colimits_of_shape J F)

attribute [instance, priority 100] preserves_filtered_colimits.preserves_filtered_colimits

@[priority 100]
instance preserves_colimits.preserves_filtered_colimits (F : C ⥤ D) [preserves_colimits F] :
  preserves_filtered_colimits F :=
{ preserves_filtered_colimits := infer_instance }

instance comp_preserves_filtered_colimits (F : C ⥤ D) (G : D ⥤ E)
  [preserves_filtered_colimits F] [preserves_filtered_colimits G] :
  preserves_filtered_colimits (F ⋙ G) :=
{ preserves_filtered_colimits := λ J _ _, by exactI infer_instance }

/--
A functor is said to preserve cofiltered limits, if it preserves all limits of shape `J`, where
`J` is a cofiltered category.
-/
class preserves_cofiltered_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(preserves_cofiltered_limits : Π (J : Type v) [small_category J] [is_cofiltered J],
  preserves_limits_of_shape J F)

attribute [instance, priority 100] preserves_cofiltered_limits.preserves_cofiltered_limits

@[priority 100]
instance preserves_limits.preserves_cofiltered_limits (F : C ⥤ D) [preserves_limits F] :
  preserves_cofiltered_limits F :=
{ preserves_cofiltered_limits := infer_instance }

instance comp_preserves_cofiltered_limits (F : C ⥤ D) (G : D ⥤ E)
  [preserves_cofiltered_limits F] [preserves_cofiltered_limits G] :
  preserves_cofiltered_limits (F ⋙ G) :=
{ preserves_cofiltered_limits := λ J _ _, by exactI infer_instance }


end category_theory.limits
