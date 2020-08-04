/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import algebra.category.Group.limits

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

open category_theory
open category_theory.limits

universes u v

namespace Module

variables {R : Type u} [ring R]
variables {J : Type v} [small_category J]

instance add_comm_group_obj (F : J ⥤ Module.{v} R) (j) :
  add_comm_group ((F ⋙ forget (Module R)).obj j) :=
by { change add_comm_group (F.obj j), apply_instance }

instance module_obj (F : J ⥤ Module.{v} R) (j) :
  module R ((F ⋙ forget (Module R)).obj j) :=
by { change module R (F.obj j), apply_instance }

/--
The flat sections of a functor into `Module R` form a submodule of all sections.
-/
def sections_submodule (F : J ⥤ Module R) :
  submodule R (Π j, F.obj j) :=
{ carrier := (F ⋙ forget (Module R)).sections,
  smul_mem' := λ r s sh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, pi.smul_apply, linear_map.map_smul],
    dsimp [functor.sections] at sh,
    rw sh f,
  end,
  ..(AddGroup.sections_add_subgroup (F ⋙ forget₂ (Module R) AddCommGroup.{v} ⋙ forget₂ AddCommGroup AddGroup.{v})) }

instance limit_add_comm_group (F : J ⥤ Module R) :
  add_comm_group (limit (F ⋙ forget (Module.{v} R))) :=
begin
  change add_comm_group (sections_submodule F),
  apply_instance,
end

instance limit_module (F : J ⥤ Module R) :
  module R (limit (F ⋙ forget (Module.{v} R))) :=
begin
  change module R (sections_submodule F),
  apply_instance,
end

/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limit_π_linear_map (F : J ⥤ Module R) (j) :
  limit (F ⋙ forget (Module.{v} R)) →ₗ[R] (F ⋙ forget (Module R)).obj j :=
{ to_fun := limit.π (F ⋙ forget (Module R)) j,
  map_smul' := λ x y, by { simp only [types.types_limit_π], refl },
  map_add' := λ x y, by { simp only [types.types_limit_π], refl } }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits (Module R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Module R`.
(Internal use only; use the limits API.)
-/
def limit (F : J ⥤ Module R) : cone F :=
{ X := Module.of R (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_linear_map F,
    naturality' := λ j j' f,
      linear_map.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Module R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_is_limit (F : J ⥤ Module R) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful
    (forget (Module R)) (limit.is_limit _)
    (λ s, ⟨_, _, _⟩) (λ s, rfl); tidy
end

end has_limits

open has_limits

/-- The category of R-modules has all limits. -/
instance has_limits : has_limits (Module.{v} R) :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI
    { cone     := limit F,
      is_limit := limit_is_limit F } } }

/--
The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂_AddCommGroup_preserves_limits : preserves_limits (forget₂ (Module R) AddCommGroup.{v}) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget₂ (Module R) AddCommGroup)) } }

/--
The forgetful functor from R-modules to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget (Module R)) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end Module
