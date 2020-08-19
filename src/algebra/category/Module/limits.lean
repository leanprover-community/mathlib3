/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import algebra.category.Group.limits
import data.equiv.transfer_instance

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace Module

variables {R : Type u} [ring R]
variables {J : Type u} [small_category J]

instance add_comm_group_obj (F : J ⥤ Module R) (j) :
  add_comm_group ((F ⋙ forget (Module R)).obj j) :=
by { change add_comm_group (F.obj j), apply_instance }

instance module_obj (F : J ⥤ Module R) (j) :
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
  ..(AddGroup.sections_add_subgroup (F ⋙ forget₂ (Module R) AddCommGroup ⋙ forget₂ AddCommGroup AddGroup)) }

instance sections_add_comm_group (F : J ⥤ Module R) : add_comm_group ((F ⋙ forget (Module R)).sections) :=
(by apply_instance : add_comm_group (sections_submodule F))

instance limit_add_comm_group (F : J ⥤ Module R) :
  add_comm_group (limit (F ⋙ forget (Module R))) :=
begin
  haveI := Module.sections_add_comm_group F,
  transport using (types.limit_equiv_sections (F ⋙ forget (Module R))).symm,
end

instance limit_module (F : J ⥤ Module R) :
  module R (limit (F ⋙ forget (Module R))) :=
begin
  haveI : module R ((F ⋙ forget (Module R)).sections) :=
    (by apply_instance : module R (sections_submodule F)),
  exact equiv.semimodule R (types.limit_equiv_sections (F ⋙ forget (Module R))),
end

/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limit_π_linear_map (F : J ⥤ Module R) (j) :
  limit (F ⋙ forget (Module R)) →ₗ[R] (F ⋙ forget (Module R)).obj j :=
{ to_fun := limit.π (F ⋙ forget (Module R)) j,
  map_smul' := λ x y, by { erw types.limit_equiv_sections_symm_apply, refl },
  map_add' := λ x y, by { erw types.limit_equiv_sections_symm_apply, refl } }

lemma limit_π_linear_map_apply (F : J ⥤ Module R) (j) (x) :
  (limit_π_linear_map F j) x = limit.π (F ⋙ forget (Module R)) j x := rfl

namespace has_limits
-- The next two definitions are used in the construction of `has_limits (Module R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Module R`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ Module R) : cone F :=
{ X := Module.of R (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_linear_map F,
    naturality' := λ j j' f,
      linear_map.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

@[simps]
def forget_map_cone_limit_cone_iso (F : J ⥤ Module R) :
  (forget (Module R)).map_cone (limit_cone F) ≅ limit.cone (F ⋙ forget (Module R)) :=
{ hom := { hom := 𝟙 _, },
  inv := { hom := 𝟙 _, } }

def is_limit_forget_map_cone_limit_cone (F : J ⥤ Module R) :
  is_limit ((forget (Module R)).map_cone (limit_cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) (forget_map_cone_limit_cone_iso F).symm

/--
Witness that the limit cone in `Module R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ Module R) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget (Module R)) (is_limit_forget_map_cone_limit_cone F)
    (λ s, ⟨_, _, _⟩) (λ s, rfl),
  { intros, ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom, types.lift_π_apply,
      linear_map.map_add, types_id_apply, functor.map_cone_π],
    rw ←limit_π_linear_map_apply,
    simp [limit_π_linear_map], },
  { intros, ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom, types.lift_π_apply,
      linear_map.map_smul, types_id_apply, functor.map_cone_π],
    rw ←limit_π_linear_map_apply,
    simp [limit_π_linear_map], },
end

end has_limits

open has_limits

/-- The category of R-modules has all limits. -/
instance has_limits : has_limits (Module R) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F,
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

def limit_iso_Module_of_limit_forget (F : J ⥤ Module R) :
  limit F ≅ Module.of R (limit (F ⋙ forget (Module R))) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit F)
  (limit_cone_is_limit F)

def forget₂_AddCommGroup_limit_iso_AddCommGroup_of_limit_forget (F : J ⥤ Module R) :
  (forget₂ (Module R) AddCommGroup).obj (limit F) ≅ AddCommGroup.of (limit (F ⋙ forget (Module R))) :=
(forget₂ (Module R) AddCommGroup).map_iso (limit_iso_Module_of_limit_forget F)

def is_limit_forget₂_AddCommGroup_map_cone_limit_cone (F : J ⥤ Module R) :
  is_limit ((forget₂ (Module R) AddCommGroup).map_cone (limit.cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext
(AddCommGroup.limit_iso_AddCommGroup_of_limit_forget _ ≪≫
  (forget₂_AddCommGroup_limit_iso_AddCommGroup_of_limit_forget _).symm)
(λ j,
begin
  simp only [forget₂_AddCommGroup_limit_iso_AddCommGroup_of_limit_forget,
    limit_iso_Module_of_limit_forget, is_limit.cone_point_unique_up_to_iso,
    functor.map_iso_inv, is_limit.unique_up_to_iso_inv, iso.symm_hom, limit.is_limit_lift,
    limit.cone_π, cones.forget_map, is_limit.lift_cone_morphism_hom, iso.trans_hom, category.assoc,
     functor.map_cone_π],
  erw [←category_theory.functor.map_comp, limit.lift_π, is_limit.fac],
  refl,
end)

/--
The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂_AddCommGroup_preserves_limits : preserves_limits (forget₂ (Module R) AddCommGroup) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (is_limit_forget₂_AddCommGroup_map_cone_limit_cone F) } }

/--
The forgetful functor from R-modules to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget (Module R)) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (is_limit_forget_map_cone_limit_cone F) } }

end Module
