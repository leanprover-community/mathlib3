/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.limits.types
import category_theory.limits.preserves
import algebra.pi_instances

/-!
# The category of abelian groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

## Further work
A lot of this should be generalised / automated, as it's quite common for concrete
categories that the forgetful functor preserves limits.
-/

open category_theory
open category_theory.limits

universe u

namespace AddCommGroup

variables {J : Type u} [small_category J]

instance add_comm_group_obj (F : J ⥤ AddCommGroup.{u}) (j) :
  add_comm_group ((F ⋙ forget AddCommGroup).obj j) :=
by { change add_comm_group (F.obj j), apply_instance }

instance sections_add_submonoid (F : J ⥤ AddCommGroup.{u}) :
  is_add_submonoid (F ⋙ forget AddCommGroup).sections :=
{ zero_mem := λ j j' f,
  begin
    erw [functor.comp_map, forget_map_eq_coe, (F.map f).map_zero],
    refl,
  end,
  add_mem := λ a b ah bh j j' f,
  begin
    erw [functor.comp_map, forget_map_eq_coe, (F.map f).map_add],
    dsimp [functor.sections] at ah,
    rw ah f,
    dsimp [functor.sections] at bh,
    rw bh f,
    refl,
  end }

instance sections_add_subgroup (F : J ⥤ AddCommGroup.{u}) :
  is_add_subgroup (F ⋙ forget AddCommGroup).sections :=
{ neg_mem := λ a ah j j' f,
  begin
    erw [functor.comp_map, forget_map_eq_coe, (F.map f).map_neg],
    dsimp [functor.sections] at ah,
    rw ah f,
    refl,
  end,
  ..(AddCommGroup.sections_add_submonoid F) }

instance limit_add_comm_group (F : J ⥤ AddCommGroup.{u}) :
  add_comm_group (limit (F ⋙ forget AddCommGroup)) :=
@subtype.add_comm_group ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
  (by convert (AddCommGroup.sections_add_subgroup F))

/-- `limit.π (F ⋙ forget AddCommGroup) j` as a `add_monoid_hom`. -/
def limit_π_add_monoid_hom (F : J ⥤ AddCommGroup.{u}) (j) :
  limit (F ⋙ forget AddCommGroup) →+ (F ⋙ forget AddCommGroup).obj j :=
{ to_fun := limit.π (F ⋙ forget AddCommGroup) j,
  map_zero' := by { simp only [types.types_limit_π], refl },
  map_add' := λ x y, by { simp only [types.types_limit_π], refl } }

namespace AddCommGroup_has_limits
-- The next two definitions are used in the construction of `has_limits AddCommGroup`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `AddCommGroup`.
(Internal use only; use the limits API.)
-/
def limit (F : J ⥤ AddCommGroup.{u}) : cone F :=
{ X := ⟨limit (F ⋙ forget _), by apply_instance⟩,
  π :=
  { app := limit_π_add_monoid_hom F,
    naturality' := λ j j' f,
      add_monoid_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `AddCommGroup` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_is_limit (F : J ⥤ AddCommGroup.{u}) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful
    (forget AddCommGroup) (limit.is_limit _)
    (λ s, ⟨_, _, _⟩) (λ s, rfl); dsimp,
  { apply subtype.eq, funext, dsimp,
    erw (s.π.app j).map_zero, refl },
  { intros x y, apply subtype.eq, funext, dsimp,
    erw (s.π.app j).map_add, refl }
end

end AddCommGroup_has_limits
open AddCommGroup_has_limits

/-- The category of abelian groups has all limits. -/
instance AddCommGroup_has_limits : has_limits.{u} AddCommGroup.{u} :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI
    { cone     := limit F,
      is_limit := limit_is_limit F } } }

/--
The forgetful functor from abelian groups to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget AddCommGroup.{u}) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end AddCommGroup
