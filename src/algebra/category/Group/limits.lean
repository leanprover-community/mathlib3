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

namespace CommGroup

variables {J : Type u} [small_category J]

-- FIXME: to_additive by default transports this to `AddCommGroup.comm_group_obj`
@[to_additive AddCommGroup.add_comm_group_obj]
instance comm_group_obj (F : J ⥤ CommGroup) (j) :
  comm_group ((F ⋙ forget CommGroup).obj j) :=
by { change comm_group (F.obj j), apply_instance }

/--
The flat sections of a functor into `AddCommGroup` form a additive submonoid of all sections.
-/
@[to_additive AddCommGroup.sections_add_submonoid]
def sections_submonoid (F : J ⥤ CommGroup) :
  submonoid (Π j, F.obj j) :=
{ carrier := (F ⋙ forget CommGroup).sections,
  one_mem' := λ j j' f, by simp,
  mul_mem' := λ a b ah bh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, monoid_hom.map_mul, pi.mul_apply],
    dsimp [functor.sections] at ah bh,
    rw [ah f, bh f],
  end }

/--
The flat sections of a functor into `AddCommGroup` form a additive subgroup of all sections.
-/
@[to_additive AddCommGroup.sections_add_subgroup]
def sections_subgroup (F : J ⥤ CommGroup) :
  subgroup (Π j, F.obj j) :=
{ carrier := (F ⋙ forget CommGroup).sections,
  inv_mem' := λ a ah j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, pi.inv_apply, monoid_hom.map_inv, inv_inj],
    dsimp [functor.sections] at ah,
    rw ah f,
  end,
  ..(CommGroup.sections_submonoid F) }

@[to_additive AddCommGroup.limit_add_comm_group]
instance limit_comm_group (F : J ⥤ CommGroup) :
  comm_group (limit (F ⋙ forget CommGroup)) :=
begin
  change comm_group (sections_subgroup F),
  apply_instance,
end

/-- `limit.π (F ⋙ forget CommGroup) j` as a `monoid_hom`. -/
@[to_additive AddCommGroup.limit_π_add_monoid_hom]
def limit_π_monoid_hom (F : J ⥤ CommGroup) (j) :
  limit (F ⋙ forget CommGroup) →* (F ⋙ forget CommGroup).obj j :=
{ to_fun := limit.π (F ⋙ forget CommGroup) j,
  map_one' := by { simp only [types.types_limit_π], refl },
  map_mul' := λ x y, by { simp only [types.types_limit_π], refl } }

namespace CommGroup_has_limits
-- The next two definitions are used in the construction of `has_limits CommGroup`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `CommGroup`.
(Internal use only; use the limits API.)
-/
@[to_additive AddCommGroup_has_limits.limit]
def limit (F : J ⥤ CommGroup) : cone F :=
{ X := CommGroup.of (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_monoid_hom F,
    naturality' := λ j j' f,
      monoid_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `CommGroup` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive AddCommGroup_has_limits.limit_is_limit]
def limit_is_limit (F : J ⥤ CommGroup) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful
    (forget CommGroup) (limit.is_limit _)
    (λ s, ⟨_, _, _⟩) (λ s, rfl); tidy,
end

end CommGroup_has_limits

open CommGroup_has_limits

/-- The category of commutative groups has all limits. -/
@[to_additive AddCommGroup.has_limits]
instance has_limits : has_limits CommGroup :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI
    { cone     := limit F,
      is_limit := limit_is_limit F } } }

/--
The forgetful functor from commutative groups to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddCommGroup.forget_preserves_limits]
instance forget_preserves_limits : preserves_limits (forget CommGroup) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end CommGroup
