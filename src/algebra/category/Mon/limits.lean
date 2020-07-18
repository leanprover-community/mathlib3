/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import category_theory.limits.types
import category_theory.limits.creates
import algebra.pi_instances

/-!
# The category of (commutative / additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

## Further work
A lot of this should be automated, as it's quite common for concrete
categories that the forgetful functor preserves limits.
-/

open category_theory
open category_theory.limits

universe u

namespace Mon

variables {J : Type u} [small_category J]

-- FIXME: to_additive by default transports this to `AddMon.monoid_obj`
@[to_additive AddMon.add_monoid_obj]
instance monoid_obj (F : J ⥤ Mon) (j) :
  monoid ((F ⋙ forget Mon).obj j) :=
by { change monoid (F.obj j), apply_instance }

/--
The flat sections of a functor into `Mon` form a additive submonoid of all sections.
-/
@[to_additive AddMon.sections_add_submonoid]
def sections_submonoid (F : J ⥤ Mon) :
  submonoid (Π j, F.obj j) :=
{ carrier := (F ⋙ forget Mon).sections,
  one_mem' := λ j j' f, by simp,
  mul_mem' := λ a b ah bh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, monoid_hom.map_mul, pi.mul_apply],
    dsimp [functor.sections] at ah bh,
    rw [ah f, bh f],
  end }

@[to_additive AddMon.limit_add_monoid]
instance limit_monoid (F : J ⥤ Mon) :
  monoid (limit (F ⋙ forget Mon)) :=
begin
  change monoid (sections_submonoid F),
  apply_instance,
end

/-- `limit.π (F ⋙ forget Mon) j` as a `monoid_hom`. -/
@[to_additive AddCommGroup.limit_π_add_monoid_hom]
def limit_π_monoid_hom (F : J ⥤ Mon) (j) :
  limit (F ⋙ forget Mon) →* (F ⋙ forget Mon).obj j :=
{ to_fun := limit.π (F ⋙ forget Mon) j,
  map_one' := by { simp only [types.types_limit_π], refl },
  map_mul' := λ x y, by { simp only [types.types_limit_π], refl } }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits Mon`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Mon`.
(Internal use only; use the limits API.)
-/
@[to_additive AddMon.has_limits.limit]
def limit (F : J ⥤ Mon) : cone F :=
{ X := Mon.of (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_monoid_hom F,
    naturality' := λ j j' f,
      monoid_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Mon` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive AddMon.has_limits.limit_is_limit]
def limit_is_limit (F : J ⥤ Mon) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful
    (forget Mon) (limit.is_limit _)
    (λ s, ⟨_, _, _⟩) (λ s, rfl); tidy,
end

end has_limits

open has_limits

/-- The category of monoids has all limits. -/
@[to_additive AddMon.has_limits]
instance has_limits : has_limits Mon :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI
    { cone     := limit F,
      is_limit := limit_is_limit F } } }

/--
The forgetful functor from monoids to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddMon.forget_preserves_limits]
instance forget_preserves_limits : preserves_limits (forget Mon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end Mon

namespace CommMon

variables {J : Type u} [small_category J]

instance comm_monoid_obj (F : J ⥤ CommMon) (j) :
  comm_monoid ((F ⋙ forget CommMon).obj j) :=
by { change comm_monoid (F.obj j), apply_instance }

instance limit_comm_monoid (F : J ⥤ CommMon) :
  comm_monoid (limit (F ⋙ forget CommMon)) :=
sorry

-- (Mon.sections_submonoid (F ⋙ forget₂ CommMon Mon)).to_comm_monoid

-- @subtype.comm_monoid ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
--   (by convert (Mon.sections_submonoid (F ⋙ forget₂ CommMon Mon)))

/--
We show that the forgetful functor `CommMon ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `comm_monoid` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommMon) : creates_limit F (forget₂ CommMon Mon) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := CommMon.of (limit (F ⋙ forget _)),
    π :=
    { app := Mon.limit_π_monoid_hom (F ⋙ forget₂ CommMon Mon),
      naturality' := (Mon.has_limits.limit (F ⋙ forget₂ _ _)).π.naturality, } },
  valid_lift := is_limit.unique_up_to_iso (limit.is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ CommMon Mon) (limit.is_limit _)
    (λ s, _) (λ s, rfl) })

/-- The category of commutative monoids has all limits. -/
instance has_limits : has_limits CommMon :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommMon Mon) } }

/--
The forgetful functor from commutative monoids to monoids preserves all limits.
(That is, the underlying monoid could have been computed instead as limits in the category of monoids.)
-/
instance forget₂_Mon_preserves_limits : preserves_limits (forget₂ CommMon Mon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
The forgetful functor from commutative monoids to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget CommMon) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end CommMon



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
