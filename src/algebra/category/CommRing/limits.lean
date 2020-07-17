/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.CommRing.basic
import algebra.category.Group.limits
import deprecated.subgroup

/-!
# The category of commutative rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

## Further work
A lot of this should be generalised / automated, as it's quite common for concrete
categories that the forgetful functor preserves limits.
-/

open category_theory
open category_theory.limits

universe u

namespace CommRing

variables {J : Type u} [small_category J]

instance comm_ring_obj (F : J ⥤ CommRing) (j) :
  comm_ring ((F ⋙ forget CommRing).obj j) :=
by { change comm_ring (F.obj j), apply_instance }

/--
The flat sections of a functor into `CommRing` form a multiplicative submonoid of all sections.
-/
def sections_submonoid (F : J ⥤ CommRing) :
  submonoid (Π j, F.obj j) :=
{ carrier := (F ⋙ forget CommRing).sections,
  one_mem' := λ j j' f, by simp,
  mul_mem' := λ a b ah bh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, ring_hom.map_mul, pi.mul_apply],
    dsimp [functor.sections] at ah bh,
    rw [ah f, bh f],
  end }

-- We still don't have bundled subrings,
-- so we need to convert the bundled sub-objects back to unbundled

instance sections_submonoid' (F : J ⥤ CommRing) :
  is_submonoid (F ⋙ forget CommRing).sections :=
(sections_submonoid F).is_submonoid

instance sections_add_subgroup' (F : J ⥤ CommRing) :
  is_add_subgroup (F ⋙ forget CommRing).sections :=
(AddCommGroup.sections_add_subgroup (F ⋙ forget₂ CommRing Ring ⋙ forget₂ Ring AddCommGroup)).is_subgroup

instance sections_subring (F : J ⥤ CommRing) :
  is_subring (F ⋙ forget CommRing).sections := {}

instance limit_comm_ring (F : J ⥤ CommRing) :
  comm_ring (limit (F ⋙ forget CommRing)) :=
@subtype.comm_ring ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
  (by convert (CommRing.sections_subring F))

/-- `limit.π (F ⋙ forget CommRing) j` as a `ring_hom`. -/
def limit_π_ring_hom (F : J ⥤ CommRing) (j) :
  limit (F ⋙ forget CommRing) →+* (F ⋙ forget CommRing).obj j :=
{ to_fun := limit.π (F ⋙ forget CommRing) j,
  map_one' := by { simp only [types.types_limit_π], refl },
  map_zero' := by { simp only [types.types_limit_π], refl },
  map_mul' := λ x y, by { simp only [types.types_limit_π], refl },
  map_add' := λ x y, by { simp only [types.types_limit_π], refl } }

namespace CommRing_has_limits
-- The next two definitions are used in the construction of `has_limits CommRing`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `CommRing`.
(Internal use only; use the limits API.)
-/
def limit (F : J ⥤ CommRing) : cone F :=
{ X := CommRing.of (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_ring_hom F,
    naturality' := λ j j' f,
      ring_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `CommRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_is_limit (F : J ⥤ CommRing) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful
    (forget CommRing) (limit.is_limit _)
    (λ s, ⟨_, _, _, _, _⟩) (λ s, rfl); tidy
end

end CommRing_has_limits
open CommRing_has_limits

/-- The category of commutative rings has all limits. -/
instance CommRing_has_limits : has_limits CommRing :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI
    { cone     := limit F,
      is_limit := limit_is_limit F } } }

/--
The forgetful functor from commutative rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget CommRing) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end CommRing
