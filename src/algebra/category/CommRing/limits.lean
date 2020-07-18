/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.CommRing.basic
import algebra.category.Group.limits
import category_theory.limits.creates
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

namespace Ring

variables {J : Type u} [small_category J]

instance ring_obj (F : J ⥤ Ring) (j) :
  ring ((F ⋙ forget Ring).obj j) :=
by { change ring (F.obj j), apply_instance }

/--
The flat sections of a functor into `Ring` form a multiplicative submonoid of all sections.
-/
def sections_submonoid (F : J ⥤ Ring) :
  submonoid (Π j, F.obj j) :=
{ carrier := (F ⋙ forget Ring).sections,
  one_mem' := λ j j' f, by simp,
  mul_mem' := λ a b ah bh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, ring_hom.map_mul, pi.mul_apply],
    dsimp [functor.sections] at ah bh,
    rw [ah f, bh f],
  end }

-- We still don't have bundled subrings,
-- so we need to convert the bundled sub-objects back to unbundled

instance sections_submonoid' (F : J ⥤ Ring) :
  is_submonoid (F ⋙ forget Ring).sections :=
(sections_submonoid F).is_submonoid

instance sections_add_subgroup' (F : J ⥤ Ring) :
  is_add_subgroup (F ⋙ forget Ring).sections :=
(AddCommGroup.sections_add_subgroup (F ⋙ forget₂ Ring AddCommGroup)).is_subgroup

instance sections_subring (F : J ⥤ Ring) :
  is_subring (F ⋙ forget Ring).sections := {}

instance limit_comm_ring (F : J ⥤ Ring) :
  ring (limit (F ⋙ forget Ring)) :=
@subtype.ring ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
  (by convert (Ring.sections_subring F))

/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limit_π_ring_hom (F : J ⥤ Ring) (j) :
  limit (F ⋙ forget Ring) →+* (F ⋙ forget Ring).obj j :=
{ to_fun := limit.π (F ⋙ forget Ring) j,
  map_one' := by { simp only [types.types_limit_π], refl },
  map_zero' := by { simp only [types.types_limit_π], refl },
  map_mul' := λ x y, by { simp only [types.types_limit_π], refl },
  map_add' := λ x y, by { simp only [types.types_limit_π], refl } }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits Ring`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Ring`.
(Internal use only; use the limits API.)
-/
def limit (F : J ⥤ Ring) : cone F :=
{ X := Ring.of (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_ring_hom F,
    naturality' := λ j j' f,
      ring_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Ring` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_is_limit (F : J ⥤ Ring) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful
    (forget Ring) (limit.is_limit _)
    (λ s, ⟨_, _, _, _, _⟩) (λ s, rfl); tidy
end

end has_limits

open has_limits

/-- The category of rings has all limits. -/
instance has_limits : has_limits Ring :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI
    { cone     := limit F,
      is_limit := limit_is_limit F } } }

/--
The forgetful functor from commutative rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget Ring) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end Ring


namespace CommRing

variables {J : Type u} [small_category J]

instance comm_ring_obj (F : J ⥤ CommRing) (j) :
  comm_ring ((F ⋙ forget CommRing).obj j) :=
by { change comm_ring (F.obj j), apply_instance }

instance limit_comm_ring (F : J ⥤ CommRing) :
  comm_ring (limit (F ⋙ forget CommRing)) :=
@subtype.comm_ring ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
  (by convert (Ring.sections_subring (F ⋙ forget₂ CommRing Ring)))

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `comm_ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRing) : creates_limit F (forget₂ CommRing Ring) :=
/-
A terse solution here would be
```
creates_limit_of_fully_faithful_of_iso (CommRing.of (limit (F ⋙ forget _))) (iso.refl _)
```
but it seems this would introduce additional identity morphisms in `limit.π`.
-/
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := CommRing.of (limit (F ⋙ forget _)),
    π :=
    { app := Ring.limit_π_ring_hom (F ⋙ forget₂ CommRing Ring),
      naturality' := (Ring.has_limits.limit (F ⋙ forget₂ _ _)).π.naturality, } },
  valid_lift := is_limit.unique_up_to_iso (limit.is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ CommRing Ring) (limit.is_limit _)
    (λ s, _) (λ s, rfl) })

/-- The category of commutative rings has all limits. -/
instance has_limits : has_limits CommRing :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommRing Ring) } }

/--
The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂_Ring_preserves_limits : preserves_limits (forget₂ CommRing Ring) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget CommRing) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end CommRing
