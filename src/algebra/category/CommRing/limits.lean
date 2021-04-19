/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.ring.pi
import algebra.category.CommRing.basic
import algebra.category.Group.limits
import ring_theory.subring

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

## Implementation note

Lean suffers in some unification steps, and has to do a lot of unfolding to check that types match.
We use a hack that prefixing such proofs with `by convert` can give a huge speedup.
-/

/- We use the following trick a lot of times in this file.-/
/--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/
library_note "change elaboration strategy with `by apply`"

/- We use the following trick a lot of times in this file.-/
/--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/
library_note "change elaboration strategy with `by apply`"

open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace SemiRing

variables {J : Type u} [small_category J]

instance semiring_obj (F : J ⥤ SemiRing) (j) :
  semiring ((F ⋙ forget SemiRing).obj j) :=
by { change semiring (F.obj j), apply_instance }

/--
The flat sections of a functor into `SemiRing` form a subsemiring of all sections.
-/
def sections_subsemiring (F : J ⥤ SemiRing) :
  subsemiring (Π j, F.obj j) :=
{ carrier := (F ⋙ forget SemiRing).sections,
  ..(AddMon.sections_add_submonoid (F ⋙ forget₂ SemiRing AddCommMon ⋙ forget₂ AddCommMon AddMon)),
  ..(Mon.sections_submonoid (F ⋙ forget₂ SemiRing Mon)) }

instance limit_semiring (F : J ⥤ SemiRing) :
  semiring (types.limit_cone (F ⋙ forget SemiRing.{u})).X :=
(sections_subsemiring F).to_semiring

/-- `limit.π (F ⋙ forget SemiRing) j` as a `ring_hom`. -/
def limit_π_ring_hom (F : J ⥤ SemiRing.{u}) (j) :
  (types.limit_cone (F ⋙ forget SemiRing)).X →+* (F ⋙ forget SemiRing).obj j :=
{ to_fun := (types.limit_cone (F ⋙ forget SemiRing)).π.app j,
  ..AddMon.limit_π_add_monoid_hom
      (F ⋙ forget₂ SemiRing AddCommMon.{u} ⋙ forget₂ AddCommMon AddMon) j,
  ..Mon.limit_π_monoid_hom (F ⋙ forget₂ SemiRing Mon) j, }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits SemiRing`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `SemiRing`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ SemiRing) : cone F :=
{ X := SemiRing.of (types.limit_cone (F ⋙ forget _)).X,
  π :=
  { app := limit_π_ring_hom F,
    naturality' := λ j j' f,
      ring_hom.coe_inj ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `SemiRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ SemiRing) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget SemiRing) (types.limit_cone_is_limit _)
    (λ s, ⟨_, _, _, _, _⟩) (λ s, rfl); tidy
end

end has_limits

open has_limits

/-- The category of rings has all limits. -/
@[irreducible]
instance has_limits : has_limits SemiRing :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommMon_preserves_limits_aux (F : J ⥤ SemiRing) :
  is_limit ((forget₂ SemiRing AddCommMon).map_cone (limit_cone F)) :=
by apply AddCommMon.limit_cone_is_limit (F ⋙ forget₂ SemiRing AddCommMon)

/--
The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂_AddCommMon_preserves_limits : preserves_limits (forget₂ SemiRing AddCommMon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (forget₂_AddCommMon_preserves_limits_aux F) } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_Mon_preserves_limits_aux (F : J ⥤ SemiRing) :
  is_limit ((forget₂ SemiRing Mon).map_cone (limit_cone F)) :=
by apply Mon.has_limits.limit_cone_is_limit (F ⋙ forget₂ SemiRing Mon)

/--
The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂_Mon_preserves_limits :
  preserves_limits (forget₂ SemiRing Mon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (forget₂_Mon_preserves_limits_aux F) } }

/--
The forgetful functor from semirings to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget SemiRing) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) } }

end SemiRing

namespace CommSemiRing

variables {J : Type u} [small_category J]

instance comm_semiring_obj (F : J ⥤ CommSemiRing) (j) :
  comm_semiring ((F ⋙ forget CommSemiRing).obj j) :=
by { change comm_semiring (F.obj j), apply_instance }

instance limit_comm_semiring (F : J ⥤ CommSemiRing) :
  comm_semiring (types.limit_cone (F ⋙ forget CommSemiRing.{u})).X :=
@subsemiring.to_comm_semiring (Π j, F.obj j) _
  (SemiRing.sections_subsemiring (F ⋙ forget₂ CommSemiRing SemiRing.{u}))

/--
We show that the forgetful functor `CommSemiRing ⥤ SemiRing` creates limits.

All we need to do is notice that the limit point has a `comm_semiring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommSemiRing) : creates_limit F (forget₂ CommSemiRing SemiRing.{u}) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := CommSemiRing.of (types.limit_cone (F ⋙ forget _)).X,
    π :=
    { app := by apply SemiRing.limit_π_ring_hom (F ⋙ forget₂ CommSemiRing SemiRing),
      naturality' := (SemiRing.has_limits.limit_cone (F ⋙ forget₂ _ _)).π.naturality, } },
  valid_lift := by apply is_limit.unique_up_to_iso (SemiRing.has_limits.limit_cone_is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ CommSemiRing SemiRing.{u})
    (by apply SemiRing.has_limits.limit_cone_is_limit _)
    (λ s, (SemiRing.has_limits.limit_cone_is_limit _).lift ((forget₂ _ SemiRing).map_cone s))
    (λ s, rfl) })

/--
A choice of limit cone for a functor into `CommSemiRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone (F : J ⥤ CommSemiRing) : cone F :=
lift_limit (limit.is_limit (F ⋙ (forget₂ CommSemiRing SemiRing.{u})))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit (F : J ⥤ CommSemiRing) : is_limit (limit_cone F) :=
lifted_limit_is_limit _

/-- The category of rings has all limits. -/
@[irreducible]
instance has_limits : has_limits CommSemiRing.{u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommSemiRing SemiRing.{u}) } }

/--
The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂_SemiRing_preserves_limits : preserves_limits (forget₂ CommSemiRing SemiRing) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget CommSemiRing) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F,
    limits.comp_preserves_limit (forget₂ CommSemiRing SemiRing) (forget SemiRing) } }


end CommSemiRing


namespace Ring

variables {J : Type u} [small_category J]

instance ring_obj (F : J ⥤ Ring) (j) :
  ring ((F ⋙ forget Ring).obj j) :=
by { change ring (F.obj j), apply_instance }

/--
The flat sections of a functor into `Ring` form a subring of all sections.
-/
def sections_subring (F : J ⥤ Ring) :
  subring (Π j, F.obj j) :=
{ carrier := (F ⋙ forget Ring).sections,
  .. AddGroup.sections_add_subgroup (F ⋙ forget₂ Ring AddCommGroup ⋙ forget₂ AddCommGroup AddGroup),
  .. SemiRing.sections_subsemiring (F ⋙ forget₂ Ring SemiRing) }

instance limit_ring (F : J ⥤ Ring) :
  ring (types.limit_cone (F ⋙ forget Ring.{u})).X :=
(sections_subring F).to_ring

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ Ring) : creates_limit F (forget₂ Ring SemiRing.{u}) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := Ring.of (types.limit_cone (F ⋙ forget _)).X,
    π :=
    { app := by apply SemiRing.limit_π_ring_hom (F ⋙ forget₂ Ring SemiRing),
      naturality' := (SemiRing.has_limits.limit_cone (F ⋙ forget₂ _ _)).π.naturality, } },
  valid_lift := by apply is_limit.unique_up_to_iso (SemiRing.has_limits.limit_cone_is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ Ring SemiRing.{u})
    (by apply SemiRing.has_limits.limit_cone_is_limit _)
    (λ s, _) (λ s, rfl) })

/--
A choice of limit cone for a functor into `Ring`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone (F : J ⥤ Ring) : cone F :=
lift_limit (limit.is_limit (F ⋙ (forget₂ Ring SemiRing.{u})))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit (F : J ⥤ Ring) : is_limit (limit_cone F) :=
lifted_limit_is_limit _

/-- The category of rings has all limits. -/
@[irreducible]
instance has_limits : has_limits Ring :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ Ring SemiRing) } }

/--
The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂_SemiRing_preserves_limits : preserves_limits (forget₂ Ring SemiRing) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommGroup_preserves_limits_aux (F : J ⥤ Ring) :
  is_limit ((forget₂ Ring AddCommGroup).map_cone (limit_cone F)) :=
by apply AddCommGroup.limit_cone_is_limit (F ⋙ forget₂ Ring AddCommGroup)

/--
The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂_AddCommGroup_preserves_limits : preserves_limits (forget₂ Ring AddCommGroup) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (forget₂_AddCommGroup_preserves_limits_aux F) } }

/--
The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget Ring) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F,
    limits.comp_preserves_limit (forget₂ Ring SemiRing) (forget SemiRing) } }

end Ring


namespace CommRing

variables {J : Type u} [small_category J]

instance comm_ring_obj (F : J ⥤ CommRing) (j) :
  comm_ring ((F ⋙ forget CommRing).obj j) :=
by { change comm_ring (F.obj j), apply_instance }

instance limit_comm_ring (F : J ⥤ CommRing) :
  comm_ring (types.limit_cone (F ⋙ forget CommRing.{u})).X :=
@subring.to_comm_ring (Π j, F.obj j) _
  (Ring.sections_subring (F ⋙ forget₂ CommRing Ring.{u}))

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `comm_ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRing) : creates_limit F (forget₂ CommRing Ring.{u}) :=
/-
A terse solution here would be
```
creates_limit_of_fully_faithful_of_iso (CommRing.of (limit (F ⋙ forget _))) (iso.refl _)
```
but it seems this would introduce additional identity morphisms in `limit.π`.
-/
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone :=
  { X := CommRing.of (types.limit_cone (F ⋙ forget _)).X,
    π :=
    { app := by apply
        SemiRing.limit_π_ring_hom (F ⋙ forget₂ CommRing Ring.{u} ⋙ forget₂ Ring SemiRing),
      naturality' := (SemiRing.has_limits.limit_cone
        (F ⋙ forget₂ _ Ring.{u} ⋙ forget₂ _ SemiRing)).π.naturality } },
  valid_lift := by apply is_limit.unique_up_to_iso (Ring.limit_cone_is_limit _) t,
  makes_limit := is_limit.of_faithful (forget₂ _ Ring.{u})
    (by apply Ring.limit_cone_is_limit (F ⋙ forget₂ CommRing Ring))
    (λ s, (Ring.limit_cone_is_limit _).lift ((forget₂ _ Ring.{u}).map_cone s)) (λ s, rfl) })

/--
A choice of limit cone for a functor into `CommRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limit_cone (F : J ⥤ CommRing) : cone F :=
lift_limit (limit.is_limit (F ⋙ (forget₂ CommRing Ring.{u})))

/--
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limit_cone_is_limit (F : J ⥤ CommRing) : is_limit (limit_cone F) :=
lifted_limit_is_limit _

/-- The category of commutative rings has all limits. -/
@[irreducible]
instance has_limits : has_limits CommRing.{u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommRing Ring.{u}) } }

/--
The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂_Ring_preserves_limits : preserves_limits (forget₂ CommRing Ring) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_CommSemiRing_preserves_limits_aux (F : J ⥤ CommRing) :
  is_limit ((forget₂ CommRing CommSemiRing).map_cone (limit_cone F)) :=
by apply CommSemiRing.limit_cone_is_limit (F ⋙ forget₂ CommRing CommSemiRing)

/--
The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂_CommSemiRing_preserves_limits : preserves_limits (forget₂ CommRing CommSemiRing) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (forget₂_CommSemiRing_preserves_limits_aux F) } }

/--
The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget CommRing) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ CommRing Ring) (forget Ring) } }

end CommRing
