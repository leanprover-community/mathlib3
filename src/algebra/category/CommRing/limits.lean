/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.ring.pi
import algebra.category.CommRing.basic
import algebra.category.Group.limits
import ring_theory.subring
import ring_theory.subsemiring

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

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
  semiring (limit (F ⋙ forget SemiRing)) :=
begin
  haveI : semiring ((F ⋙ forget SemiRing).sections) := (sections_subsemiring F).to_semiring,
  transport using (types.limit_equiv_sections (F ⋙ forget SemiRing)).symm,
end

/-- `limit.π (F ⋙ forget SemiRing) j` as a `ring_hom`. -/
def limit_π_ring_hom (F : J ⥤ SemiRing) (j) :
  limit (F ⋙ forget SemiRing) →+* (F ⋙ forget SemiRing).obj j :=
{ to_fun := limit.π (F ⋙ forget SemiRing) j,
  ..AddMon.limit_π_add_monoid_hom (F ⋙ forget₂ SemiRing AddCommMon ⋙ forget₂ AddCommMon AddMon) j,
  ..Mon.limit_π_monoid_hom (F ⋙ forget₂ SemiRing Mon) j, }

lemma limit_π_ring_hom_apply (F : J ⥤ SemiRing) (j) (x) :
  (limit_π_ring_hom F j) x = limit.π (F ⋙ forget SemiRing) j x := rfl

namespace has_limits
-- The next two definitions are used in the construction of `has_limits SemiRing`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `SemiRing`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ SemiRing) : cone F :=
{ X := SemiRing.of (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_ring_hom F,
    naturality' := λ j j' f,
      ring_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

@[simps]
def forget_map_cone_limit_cone_iso (F : J ⥤ SemiRing) :
  (forget SemiRing).map_cone (limit_cone F) ≅ limit.cone (F ⋙ forget SemiRing) :=
{ hom := { hom := 𝟙 _, },
  inv := { hom := 𝟙 _, } }

def is_limit_forget_map_cone_limit_cone (F : J ⥤ SemiRing) :
  is_limit ((forget SemiRing).map_cone (limit_cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) (forget_map_cone_limit_cone_iso F).symm

/--
Witness that the limit cone in `SemiRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ SemiRing) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget SemiRing) (is_limit_forget_map_cone_limit_cone F)
    (λ s, ⟨_, _, _, _, _⟩) (λ s, rfl),
  { ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom, ring_hom.map_one,
      types.lift_π_apply, types_id_apply, functor.map_cone_π],
    rw ←limit_π_ring_hom_apply,
    simp, },
  { intros, ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom, types.lift_π_apply,
      types_id_apply, ring_hom.map_mul, functor.map_cone_π],
    rw ←limit_π_ring_hom_apply,
    simp [limit_π_ring_hom], },
  { ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, ring_hom.map_zero, function.comp_app, is_limit.lift_cone_morphism_hom,
      types.lift_π_apply, types_id_apply, functor.map_cone_π],
    rw ←limit_π_ring_hom_apply,
    simp, },
  { intros, ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, ring_hom.map_add,
      iso.symm_hom, limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom,
      types.lift_π_apply, types_id_apply, functor.map_cone_π],
    rw ←limit_π_ring_hom_apply,
    simp [limit_π_ring_hom], },
end

end has_limits

open has_limits

/-- The category of rings has all limits. -/
instance has_limits : has_limits SemiRing :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F,
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

def limit_iso_SemiRing_of_limit_forget (F : J ⥤ SemiRing) :
  limit F ≅ SemiRing.of (limit (F ⋙ forget SemiRing)) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit F)
  (limit_cone_is_limit F)

def forget₂_AddCommMon_limit_iso_AddCommMon_of_limit_forget (F : J ⥤ SemiRing) :
  (forget₂ SemiRing AddCommMon).obj (limit F) ≅ AddCommMon.of (limit (F ⋙ forget SemiRing)) :=
(forget₂ SemiRing AddCommMon).map_iso (limit_iso_SemiRing_of_limit_forget F)

def is_limit_forget₂_AddCommMon_map_cone_limit_cone (F : J ⥤ SemiRing) :
  is_limit ((forget₂ SemiRing AddCommMon).map_cone (limit.cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext
(AddCommMon.limit_iso_AddCommMon_of_limit_forget _ ≪≫
  (forget₂_AddCommMon_limit_iso_AddCommMon_of_limit_forget _).symm)
(λ j,
begin
  simp only [forget₂_AddCommMon_limit_iso_AddCommMon_of_limit_forget,
    limit_iso_SemiRing_of_limit_forget, is_limit.cone_point_unique_up_to_iso,
    functor.map_iso_inv, is_limit.unique_up_to_iso_inv, iso.symm_hom, limit.is_limit_lift,
    limit.cone_π, cones.forget_map, is_limit.lift_cone_morphism_hom, iso.trans_hom, category.assoc,
     functor.map_cone_π],
  erw [←category_theory.functor.map_comp, limit.lift_π, is_limit.fac],
  refl,
end)

/--
The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂_AddCommMon_preserves_limits : preserves_limits (forget₂ SemiRing AddCommMon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit.is_limit F) (is_limit_forget₂_AddCommMon_map_cone_limit_cone F) } }

def forget₂_Mon_limit_iso_Mon_of_limit_forget (F : J ⥤ SemiRing) :
  (forget₂ SemiRing Mon).obj (limit F) ≅ Mon.of (limit (F ⋙ forget SemiRing)) :=
(forget₂ SemiRing Mon).map_iso (limit_iso_SemiRing_of_limit_forget F)

def is_limit_forget₂_Mon_map_cone_limit_cone (F : J ⥤ SemiRing) :
  is_limit ((forget₂ SemiRing Mon).map_cone (limit.cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext
(Mon.limit_iso_Mon_of_limit_forget _ ≪≫
  (forget₂_Mon_limit_iso_Mon_of_limit_forget _).symm)
(λ j,
begin
  simp only [forget₂_Mon_limit_iso_Mon_of_limit_forget,
    limit_iso_SemiRing_of_limit_forget, is_limit.cone_point_unique_up_to_iso,
    functor.map_iso_inv, is_limit.unique_up_to_iso_inv, iso.symm_hom, limit.is_limit_lift,
    limit.cone_π, cones.forget_map, is_limit.lift_cone_morphism_hom, iso.trans_hom, category.assoc,
     functor.map_cone_π],
  erw [←category_theory.functor.map_comp, limit.lift_π, is_limit.fac],
  refl,
end)

/--
The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂_Mon_preserves_limits :
  preserves_limits (forget₂ SemiRing Mon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F,  preserves_limit_of_preserves_limit_cone
    (limit.is_limit F) (is_limit_forget₂_Mon_map_cone_limit_cone F) } }

/--
The forgetful functor from semirings to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget SemiRing) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (is_limit_forget_map_cone_limit_cone F) } }

end SemiRing

namespace CommSemiRing

variables {J : Type u} [small_category J]

instance comm_semiring_obj (F : J ⥤ CommSemiRing) (j) :
  comm_semiring ((F ⋙ forget CommSemiRing).obj j) :=
by { change comm_semiring (F.obj j), apply_instance }

instance limit_comm_semiring (F : J ⥤ CommSemiRing) :
  comm_semiring (limit (F ⋙ forget CommSemiRing)) :=
begin
  haveI : comm_semiring ((F ⋙ forget CommSemiRing).sections) :=
    @subsemiring.to_comm_semiring (Π j, F.obj j) _
      (SemiRing.sections_subsemiring (F ⋙ forget₂ CommSemiRing SemiRing)),
  transport using (types.limit_equiv_sections (F ⋙ forget CommSemiRing)).symm,
end

-- FIXME Applying `@[simps]` here causes a timeout. (However it doesn't seem to be necessary.)
def lifted_cone (F : J ⥤ CommSemiRing) : cone F :=
{ X := CommSemiRing.of (limit (F ⋙ forget CommSemiRing)),
  π :=
  { app := λ j, SemiRing.limit_π_ring_hom (F ⋙ forget₂ CommSemiRing SemiRing) j,
    naturality' := (SemiRing.has_limits.limit_cone (F ⋙ forget₂ CommSemiRing SemiRing)).π.naturality, } }

def is_limit_forget₂_map_cone_lifted_cone (F : J ⥤ CommSemiRing) :
  is_limit ((forget₂ CommSemiRing SemiRing).map_cone (lifted_cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext (SemiRing.limit_iso_SemiRing_of_limit_forget _) $
  λ j, by erw is_limit.fac

/--
We show that the forgetful functor `CommSemiRing ⥤ SemiRing` creates limits.

All we need to do is notice that the limit point has a `comm_semiring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommSemiRing) : creates_limit F (forget₂ CommSemiRing SemiRing) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone := lifted_cone F,
  valid_lift := is_limit.unique_up_to_iso (is_limit_forget₂_map_cone_lifted_cone F) t,
  makes_limit := is_limit.of_faithful (forget₂ CommSemiRing SemiRing) (is_limit_forget₂_map_cone_lifted_cone F)
    (λ s, _) (λ s, rfl) })

/-- The category of rings has all limits. -/
instance has_limits : has_limits CommSemiRing :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommSemiRing SemiRing) } }

def limit_iso_CommSemiRing_of_limit_forget (F : J ⥤ CommSemiRing) :
  limit F ≅ CommSemiRing.of (limit (F ⋙ forget CommSemiRing)) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit F)
  (lifted_limit_is_limit (limit.is_limit (F ⋙ forget₂ CommSemiRing SemiRing)))

def forget₂_CommMon_limit_iso_CommMon_of_limit_forget (F : J ⥤ CommSemiRing) :
  (forget₂ CommSemiRing CommMon).obj (limit F) ≅ CommMon.of (limit (F ⋙ forget CommSemiRing)) :=
(forget₂ CommSemiRing CommMon).map_iso (limit_iso_CommSemiRing_of_limit_forget F)

def is_limit_forget₂_CommMon_map_cone_limit_cone (F : J ⥤ CommSemiRing) :
  is_limit ((forget₂ CommSemiRing CommMon).map_cone (limit.cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext
(CommMon.limit_iso_CommMon_of_limit_forget _ ≪≫
  (forget₂_CommMon_limit_iso_CommMon_of_limit_forget _).symm)
(λ j,
begin
  simp only [forget₂_CommMon_limit_iso_CommMon_of_limit_forget,
    limit_iso_CommSemiRing_of_limit_forget, is_limit.cone_point_unique_up_to_iso,
    functor.map_iso_inv, is_limit.unique_up_to_iso_inv, iso.symm_hom, limit.is_limit_lift,
    limit.cone_π, cones.forget_map, is_limit.lift_cone_morphism_hom, iso.trans_hom, category.assoc,
     functor.map_cone_π],
  erw [←category_theory.functor.map_comp, limit.lift_π, is_limit.fac],
  refl,
end)

/--
The forgetful functor from commutative semirings to commutative monoids preserves all limits.
-/
instance forget₂_CommMon_preserves_limits :
  preserves_limits (forget₂ CommSemiRing CommMon) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit.is_limit F) (is_limit_forget₂_CommMon_map_cone_limit_cone F) } }

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
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ CommSemiRing SemiRing) (forget SemiRing) } }

end CommSemiRing


namespace Ring

variables {J : Type u} [small_category J]

instance ring_obj (F : J ⥤ Ring) (j) :
  ring ((F ⋙ forget Ring).obj j) :=
by { change ring (F.obj j), apply_instance }

-- We still don't have bundled subrings,
-- so we need to convert the bundled sub-objects back to unbundled

instance sections_submonoid' (F : J ⥤ Ring) :
  is_submonoid (F ⋙ forget Ring).sections :=
(Mon.sections_submonoid (F ⋙ forget₂ Ring SemiRing ⋙ forget₂ SemiRing Mon)).is_submonoid

instance sections_add_subgroup' (F : J ⥤ Ring) :
  is_add_subgroup (F ⋙ forget Ring).sections :=
(AddGroup.sections_add_subgroup (F ⋙ forget₂ Ring AddCommGroup ⋙ forget₂ AddCommGroup AddGroup)).is_add_subgroup

instance sections_subring (F : J ⥤ Ring) :
  is_subring (F ⋙ forget Ring).sections := {}

instance limit_ring (F : J ⥤ Ring) :
  ring (limit (F ⋙ forget Ring)) :=
begin
  haveI : ring ((F ⋙ forget Ring).sections) :=
    @subtype.ring ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
      (by convert (Ring.sections_subring F)),
  transport using (types.limit_equiv_sections (F ⋙ forget Ring)).symm,
end

def lifted_cone (F : J ⥤ Ring) : cone F :=
{ X := Ring.of (limit (F ⋙ forget Ring)),
  π :=
  { app := λ j, SemiRing.limit_π_ring_hom (F ⋙ forget₂ Ring SemiRing) j,
    naturality' := (SemiRing.has_limits.limit_cone (F ⋙ forget₂ Ring SemiRing)).π.naturality, } }

def is_limit_forget₂_map_cone_lifted_cone (F : J ⥤ Ring) :
  is_limit ((forget₂ Ring SemiRing).map_cone (lifted_cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext (SemiRing.limit_iso_SemiRing_of_limit_forget _) $
  λ j, by erw is_limit.fac

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ Ring) : creates_limit F (forget₂ Ring SemiRing) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone := lifted_cone F,
  valid_lift := is_limit.unique_up_to_iso (is_limit_forget₂_map_cone_lifted_cone F) t,
  makes_limit := is_limit.of_faithful (forget₂ Ring SemiRing) (is_limit_forget₂_map_cone_lifted_cone F)
    (λ s, _) (λ s, rfl) })

/-- The category of rings has all limits. -/
instance has_limits : has_limits Ring :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ Ring SemiRing) } }

def limit_iso_Ring_of_limit_forget (F : J ⥤ Ring) :
  limit F ≅ Ring.of (limit (F ⋙ forget Ring)) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit F)
  (lifted_limit_is_limit (limit.is_limit (F ⋙ forget₂ Ring SemiRing)))

/--
The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂_SemiRing_preserves_limits : preserves_limits (forget₂ Ring SemiRing) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by apply_instance } }

def forget₂_AddCommGroup_limit_iso_AddCommGroup_of_limit_forget (F : J ⥤ Ring) :
  (forget₂ Ring AddCommGroup).obj (limit F) ≅ AddCommGroup.of (limit (F ⋙ forget Ring)) :=
(forget₂ Ring AddCommGroup).map_iso (limit_iso_Ring_of_limit_forget F)

def is_limit_forget₂_AddCommGroup_map_cone_limit_cone (F : J ⥤ Ring) :
  is_limit ((forget₂ Ring AddCommGroup).map_cone (limit.cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext
(AddCommGroup.limit_iso_AddCommGroup_of_limit_forget _ ≪≫
  (forget₂_AddCommGroup_limit_iso_AddCommGroup_of_limit_forget _).symm)
(λ j,
begin
  simp only [forget₂_AddCommGroup_limit_iso_AddCommGroup_of_limit_forget,
    limit_iso_Ring_of_limit_forget, is_limit.cone_point_unique_up_to_iso,
    functor.map_iso_inv, is_limit.unique_up_to_iso_inv, iso.symm_hom, limit.is_limit_lift,
    limit.cone_π, cones.forget_map, is_limit.lift_cone_morphism_hom, iso.trans_hom, category.assoc,
     functor.map_cone_π],
  erw [←category_theory.functor.map_comp, limit.lift_π, is_limit.fac],
  refl,
end)

/--
The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂_AddCommGroup_preserves_limits :
  preserves_limits (forget₂ Ring AddCommGroup) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit.is_limit F) (is_limit_forget₂_AddCommGroup_map_cone_limit_cone F) } }

/--
The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget Ring) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ Ring SemiRing) (forget SemiRing) } }

end Ring


namespace CommRing

variables {J : Type u} [small_category J]

instance comm_ring_obj (F : J ⥤ CommRing) (j) :
  comm_ring ((F ⋙ forget CommRing).obj j) :=
by { change comm_ring (F.obj j), apply_instance }

instance limit_comm_ring (F : J ⥤ CommRing) :
  comm_ring (limit (F ⋙ forget CommRing)) :=
begin
  haveI : comm_ring ((F ⋙ forget CommRing).sections) :=
    @subtype.comm_ring ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
      (by convert (Ring.sections_subring (F ⋙ forget₂ CommRing Ring))),
  transport using (types.limit_equiv_sections (F ⋙ forget CommRing)).symm,
end

def lifted_cone (F : J ⥤ CommRing) : cone F :=
{ X := CommRing.of (limit (F ⋙ forget CommRing)),
  π :=
  { app := λ j, SemiRing.limit_π_ring_hom (F ⋙ forget₂ CommRing Ring ⋙ forget₂ Ring SemiRing) j,
    naturality' := (SemiRing.has_limits.limit_cone (F ⋙ forget₂ _ Ring ⋙ forget₂ _ SemiRing)).π.naturality, } }

def is_limit_forget₂_map_cone_lifted_cone (F : J ⥤ CommRing) :
  is_limit ((forget₂ CommRing Ring).map_cone (lifted_cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext (Ring.limit_iso_Ring_of_limit_forget _) $
  λ j, by erw is_limit.fac

/--
We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `comm_ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRing) : creates_limit F (forget₂ CommRing Ring) :=
creates_limit_of_reflects_iso (λ c' t,
{ lifted_cone := lifted_cone F,
  valid_lift := is_limit.unique_up_to_iso (is_limit_forget₂_map_cone_lifted_cone F) t,
  makes_limit := is_limit.of_faithful (forget₂ CommRing Ring) (is_limit_forget₂_map_cone_lifted_cone F)
    (λ s, _) (λ s, rfl) })

/-- The category of commutative rings has all limits. -/
instance has_limits : has_limits CommRing :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit_of_created F (forget₂ CommRing Ring) } }

def limit_iso_CommRing_of_limit_forget (F : J ⥤ CommRing) :
  limit F ≅ CommRing.of (limit (F ⋙ forget CommRing)) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit F)
  (lifted_limit_is_limit (limit.is_limit (F ⋙ forget₂ CommRing Ring ⋙ forget₂ Ring SemiRing)))

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
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, limits.comp_preserves_limit (forget₂ CommRing Ring) (forget Ring) } }

end CommRing
