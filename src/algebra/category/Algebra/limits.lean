/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Algebra.basic
import algebra.category.Module.limits
import algebra.category.CommRing.limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace Algebra

variables {R : Type u} [comm_ring R]
variables {J : Type u} [small_category J]

instance semiring_obj (F : J ⥤ Algebra R) (j) :
  semiring ((F ⋙ forget (Algebra R)).obj j) :=
by { change semiring (F.obj j), apply_instance }

instance algebra_obj (F : J ⥤ Algebra R) (j) :
  algebra R ((F ⋙ forget (Algebra R)).obj j) :=
by { change algebra R (F.obj j), apply_instance }

/--
The flat sections of a functor into `Algebra R` form a submodule of all sections.
-/
def sections_subalgebra (F : J ⥤ Algebra R) :
  subalgebra R (Π j, F.obj j) :=
{ carrier := SemiRing.sections_subsemiring (F ⋙ forget₂ (Algebra R) Ring ⋙ forget₂ Ring SemiRing),
  algebra_map_mem' := λ r j j' f, (F.map f).commutes r, }

instance sections_ring (F : J ⥤ Algebra R) : ring ((F ⋙ forget (Algebra R)).sections) :=
(by apply_instance : ring (sections_subalgebra F))

instance sections_algebra (F : J ⥤ Algebra R) : algebra R ((F ⋙ forget (Algebra R)).sections) :=
(by apply_instance : algebra R (sections_subalgebra F))

instance limit_ring (F : J ⥤ Algebra R) :
  ring (limit (F ⋙ forget (Algebra R))) :=
equiv.ring (types.limit_equiv_sections (F ⋙ forget (Algebra R)))

def limit_ring_equiv (F : J ⥤ Algebra R) :
  limit (F ⋙ forget (Algebra R)) ≃+* ((F ⋙ forget (Algebra R)).sections) :=
equiv.ring_equiv (types.limit_equiv_sections (F ⋙ forget (Algebra R)))

instance limit_algebra (F : J ⥤ Algebra R) :
  algebra R (limit (F ⋙ forget (Algebra R))) :=
equiv.algebra R (types.limit_equiv_sections (F ⋙ forget (Algebra R)))

def limit_alg_equiv (F : J ⥤ Algebra R) :
  limit (F ⋙ forget (Algebra R)) ≃ₐ[R] ((F ⋙ forget (Algebra R)).sections) :=
equiv.alg_equiv R (types.limit_equiv_sections (F ⋙ forget (Algebra R)))

/-- `limit.π (F ⋙ forget (Algebra R)) j` as a `alg_hom`. -/
def limit_π_alg_hom (F : J ⥤ Algebra R) (j) :
  limit (F ⋙ forget (Algebra R)) →ₐ[R] (F ⋙ forget (Algebra R)).obj j :=
{ commutes' := λ r,
  begin
    simp only [SemiRing.limit_π_ring_hom],
    erw types.limit_equiv_sections_symm_apply,
    refl,
  end,
  ..SemiRing.limit_π_ring_hom (F ⋙ forget₂ (Algebra R) Ring ⋙ forget₂ Ring SemiRing) j }

lemma limit_π_alg_hom_apply (F : J ⥤ Algebra R) (j) (x) :
  (limit_π_alg_hom F j) x = limit.π (F ⋙ forget (Algebra R)) j x := rfl

namespace has_limits
-- The next two definitions are used in the construction of `has_limits (Algebra R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Algebra R`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ Algebra R) : cone F :=
{ X := Algebra.of R (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_alg_hom F,
    naturality' := λ j j' f,
      alg_hom.coe_fn_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

@[simps]
def forget_map_cone_limit_cone_iso (F : J ⥤ Algebra R) :
  (forget (Algebra R)).map_cone (limit_cone F) ≅ limit.cone (F ⋙ forget (Algebra R)) :=
{ hom := { hom := 𝟙 _, },
  inv := { hom := 𝟙 _, } }

def is_limit_forget_map_cone_limit_cone (F : J ⥤ Algebra R) :
  is_limit ((forget (Algebra R)).map_cone (limit_cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) (forget_map_cone_limit_cone_iso F).symm

/--
Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ Algebra R) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget (Algebra R)) (is_limit_forget_map_cone_limit_cone F)
    (λ s, { .. }) (λ s, rfl),
  { intros, ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, function.comp_app, alg_hom.map_one, is_limit.lift_cone_morphism_hom,
      types.lift_π_apply, types_id_apply, functor.map_cone_π],
    rw ←limit_π_alg_hom_apply,
    simp [limit_π_alg_hom], },
  { intros, ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom, types.lift_π_apply,
      types_id_apply, alg_hom.map_mul, functor.map_cone_π],
    rw ←limit_π_alg_hom_apply,
    simp only [limit_π_alg_hom, SemiRing.limit_π_ring_hom, alg_hom.coe_mk, alg_hom.map_mul],
    erw [types.lift_π_apply, types.lift_π_apply],
    refl, },
  { intros, ext,
    simp only [forget_map_eq_coe, forget_map_cone_limit_cone_iso_inv_hom, iso.symm_hom,
      limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom, types.lift_π_apply,
      alg_hom.map_zero, types_id_apply, functor.map_cone_π],
    rw ←limit_π_alg_hom_apply,
    simp [limit_π_alg_hom], },
  { intros, ext,
    simp only [forget_map_eq_coe, alg_hom.map_add, forget_map_cone_limit_cone_iso_inv_hom,
      iso.symm_hom, limit.is_limit_lift, function.comp_app, is_limit.lift_cone_morphism_hom,
      types.lift_π_apply, types_id_apply, functor.map_cone_π],
    rw ←limit_π_alg_hom_apply,
    simp only [limit_π_alg_hom, SemiRing.limit_π_ring_hom, alg_hom.coe_mk, alg_hom.map_add],
    erw [types.lift_π_apply, types.lift_π_apply],
    refl, },
   { intros r, ext j, dsimp,
     simp only [forget_map_eq_coe, types.lift_π_apply, functor.map_cone_π],
     erw [(s.π.app j).commutes r, ←limit_π_alg_hom_apply, alg_hom.commutes],
     refl, },
end

end has_limits

open has_limits

/-- The category of R-algebras has all limits. -/
instance has_limits : has_limits (Algebra R) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F,
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

def limit_iso_Algebra_of_limit_forget (F : J ⥤ Algebra R) :
  limit F ≅ Algebra.of R (limit (F ⋙ forget (Algebra R))) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit F)
  (limit_cone_is_limit F)

def forget₂_Ring_limit_iso_Ring_of_limit_forget (F : J ⥤ Algebra R) :
  (forget₂ (Algebra R) Ring).obj (limit F) ≅ Ring.of (limit (F ⋙ forget (Algebra R))) :=
(forget₂ (Algebra R) Ring).map_iso (limit_iso_Algebra_of_limit_forget F)

def is_limit_forget₂_Ring_map_cone_limit_cone (F : J ⥤ Algebra R) :
  is_limit ((forget₂ (Algebra R) Ring).map_cone (limit.cone F)) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext
(Ring.limit_iso_Ring_of_limit_forget _ ≪≫
  (forget₂_Ring_limit_iso_Ring_of_limit_forget _).symm)
(λ j,
begin
  simp only [forget₂_Ring_limit_iso_Ring_of_limit_forget,
    limit_iso_Algebra_of_limit_forget, is_limit.cone_point_unique_up_to_iso,
    functor.map_iso_inv, is_limit.unique_up_to_iso_inv, iso.symm_hom, limit.is_limit_lift,
    limit.cone_π, cones.forget_map, is_limit.lift_cone_morphism_hom, iso.trans_hom, category.assoc,
     functor.map_cone_π],
  erw [←category_theory.functor.map_comp, limit.lift_π, is_limit.fac],
  refl,
end)

/--
The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂_Ring_preserves_limits : preserves_limits (forget₂ (Algebra R) Ring) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (is_limit_forget₂_Ring_map_cone_limit_cone F) } }

/--
The forgetful functor from R-algebras to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget (Algebra R)) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (is_limit_forget_map_cone_limit_cone F) } }

end Algebra
