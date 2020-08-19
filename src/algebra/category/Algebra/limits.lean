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
{ commutes' := λ r, begin simp, erw types.limit_equiv_sections_symm_apply, refl, end,
  ..SemiRing.limit_π_ring_hom (F ⋙ forget₂ (Algebra R) Ring ⋙ forget₂ Ring SemiRing) j }

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

/--
Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ Algebra R) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget (Algebra R)) (limit.is_limit _)
    (λ s, { .. }) (λ s, rfl),
  { simp only [forget_map_eq_coe, alg_hom.map_one, functor.map_cone_π], refl, },
  { intros x y, simp only [forget_map_eq_coe, alg_hom.map_mul, functor.map_cone_π], refl, },
  { simp only [forget_map_eq_coe, alg_hom.map_zero, functor.map_cone_π], refl, },
  { intros x y, simp only [forget_map_eq_coe, alg_hom.map_add, functor.map_cone_π], refl, },
  { intros r, ext j, dsimp, erw (s.π.app j).commutes r, refl, },
end

end has_limits

open has_limits

/-- The category of R-algebras has all limits. -/
instance has_limits : has_limits (Algebra R) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

def limit_iso_Algebra_of_limit_forget (F : J ⥤ Algebra R) :
  limit F ≅ Algebra.of R (limit (F ⋙ forget (Algebra R))) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit F)
  (limit_cone_is_limit F)

/--
The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂_Ring_preserves_limits : preserves_limits (forget₂ (Algebra R) Ring) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget₂ (Algebra R) Ring)) } }

/--
The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂_Module_preserves_limits : preserves_limits (forget₂ (Algebra R) (Module R)) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget₂ (Algebra R) (Module R))) } }

/--
The forgetful functor from R-algebras to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget (Algebra R)) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end Algebra
