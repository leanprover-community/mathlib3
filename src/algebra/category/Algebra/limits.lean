/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Algebra.basic
import algebra.category.Module.limits
import algebra.category.Ring.limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

open category_theory
open category_theory.limits

universes v w u -- `u` is determined by the ring, so can come last

noncomputable theory

namespace Algebra

variables {R : Type u} [comm_ring R]
variables {J : Type v} [small_category J]

instance semiring_obj (F : J ⥤ Algebra.{max v w} R) (j) :
  semiring ((F ⋙ forget (Algebra R)).obj j) :=
by { change semiring (F.obj j), apply_instance }

instance algebra_obj (F : J ⥤ Algebra.{max v w} R) (j) :
  algebra R ((F ⋙ forget (Algebra R)).obj j) :=
by { change algebra R (F.obj j), apply_instance }

/--
The flat sections of a functor into `Algebra R` form a submodule of all sections.
-/
def sections_subalgebra (F : J ⥤ Algebra.{max v w} R) :
  subalgebra R (Π j, F.obj j) :=
{ algebra_map_mem' := λ r j j' f, (F.map f).commutes r,
  ..SemiRing.sections_subsemiring
    (F ⋙ forget₂ (Algebra R) Ring.{max v w} ⋙ forget₂ Ring SemiRing.{max v w}) }


instance limit_semiring (F : J ⥤ Algebra.{max v w} R) :
  ring (types.limit_cone (F ⋙ forget (Algebra.{max v w} R))).X :=
begin
  change ring (sections_subalgebra F),
  apply_instance,
end

instance limit_algebra (F : J ⥤ Algebra.{max v w} R) :
  algebra R (types.limit_cone (F ⋙ forget (Algebra.{max v w} R))).X :=
begin
  have : algebra R (types.limit_cone (F ⋙ forget (Algebra.{max v w} R))).X
    = algebra R (sections_subalgebra F), by refl,
  rw this,
  apply_instance,
end

/-- `limit.π (F ⋙ forget (Algebra R)) j` as a `alg_hom`. -/
def limit_π_alg_hom (F : J ⥤ Algebra.{max v w} R) (j) :
  (types.limit_cone (F ⋙ forget (Algebra R))).X →ₐ[R] (F ⋙ forget (Algebra.{max v w} R)).obj j :=
{ commutes' := λ r, rfl,
  ..SemiRing.limit_π_ring_hom
    (F ⋙ forget₂ (Algebra R) Ring.{max v w} ⋙ forget₂ Ring SemiRing.{max v w}) j }

namespace has_limits
-- The next two definitions are used in the construction of `has_limits (Algebra R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Algebra R`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ Algebra.{max v w} R) : cone F :=
{ X := Algebra.of R (types.limit_cone (F ⋙ forget _)).X,
  π :=
  { app := limit_π_alg_hom F,
    naturality' := λ j j' f,
      alg_hom.coe_fn_injective ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ Algebra.{max v w} R) : is_limit (limit_cone F) :=
begin
  refine is_limit.of_faithful
    (forget (Algebra R)) (types.limit_cone_is_limit _)
    (λ s, { .. }) (λ s, rfl),
  { simp only [forget_map_eq_coe, alg_hom.map_one, functor.map_cone_π_app], refl, },
  { intros x y, simp only [forget_map_eq_coe, alg_hom.map_mul, functor.map_cone_π_app], refl, },
  { simp only [forget_map_eq_coe, alg_hom.map_zero, functor.map_cone_π_app], refl, },
  { intros x y, simp only [forget_map_eq_coe, alg_hom.map_add, functor.map_cone_π_app], refl, },
  { intros r, ext j, exact (s.π.app j).commutes r, },
end

end has_limits

open has_limits

/-- The category of R-algebras has all limits. -/
@[irreducible]
instance has_limits_of_size : has_limits_of_size.{v v} (Algebra.{max v w} R) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

instance has_limits : has_limits (Algebra.{w} R) := Algebra.has_limits_of_size.{w w u}

/--
The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂_Ring_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget₂ (Algebra R) Ring.{max v w}) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F)
      (by apply Ring.limit_cone_is_limit (F ⋙ forget₂ (Algebra R) Ring.{max v w})) } }

instance forget₂_Ring_preserves_limits :
  preserves_limits (forget₂ (Algebra R) Ring.{w}) :=
Algebra.forget₂_Ring_preserves_limits_of_size.{w w}

/--
The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂_Module_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget₂ (Algebra R) (Module.{max v w} R)) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F)
      (by apply Module.has_limits.limit_cone_is_limit
        (F ⋙ forget₂ (Algebra R) (Module.{max v w} R))) } }

instance forget₂_Module_preserves_limits : preserves_limits (forget₂ (Algebra R) (Module.{w} R)) :=
Algebra.forget₂_Module_preserves_limits_of_size.{w w}

/--
The forgetful functor from R-algebras to types preserves all limits.
-/
instance forget_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget (Algebra.{max v w} R)) :=
{ preserves_limits_of_shape := λ J 𝒥, by exactI
  { preserves_limit := λ F, preserves_limit_of_preserves_limit_cone
    (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) } }

instance forget_preserves_limits : preserves_limits (forget (Algebra.{w} R)) :=
Algebra.forget_preserves_limits_of_size.{w w}

end Algebra
