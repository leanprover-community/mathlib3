/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.FinVect
import algebra.category.Module.limits
import algebra.category.Module.products
import algebra.category.Module.epi_mono
import category_theory.limits.creates
import category_theory.limits.shapes.finite_limits
import category_theory.limits.constructions.limits_of_products_and_equalizers

/-!
# `forget₂ (FinVect K) (Module K)` creates all finite limits.

And hence `FinVect K` has all finite limits.

## Future work
After generalising `FinVect` to allow the ring and the module to live in different universes,
generalize this construction so we can take limits over smaller diagrams,
as is done for the other algebraic categories.
-/

noncomputable theory
universes v u

open category_theory
open category_theory.limits

namespace FinVect

variables {J : Type v} [small_category J] [fin_category J]
variables {k : Type v} [field k]

instance {J : Type v} [fintype J] (Z : J → Module.{v} k) [∀ j, finite_dimensional k (Z j)] :
  finite_dimensional k (∏ λ j, Z j : Module.{v} k) :=
begin
  haveI : finite_dimensional k (Module.of k (Π j, Z j)), { dsimp, apply_instance, },
  exact finite_dimensional.of_injective
    (Module.pi_iso_pi.{v v v} _).hom
    ((Module.mono_iff_injective _).1 (by apply_instance)),
end

/-- Finite limits of finite finite dimensional vectors spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FinVect k) :
  finite_dimensional k (limit (F ⋙ forget₂ (FinVect k) (Module.{v} k)) : Module.{v} k) :=
begin
  haveI : ∀ j, finite_dimensional k ((F ⋙ forget₂ (FinVect k) (Module.{v} k)).obj j),
  { intro j, change finite_dimensional k (F.obj j), apply_instance, },
  exact finite_dimensional.of_injective
    (limit_subobject_product (F ⋙ forget₂ (FinVect k) (Module.{v} k)))
    ((Module.mono_iff_injective _).1 (by apply_instance)),
end

/-- The forgetful functor from `FinVect k` to `Module k` creates all finite limits. -/
def forget₂_creates_limit (F : J ⥤ FinVect k) :
  creates_limit F (forget₂ (FinVect k) (Module.{v} k)) :=
creates_limit_of_fully_faithful_of_iso
  ⟨(limit (F ⋙ forget₂ (FinVect k) (Module.{v} k)) : Module.{v} k), by apply_instance⟩
  (iso.refl _)

instance : creates_limits_of_shape J (forget₂ (FinVect k) (Module.{v} k)) :=
{ creates_limit := λ F, forget₂_creates_limit F, }

instance : has_finite_limits (FinVect k) :=
{ out := λ J _ _, by exactI
  has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape
    (forget₂ (FinVect k) (Module.{v} k)), }

instance : preserves_finite_limits (forget₂ (FinVect k) (Module.{v} k)) :=
{ preserves_finite_limits := λ J _ _, by exactI infer_instance, }

end FinVect
