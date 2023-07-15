/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.fgModule.basic
import algebra.category.Module.limits
import algebra.category.Module.products
import algebra.category.Module.epi_mono
import category_theory.limits.creates
import category_theory.limits.shapes.finite_limits
import category_theory.limits.constructions.limits_of_products_and_equalizers

/-!
# `forget₂ (fgModule K) (Module K)` creates all finite limits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

And hence `fgModule K` has all finite limits.

## Future work
After generalising `fgModule` to allow the ring and the module to live in different universes,
generalize this construction so we can take limits over smaller diagrams,
as is done for the other algebraic categories.

Analogous constructions for Noetherian modules.
-/

noncomputable theory
universes v u

open category_theory
open category_theory.limits

namespace fgModule

variables {J : Type} [small_category J] [fin_category J]
variables {k : Type v} [field k]

instance {J : Type} [fintype J] (Z : J → Module.{v} k) [∀ j, finite_dimensional k (Z j)] :
  finite_dimensional k (∏ λ j, Z j : Module.{v} k) :=
begin
  haveI : finite_dimensional k (Module.of k (Π j, Z j)), { dsimp, apply_instance, },
  exact finite_dimensional.of_injective
    (Module.pi_iso_pi _).hom
    ((Module.mono_iff_injective _).1 (by apply_instance)),
end

/-- Finite limits of finite dimensional vectors spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ fgModule k) :
  finite_dimensional k (limit (F ⋙ forget₂ (fgModule k) (Module.{v} k)) : Module.{v} k) :=
begin
  haveI : ∀ j, finite_dimensional k ((F ⋙ forget₂ (fgModule k) (Module.{v} k)).obj j),
  { intro j, change finite_dimensional k (F.obj j).obj, apply_instance, },
  exact finite_dimensional.of_injective
    (limit_subobject_product (F ⋙ forget₂ (fgModule k) (Module.{v} k)))
    ((Module.mono_iff_injective _).1 (by apply_instance)),
end

/-- The forgetful functor from `fgModule k` to `Module k` creates all finite limits. -/
def forget₂_creates_limit (F : J ⥤ fgModule k) :
  creates_limit F (forget₂ (fgModule k) (Module.{v} k)) :=
creates_limit_of_fully_faithful_of_iso
  ⟨(limit (F ⋙ forget₂ (fgModule k) (Module.{v} k)) : Module.{v} k), by apply_instance⟩
  (iso.refl _)

instance : creates_limits_of_shape J (forget₂ (fgModule k) (Module.{v} k)) :=
{ creates_limit := λ F, forget₂_creates_limit F, }

instance : has_finite_limits (fgModule k) :=
{ out := λ J _ _, by exactI
  has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape
    (forget₂ (fgModule k) (Module.{v} k)), }

instance : preserves_finite_limits (forget₂ (fgModule k) (Module.{v} k)) :=
{ preserves_finite_limits := λ J _ _, by exactI infer_instance, }

end fgModule
