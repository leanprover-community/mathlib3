/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.simple
import category_theory.abelian.basic

/-!
We prove Schur's Lemma,
that any nonzero morphism between simple objects in an abelian category
is an isomorphism.
-/

namespace category_theory

open category_theory.limits

universes v u
variables {C : Type u} [category.{v} C]
variables [abelian.{v} C]

local attribute [instance, priority 100] preadditive.has_limit_parallel_pair

/--
Schur's Lemma (for a general abelian category),
that a nonzero morphism between simple objects is an isomorphism.
-/
def schur {X Y : C} [simple.{v} X] [simple.{v} Y] {f : X ⟶ Y} (w : f ≠ 0) :
  is_iso f :=
begin
  classical,
  have : mono f := preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w),
  have : epi f,
  { have := is_iso_of_mono_of_nonzero (nonzero_image_of_nonzero w),
    exact epi_of_image_is_iso f },
  apply abelian.is_iso_of_mono_of_epi,
end

end category_theory
