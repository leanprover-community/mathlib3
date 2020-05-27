/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels

open category_theory.limits

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C]
variables [has_zero_morphisms.{v} C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
class simple (X : C) :=
(mono_is_iso_equiv_nonzero : ∀ {Y : C} (f : Y ⟶ X) [mono f], is_iso.{v} f ≃ (f ≠ 0))

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
def is_iso_of_mono_of_nonzero {X Y : C} [simple.{v} X] {f : Y ⟶ X} [mono f] (w : f ≠ 0) :
  is_iso f :=
(simple.mono_is_iso_equiv_nonzero f).symm w

lemma kernel_zero_of_nonzero_from_simple
  {X Y : C} [simple.{v} X] {f : X ⟶ Y} [has_limit (parallel_pair f 0)] (w : f ≠ 0) :
  kernel.ι f = 0 :=
begin
  classical,
  by_contradiction h,
  haveI := is_iso_of_mono_of_nonzero h,
  exact w (eq_zero_of_kernel_is_iso f),
end

section
variable [has_zero_object.{v} C]
local attribute [instance] has_zero_object.has_zero

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
lemma zero_not_simple [simple.{v} (0 : C)] : false :=
(simple.mono_is_iso_equiv_nonzero (0 : (0 : C) ⟶ (0 : C))) { inv := 0, } rfl

end

end category_theory
