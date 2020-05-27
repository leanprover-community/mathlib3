/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.simple
import category_theory.abelian.basic

/-!
# Simple objects
We prove the version of Schur's Lemma that is true in any abelian category,
that any nonzero morphism between simple objects
is an isomorphism.

## TODO
If the category is enriched over finite dimensional vector spaces
over an algebraically closed field, then we can further prove that
`dim (X ⟶ Y) ≤ 1`.

(Probably easiest to prove this for endomorphisms first:
some polynomial `p` in `f : X ⟶ X` vanishes by finite dimensionality,
that polynomial factors linearly,
and at least one factor must be non-invertible, hence zero,
so `f` is a scalar multiple of the identity.
Then for any two nonzero `f g : X ⟶ Y`,
observe `f ≫ g⁻¹` is a multiple of the identity.)
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
