/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.simple
import category_theory.preadditive

/-!
# Schur's lemma
We prove the part of Schur's Lemma that holds in any preadditive category with kernels,
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
variables [preadditive C] [has_kernels C]

/--
Schur's Lemma (for a general preadditive category),
that a nonzero morphism between simple objects is an isomorphism.
-/
def is_iso_of_hom_simple {X Y : C} [simple X] [simple Y] {f : X ⟶ Y} (w : f ≠ 0) :
  is_iso f :=
begin
  haveI : mono f := preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w),
  exact is_iso_of_mono_of_nonzero w
end

/--
As a corollary of Schur's lemma,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
def is_iso_equiv_nonzero {X Y : C} [simple.{v} X] [simple.{v} Y] {f : X ⟶ Y} :
  is_iso.{v} f ≃ (f ≠ 0) :=
{ to_fun := λ I,
  begin
    introI h,
    apply id_nonzero X,
    simp only [←is_iso.hom_inv_id f, h, has_zero_morphisms.zero_comp],
  end,
  inv_fun := λ w, is_iso_of_hom_simple w,
  left_inv := λ I, subsingleton.elim _ _,
  right_inv := λ w, rfl }

end category_theory
