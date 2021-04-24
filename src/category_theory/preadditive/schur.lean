/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.simple
import category_theory.linear
import category_theory.endomorphism
import field_theory.algebraic_closure

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
lemma is_iso_of_hom_simple {X Y : C} [simple X] [simple Y] {f : X ⟶ Y} (w : f ≠ 0) :
  is_iso f :=
begin
  haveI : mono f := preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w),
  exact is_iso_of_mono_of_nonzero w
end

/--
As a corollary of Schur's lemma,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
lemma is_iso_iff_nonzero {X Y : C} [simple.{v} X] [simple.{v} Y] (f : X ⟶ Y) :
  is_iso.{v} f ↔ f ≠ 0 :=
⟨λ I,
  begin
    introI h,
    apply id_nonzero X,
    simp only [←is_iso.hom_inv_id f, h, zero_comp],
  end,
  λ w, is_iso_of_hom_simple w⟩

-- TODO move to `category_theory.endomorphism`
lemma is_iso_iff_is_unit {X : C} (f : End X) : is_iso f ↔ is_unit (f : End X) :=
sorry

instance (X : C) [simple.{v} X] : nontrivial (End X) :=
nontrivial_of_ne 1 0 (id_nonzero X)

open finite_dimensional

variables {𝕜 : Type*} [field 𝕜] [is_alg_closed 𝕜]

-- TODO try out Sebastien's workaround
local attribute [ext] add_comm_group semimodule distrib_mul_action mul_action has_scalar

lemma findim_endomorphism_eq_one
  [linear 𝕜 C] {X : C} (is_iso_iff_nonzero : ∀ f : X ⟶ X, is_iso f ↔ f ≠ 0)
  [I : finite_dimensional 𝕜 (X ⟶ X)] :
  findim 𝕜 (X ⟶ X) = 1 :=
begin
  have id_nonzero := (is_iso_iff_nonzero (𝟙 X)).mp (by apply_instance),
  apply findim_eq_one (𝟙 X),
  exact id_nonzero,
  intro f,
  haveI : nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero,
  obtain ⟨c, nu⟩ := @exists_spectrum_of_is_alg_closed_of_finite_dimensional 𝕜 _ _ (End X) _ _ _
    (by { convert I, ext; refl, ext; refl, }) (End.of f),
  use c,
  rw [←is_iso_iff_is_unit, is_iso_iff_nonzero, ne.def, not_not, sub_eq_zero,
    algebra.algebra_map_eq_smul_one] at nu,
  exact nu.symm,
end

/--
Schur's lemma for `𝕜`-linear categories
-/
lemma findim_endomorphism_simple_eq_one
  [linear 𝕜 C] {X : C} [simple.{v} X] [I : finite_dimensional 𝕜 (X ⟶ X)] :
  findim 𝕜 (X ⟶ X) = 1 :=
findim_endomorphism_eq_one is_iso_iff_nonzero

lemma findim_hom_simple_simple_le_one
  [linear 𝕜 C] {X Y : C} [finite_dimensional 𝕜 (X ⟶ X)] [simple.{v} X] [simple.{v} Y] :
  findim 𝕜 (X ⟶ Y) ≤ 1 :=
sorry

end category_theory
